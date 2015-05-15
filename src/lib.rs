/// My take on an entity component system.
///
/// Assumption: Entities are created and destroyed frequently.
///
/// Assumption: Entity IDs can be recycled.
///
/// Assumption: Components are never destroyed, and created very infrequently.
///
/// Assumption: Component data need never exceed 64k.
///
/// Assumption: Entity types are never destroyed, and created very infrequently.
///
/// Assumption: Most systems only care about a few components.
///
/// Assumption: Component data fits in addressable memory.
///
/// Assumption: Almost all entities fit into a few pre-determined "buckets" of
/// shared components layout ("entity types").
///
/// Assumption: The game can have billions of entities over the course of its
/// lifetime, but only a few million active at any one point.
///
/// Assumption: Saving all entity + component state to a file is necessary.
///
/// Assumption: System parallelism is desirable.
///
/// Assumption: Systems don't communicate to any significant extent during
/// processing.
///
/// Assumption: Most systems write to only a few components, and system processing
/// order is commutative.

use std::collections::{HashMap};

/// The `Entity` encodes entity type and id, which is used as an index into the component storage.
///
/// The type of this entity is packed in the first 8 bits, leaving the other 56 for the id.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Clone, Copy)]
pub struct Entity(u64);
impl std::ops::Deref for Entity { type Target = u64; fn deref(&self) -> &u64 { &self.0 } }

/// The `EntityType` records which of 256 possible entity types an entity is.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Clone, Copy)]
pub struct EntityType(u8);
impl std::ops::Deref for EntityType { type Target = u8; fn deref(&self) -> &u8 { &self.0 } }

/// The `Component` is a handle to a chunk of data associated with an entity.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Clone, Copy)]
pub struct Component(u16);
impl std::ops::Deref for Component { type Target = u16; fn deref(&self) -> &u16 { &self.0 } }

type Bytes = Vec<u8>;

impl Entity {
    fn new(id: u64, ty: EntityType) -> Entity {
        Entity(id | (ty.0 as u64) << 56)
    }

    fn id(&self) -> u8 {
        (self.0 >> 56) as u8
    }

    fn without_type(&self) -> u64 {
        self.0 & (1<<56)-1
    }
}

struct IdAllocator {
    free_list: Vec<u64>,
    max_made: u64,
}

impl IdAllocator {
    fn new() -> IdAllocator { IdAllocator { free_list: Vec::with_capacity(64), max_made: 0 } }
    fn next(&mut self) -> (u64, bool) {
        match self.free_list.pop() {
            Some(id) => (id, false),
            None => {
                let val = self.max_made;
                self.max_made += 1;
                (val, true)
            }
        }
    }

    fn free(&mut self, id: u64) {
        self.free_list.push(id);
    }

    #[allow(dead_code)]
    fn compact(&mut self) {
        // todo: make intervals of the ranges of ids in the free_list, see if max_made can be
        // decremented to make the free list smaller.
    }
}

// Implementation note: Why not use VecMap? These aren't purely maps since they have
// the indirection of the component index. Additionally, using VecMap adds the overhead of wrapping
// everything in an Option, when we can always have a valid entry.
//
// Note: reevaluate to see if the uses here allow for the enum compression optimization.

// NOTE: Please be careful when indexing entity_type_*, as you must never index them when the
// EntityType is 0 (the "empty type"), and you must subtract 1 from a "real" EntityType to index.

/// Raw entity/component manager.
///
/// Considers components as chunks of bytes, with no particular concern for interpretation or
/// safety. This is quite easy to use incorrectly, so its use is not advised.
pub struct ComponentStorage {
    /// Used to lookup entity type size.
    entity_type_sizes: Vec<u16>,
    /// Maps from EntityType -> Component data array.
    entity_type_data: Vec<Bytes>,
    /// Maps from Component -> Component data array
    component_data: Vec<Bytes>,
    /// Maps from Component -> Entity location index, which maps Entity -> index in component data array
    // note: investigate other data structures.
    component_index: Vec<HashMap<Entity, usize>>,
    /// Maps from EntityType -> Component set
    entity_type_components: Vec<Vec<(usize, Component)>>,
    /// Maps from Component -> number of bytes the component takes up.
    component_sizes: Vec<u16>,
    /// Maps from Entity Type -> entity id allocator
    entity_id_cache: Vec<IdAllocator>,
    /// Maps from Component -> component index allocator
    component_index_cache: Vec<IdAllocator>,
}

impl ComponentStorage {
    /// Create an empty ComponentStorage with space pre-allocated for 4 entity types and 16
    /// components.
    pub fn new() -> ComponentStorage {
        ComponentStorage {
            entity_type_sizes: Vec::with_capacity(4),
            entity_type_data: Vec::with_capacity(4),
            component_data: Vec::with_capacity(16),
            component_index: Vec::with_capacity(16),
            entity_type_components: Vec::with_capacity(4),
            component_sizes: Vec::with_capacity(16),
            entity_id_cache: Vec::with_capacity(4),
            component_index_cache: Vec::with_capacity(16),
        }
    }

    /// Create an entity type where each entity of that type has storage for all of `comps`
    /// automatically allocated.
    #[inline]
    pub fn create_entity_type(&mut self, comps: Vec<Component>) -> EntityType {
        assert!(self.entity_type_sizes.len() < 255);
        if cfg!(debug_assertions) {
            if self.entity_type_sizes.len() == 254 {
                println!("WARN: Entity type limit reached!")
            }
        }

        let size = comps.iter().map(|c| self.component_sizes[c.0 as usize] as u64).fold(0u64, |acc, it| acc + it);
        assert!(size < u16::max_value() as u64);

        self.entity_id_cache.push(IdAllocator::new());
        self.entity_type_sizes.push(size as u16);
        self.entity_type_data.push(Vec::with_capacity(size as usize * 128));

        let mut comps = comps.into_iter().enumerate().collect::<Vec<_>>();
        comps.sort_by(|a, b| a.1.cmp(&b.1));
        self.entity_type_components.push(comps);

        EntityType(self.entity_type_sizes.len() as u8)
    }

    /// Create a component that uses `size` bytes per entity.
    #[inline]
    pub fn create_component(&mut self, size: u16) -> Component {
        let new_id = self.component_sizes.len();
        assert!(new_id < u16::max_value() as usize);
        self.component_sizes.push(size);
        self.component_index.push(HashMap::new());
        self.component_data.push(Vec::with_capacity(size as usize * 128));
        self.component_index_cache.push(IdAllocator::new());
        Component(new_id as u16)
    }

    /// Create an entity, reserving space it is due by its EntityType.
    #[inline]
    pub fn create_entity(&mut self, ty: EntityType) -> Entity {
        let (id, new) = self.entity_id_cache[ty.0 as usize].next();
        if ty.0 != 0 {
            if new {
                self.entity_type_data[ty.0 as usize - 1].reserve(self.entity_type_sizes[ty.0 as usize - 1] as usize)
            }
        }
        Entity::new(id, ty)
    }

    /// Destroy an entity, freeing the storage its components are using for other entities.
    ///
    /// This is expensive for the same reason that components_for is expensive. Entity
    /// destruction should be batched and done after everything else.
    #[inline]
    pub fn destroy_entities(&mut self, ents: &[Entity]) {
        let &mut ComponentStorage {
            ref mut entity_id_cache,
            ref mut component_index,
            ref mut component_index_cache,
            ..
        } = self;

        for ent in ents {
            entity_id_cache[ent.id() as usize - 1].free(ent.without_type())
        }

        // ok, we've returned their ids. let's free the component data.
        for (comp_id, index) in component_index.iter_mut().enumerate() {
            // don't bother looking up to see if this component is part of the entity type data,
            // no use wasting cache on it, it just adds yet another hashmap lookup.
            //
            // it's ok to not look it up, because if the id is part of the entity type, then all
            // we're doing is returning an id that was never used to the pool. while this may be
            // inefficient, `compact` should take care of it later.
            for ent in ents {
                if let Some(id) = index.remove(ent) {
                    component_index_cache[comp_id as usize].free(id as u64);
                }
            }
        }
    }

    /// Lookup component location for a single entity.
    ///
    /// This query should be avoided, as it needs to lookup where the component is stored for this
    /// particular entity type, which can have undesirable effects on cache.
    #[inline]
    pub fn lookup_component(&self, ent: Entity, comp: Component) -> Option<*mut u8> {
        let id = ent.id();
        if id != 0 {
            match self.lookup_internal_component(ent, comp) {
                Some(ptr) => return Some(ptr),
                None => { } // keep looking
            }
        }
        self.lookup_external_component(ent, comp)
    }

    /// Lookup component index for a single entity, where comp is guaranteed to be part of the
    /// entity type for `ent`.
    #[inline]
    pub fn lookup_internal_component(&self, ent: Entity, comp: Component) -> Option<*mut u8> {
        let &ComponentStorage {
            ref entity_type_sizes,
            ref entity_type_data,
            ref entity_type_components,
            ..
        } = self;

        let id = ent.id();
        if id == 0 { return None; }
        let size = entity_type_sizes[id as usize - 1];
        let idx = entity_type_components[id as usize - 1].binary_search_by(|&(_, cand)| cand.cmp(&comp));
        match idx {
            Ok(i) => {
                let idx = entity_type_components[id as usize - 1][i].0 as isize;
                unsafe {
                    Some(entity_type_data[id as usize - 1].as_ptr().offset(size as isize * idx) as *mut u8)
                }
            },
            Err(_) => None
        }
    }

    /// Lookup component index for a single entity, where comp is guaranteed to not be part of the
    /// entity type for `ent`.
    #[inline]
    pub fn lookup_external_component(&self, ent: Entity, comp: Component) -> Option<*mut u8> {
        let idx = self.component_index[comp.0 as usize].get(&ent).map(|&v| v);
        match idx {
            Some(idx) => {
                let size = self.component_sizes[comp.0 as usize];
                unsafe {
                    Some(self.component_data[comp.0 as usize].as_ptr().offset(size as isize * idx as isize) as *mut u8)
                }
            },
            None => None
        }
    }

    /// Lookup entity type data for a single entity.
    #[inline]
    pub fn lookup_entity_type_data(&self, ent: Entity) -> Option<*mut u8> {
        let id = ent.id();
        if id == 0 { return None; }
        let size = self.entity_type_sizes[id as usize - 1];
        unsafe {
            Some(self.entity_type_data[id as usize - 1].as_ptr().offset(size as isize * ent.without_type() as isize) as *mut u8)
        }
    }

    /// Lookup all component data for an entity.
    ///
    /// This query is *extremely* expensive, and should be used very infrequently. It must walk all
    /// component indices looking for this entity, trashing the cache.
    #[inline]
    pub fn components_for(&self, ent: Entity) -> Vec<Component> {
        let mut comps = Vec::new();
        if ent.id() != 0 {
            comps.extend(self.entity_type_components[ent.id() as usize - 1].iter().map(|&c| c.1))
        }
        for (id, index) in self.component_index.iter().enumerate() {
            if index.contains_key(&ent) {
                comps.push(Component(id as u16))
            }
        }
        comps
    }

    /// Set component data for an entity.
    ///
    /// This query should be avoided, as it needs to lookup where the component is stored for this
    /// particular entity type, which can have undesirable effects on cache.
    #[inline]
    #[allow(unused_variables)]
    pub fn set_component(&mut self, ent: Entity, comp: Component, data: &[u8]) {
        unimplemented!()
    }

    /// Set component data for an entity, where comp is guaranteed to not be part of the entity
    /// type for `ent`.
    #[inline]
    pub fn set_external_component(&mut self, ent: Entity, comp: Component, data: &[u8]) {
        let size = self.component_sizes[comp.0 as usize];
        match self.lookup_external_component(ent, comp) {
            Some(dest) => {
                unsafe { std::ptr::copy_nonoverlapping(data.as_ptr(), dest, size as usize) }
            },
            None => {
                let (idx, new) = self.component_index_cache[comp.0 as usize].next();
                if new {
                    self.component_data[comp.0 as usize].reserve(size as usize);
                }
                unsafe {
                    let dest = self.component_data[comp.0 as usize].as_mut_ptr().offset(idx as isize * size as isize);
                    std::ptr::copy_nonoverlapping(data.as_ptr(), dest, size as usize);
                }
            }
        }
    }

    /// Set component data for an entity, where comp is guaranteed to be part of the entity type
    /// for `ent`.
    #[inline]
    pub fn set_internal_component(&mut self, ent: Entity, comp: Component, data: &[u8]) {
        let id = ent.id();
        if id == 0 { panic!("Tried to set internal component with no entity type!"); }
        let size = self.entity_type_sizes[id as usize - 1];
        assert!(data.len() >= size as usize);
        let dest = self.lookup_internal_component(ent, comp)
            .expect("Wanted to set internal component but entity type doesn't have that component");
        unsafe { std::ptr::copy_nonoverlapping(data.as_ptr(), dest, size as usize) }
    }

    /// Set all component data specific to the entity's type.
    #[inline]
    pub fn set_entity_type_data(&mut self, ent: Entity, data: &[u8]) {
        let id = ent.id();
        if id == 0 { panic!("Tried to set entity type data with no entity type!") }
        let size = self.entity_type_sizes[id as usize - 1];
        assert!(data.len() >= size as usize);
        unsafe {
            let dest = self.entity_type_data[id as usize - 1].as_ptr().offset(size as isize * ent.without_type() as isize);
            std::ptr::copy_nonoverlapping(data.as_ptr(), dest as *mut u8, size as usize);
        }
    }

    /// Query whether an entity has the given component.
    ///
    /// This is expensive for the same reason as components_for.
    #[inline]
    pub fn entity_has_component(&self, ent: Entity, comp: Component) -> bool {
        if ent.id() != 0 {
            if self.entity_type_components[ent.id() as usize - 1].binary_search_by(|&(_, cand)| cand.cmp(&comp)).is_ok() {
                return true;
            }
        }
        // todo : search real caches
        false
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn id_alloc_smoke() {
        let mut idl = ::IdAllocator::new();
        let ids = (0..10).map(|_| idl.next()).collect::<Vec<_>>();
        for (a, b) in ids.iter().zip(0..10) {
            assert_eq!(*a, (b, true))
        }

        idl.free(3);
        assert_eq!(idl.next(), (3, false));
    }
}
