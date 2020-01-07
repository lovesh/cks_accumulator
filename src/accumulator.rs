use amcl_wrapper::extension_field_gt::GT;
use amcl_wrapper::field_elem::{FieldElement, FieldElementVector};
use amcl_wrapper::group_elem::{GroupElement, GroupElementVector};
use amcl_wrapper::group_elem_g1::{G1Vector, G1};
use amcl_wrapper::group_elem_g2::{G2Vector, G2};
use std::collections::HashSet;
use std::collections::hash_set;

/// Tracks indices currently present in the accumulator. This data-structure does not need to be publicly
/// writable but is needed to prevent adding the same entry again or removing an entry that is not present
/// and when an old witness needs to be updated. Only the party in-charge of updating the accumulator
/// should have write access to this.
pub trait AccumulatorState {
    fn is_empty(&self) -> bool;
    fn capacity(&self) -> usize;
    fn has_index(&self, index: usize) -> bool;
    /// Return true if the state did not have this value
    fn add(&mut self, index: usize) -> bool;
    /// Return true if the state did have this value
    fn remove(&mut self, index: usize) -> bool;
    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a usize> + 'a>;
}

/// Accumulator state that keeps the added indices in a HashSet. For production use, a persistent
/// database should be used.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InMemoryAccumulatorState {
    max_size: usize,
    /// 1-indexed
    indices: HashSet<usize>,
}

impl InMemoryAccumulatorState {
    pub fn new(max_size: usize) -> Self {
        Self {
            max_size,
            indices: HashSet::with_capacity(max_size),
        }
    }
}

impl AccumulatorState for InMemoryAccumulatorState {
    fn is_empty(&self) -> bool {
        self.indices.is_empty()
    }

    fn capacity(&self) -> usize {
        self.max_size
    }

    fn has_index(&self, index: usize) -> bool {
        assert!(index <= self.max_size);
        self.indices.contains(&index)
    }

    /// Return true if the state did not have this value
    fn add(&mut self, index: usize) -> bool {
        assert!(index <= self.max_size);
        self.indices.insert(index)
    }

    /// Return true if the state did have this value
    fn remove(&mut self, index: usize) -> bool {
        assert!(index <= self.max_size);
        self.indices.remove(&index)
    }

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a usize> + 'a> {
        let iter: hash_set::Iter<'a, usize> = self.indices.iter();
        Box::new(iter)
    }
}

/// Iterator over accumulator state
pub struct IterAccumulatorState<'a, T: 'a> {
    pub inner: &'a mut T,
}

impl<'a> Iterator for IterAccumulatorState<'a, hash_set::Iter<'a, usize>> {
    type Item = &'a usize;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

/// Contains entries that are multiplied together to form the accumulator and witness
/// For each index there is 1 corresponding entry that goes in the accumulator.
pub trait AccumulatorEntries {
    fn size(&self) -> usize;
    fn get_g1(&self) -> &G1;
    fn get_g2(&self) -> &G2;
    // TODO: Rename `get_g1_power` and `get_g2_power` to more specific
    fn get_g1_power(&self, index: usize) -> &G1;
    fn get_g2_power(&self, index: usize) -> &G2;

    /// Return g1_{n + 1 - index}
    fn get_accumulator_entry_for_index(&self, index: usize) -> &G1 {
        self.get_g1_power(self.size() + 1 - index)
    }

    /// Return g1_{n + 1 - i + j} when for witness of index j and i != j
    fn get_witness_entry_for_index(&self, index: usize, witness_index: usize) -> &G1 {
        self.get_g1_power(self.size() + 1 - index + witness_index)
    }

    fn get_index_in_power_vector(&self, index: usize) -> usize {
        assert!(index > 0 && index != (self.size() + 1));
        if index > self.size() {
            index - 1
        } else {
            index
        }
    }
}

/// `gamma` is the trapdoor
fn generate_entries_from_trapdoor(size: usize, label: &[u8], gamma: &FieldElement) -> (G1Vector, G2Vector, GT) {
    // g1 and g2 come from random oracle
    let g1 = G1::from_msg_hash(&[label, " : g1".as_bytes()].concat());
    let g2 = G2::from_msg_hash(&[label, " : g2".as_bytes()].concat());

    // gamma_powers = [1, gamma, gamma^2, gamma^3, ..., gamma^{2*size}]
    let gamma_powers = FieldElementVector::new_vandermonde_vector(&gamma, 2 * size + 1);

    // g1_powers = g1, g1^gamma, g1^{gamma^2}, g1^{gamma^3}, .. g1^{gamma^n}, g1^{gamma^{n+2}},... g1^{gamma^{2*n}}
    let mut g1_powers = G1Vector::with_capacity(2 * size);
    // g2_powers = g2, g2^gamma, g2^{gamma^2}, g2^{gamma^3}, .. g2^{gamma^n}, g2^{gamma^{n+2}},... g2^{gamma^{2*n}}
    let mut g2_powers = G2Vector::with_capacity(2 * size);

    // z = e(g1, g2)^{gamma^{n+1}}
    let mut z = GT::new();

    // skip 1st element since its 1
    for i in 1..=2 * size {
        let l = &gamma_powers[i];
        if i == size + 1 {
            z = GT::ate_pairing(&g1, &g2);
            z = z.pow(l);
            continue;
        }
        // TODO: Add an efficient way since the same group element is used.
        g1_powers.push(&g1 * l);
        // If its not required to prove knowledge of an index in the accumulator (using the signature),
        // `g2_powers` need not have indices beyond `size`.
        g2_powers.push(&g2 * l);
    }

    // First element of g1_powers should be `g1`.
    g1_powers.insert(0, g1);
    // First element of g2_powers should be `g2`.
    g2_powers.insert(0, g2);

    (g1_powers, g2_powers, z)
}

/// Stores the accumulator entries (g^{lambda^i}) in memory. For production, these should be persisted
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InMemoryAccumulatorEntries {
    pub size: usize,
    /// 1-indexed
    pub g1_powers: G1Vector,
    /// 1-indexed
    pub g2_powers: G2Vector,
}

impl AccumulatorEntries for InMemoryAccumulatorEntries {
    fn size(&self) -> usize {
        self.size
    }

    fn get_g1(&self) -> &G1 {
        &self.g1_powers[0]
    }

    fn get_g2(&self) -> &G2 {
        &self.g2_powers[0]
    }

    fn get_g1_power(&self, index: usize) -> &G1 {
        let i = self.get_index_in_power_vector(index);
        &self.g1_powers[i]
    }

    fn get_g2_power(&self, index: usize) -> &G2 {
        let i = self.get_index_in_power_vector(index);
        &self.g2_powers[i]
    }
}

impl InMemoryAccumulatorEntries {
    fn new(size: usize, label: &[u8]) -> (InMemoryAccumulatorEntries, FieldElement, GT) {
        let trapdoor = FieldElement::random();

        let(g1_powers, g2_powers, z) = generate_entries_from_trapdoor(size, label, &trapdoor);

        (
            InMemoryAccumulatorEntries {
                size,
                g1_powers,
                g2_powers,
            },
            trapdoor,
            z,
        )
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Witness(G1, usize);

impl Witness {
    /// Compute witness for an index. Does not use trapdoor and computational complexity is
    /// proportional to the size of accumulator.
    pub fn for_index(
        index: usize,
        state: &dyn AccumulatorState,
        entries: &dyn AccumulatorEntries,
    ) -> Self {
        let mut witness = G1::new();
        for i in state.iter() {
            if *i == index {
                continue;
            }
            witness += entries.get_witness_entry_for_index(*i, index);
        }
        Self(witness, index)
    }

    /// Return a new witness computed from updating the current witness.
    pub fn update(
        &self,
        mut added: HashSet<usize>,
        mut removed: HashSet<usize>,
        entries: &dyn AccumulatorEntries,
    ) -> Self {
        // Check if `added` or `removed` have an intersection and don't process elements in the intersection
        let intersection: HashSet<usize> = added.intersection(&removed).map(|i| *i).collect();
        for i in intersection {
            // Ignore `i` like `i` was never added to the accumulator in the first place.
            added.remove(&i);
            removed.remove(&i);
        }

        let mut witness = self.0.clone();
        for i in added {
            witness += entries.get_witness_entry_for_index(i, self.1);
        }
        for i in removed {
            witness = witness - entries.get_witness_entry_for_index(i, self.1);
        }
        Self(witness, self.1)
    }

    /// Compute witness for an index using the trapdoor and computational complexity is constant.
    /// Checks whether the accumulator contains the index or not using the state and generates the
    /// accumulator value without the index. It then uses the trapdoor to compute the witness for that index
    /// and is much more efficient than using the entries in `AccumulatorEntries`
    pub fn for_index_using_trapdoor(
        index: usize,
        accum: &Accumulator,
        entries: &dyn AccumulatorEntries,
        state: &dyn AccumulatorState,
        trapdoor: &FieldElement,
    ) -> Self {
        let accum_without_index = if state.has_index(index) {
            &accum.0 - entries.get_accumulator_entry_for_index(index)
        } else {
            accum.0.clone()
        };

        Self::for_index_using_trapdoor_and_accumulator_without_index(
            index,
            &accum_without_index,
            trapdoor,
        )
    }

    /// Compute the witness for an index using trapdoor. Takes the accumulator that does not
    /// contain the index yet. Works by taking the accumulator and raising it to the `index`th power
    /// of the trapdoor.
    /// This works since the accumulator always has the value \prod_{all j in the accumulator} g_{n+1-j}.
    /// The witness for index i is \prod_{all j in the accumulator except i} g_{n+1-j+i} which is
    /// equivalent to raising \prod_{all j in the accumulator except i} g_{n+1-j} to `i`th power of trapdoor (gamma in the paper)
    /// \prod_{all j in the accumulator except i} g_{n+1-j+i} = {\prod_{all j in the accumulator except i} g_{n+1-j}}^{gamma^i}
    pub(crate) fn for_index_using_trapdoor_and_accumulator_without_index(
        index: usize,
        accum_without_index: &G1,
        trapdoor: &FieldElement,
    ) -> Self {
        let trapdoor_i = trapdoor.pow(&FieldElement::from(index as u64));
        let witness = accum_without_index * &trapdoor_i;
        Witness(witness, index)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Accumulator(G1);

impl Accumulator {
    pub fn new() -> Self {
        Accumulator(G1::identity())
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_identity()
    }

    pub fn add_index(
        &self,
        index: usize,
        entries: &dyn AccumulatorEntries,
        state: &mut dyn AccumulatorState,
    ) -> Accumulator {
        let was_absent = state.add(index);
        if was_absent {
            // Only update the accumulator if the accumulator did not have the index
            let entry = entries.get_accumulator_entry_for_index(index);
            self.add_entry(entry)
        } else {
            self.clone()
        }
    }

    pub fn add_entry(&self, entry: &G1) -> Accumulator {
        Accumulator(&self.0 + entry)
    }

    pub fn remove_index(
        &self,
        index: usize,
        entries: &dyn AccumulatorEntries,
        state: &mut dyn AccumulatorState,
    ) -> Accumulator {
        let was_present = state.remove(index);
        if was_present {
            // Only update the accumulator if the accumulator did have the index
            let entry = entries.get_accumulator_entry_for_index(index);
            self.remove_entry(entry)
        } else {
            self.clone()
        }
    }

    pub fn remove_entry(&self, entry: &G1) -> Accumulator {
        Accumulator(&self.0 - entry)
    }

    /// Check if an index is present in the accumulator
    pub fn has_index(
        &self,
        index: usize,
        witness: &Witness,
        entries: &dyn AccumulatorEntries,
        z: &GT,
    ) -> bool {
        let entry = entries.get_g2_power(index);
        let g2 = entries.get_g2();
        // Check e(self, entry) / e(witness, g2) == z which is equivalent to e(self, entry) * e(witness, g2)^-1 == z
        // which is equivalent to e(self, entry) * e(witness, g2^-1) == z. This can now be done using a multi-pairing
        let lhs = GT::ate_2_pairing(&self.0, entry, &witness.0, &(g2.negation()));
        lhs == *z
    }

    /// Checks if the accumulator contains the index and only return witness if the accumulator did not
    /// contain that index. Uses trapdoor to compute the witness. This method should be used for adding
    /// a new item to the accumulator by the entity that is incharge of updating the accumulator and
    /// knows the trapdoor as well
    pub fn add_index_and_compute_witness(
        &self,
        index: usize,
        entries: &dyn AccumulatorEntries,
        state: &mut dyn AccumulatorState,
        trapdoor: &FieldElement,
    ) -> (Accumulator, Option<Witness>) {
        let new_accum = self.add_index(index, entries, state);
        if self.0 != new_accum.0 {
            let witness = Witness::for_index_using_trapdoor_and_accumulator_without_index(
                index, &self.0, trapdoor,
            );
            (new_accum, Some(witness))
        } else {
            (new_accum, None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{thread_rng, Rng};

    /// Create a new accumulator, an in-memory state and in-memory accumulator entries.
    fn setup_accumulator_for_testing(
        size: usize,
        label: &[u8],
    ) -> (
        Accumulator,
        InMemoryAccumulatorState,
        InMemoryAccumulatorEntries,
        FieldElement,
        GT,
    ) {
        let (entries, trapdoor, z) = InMemoryAccumulatorEntries::new(size, label);
        let accum = Accumulator::new();
        let state = InMemoryAccumulatorState::new(size);
        (accum, state, entries, trapdoor, z)
    }

    #[test]
    fn test_accumulator_gen() {
        let size = 10;
        let (accum, state, entries, trapdoor, z) =
            setup_accumulator_for_testing(size, "test".as_bytes());
        assert!(accum.is_empty());
        assert!(state.is_empty());
        assert_eq!(entries.size, size);
        assert_eq!(entries.g1_powers.len(), 2 * size);
        assert_eq!(entries.g2_powers.len(), 2 * size);
        let g1 = entries.get_g1();
        let g2 = entries.get_g2();
        // pow = trapdoor^{size+1}
        let pow = trapdoor.pow(&FieldElement::from(size as u64 + 1));
        let expected_z = GT::ate_pairing(g1, g2).pow(&pow);
        assert_eq!(z, expected_z);
    }

    #[test]
    fn test_accumulator_addition_removal() {
        let size = 10;
        let (accum, mut state, entries, trapdoor, z) =
            setup_accumulator_for_testing(size, "test".as_bytes());
        let accum_1 = accum.add_index(1, &entries, &mut state);
        let witness_1 = Witness::for_index(1, &state, &entries);
        assert!(accum_1.has_index(1, &witness_1, &entries, &z));

        let accum_2 = accum_1.add_index(2, &entries, &mut state);
        assert!(!state.is_empty());
        let witness_2 = Witness::for_index(2, &state, &entries);
        assert!(accum_2.has_index(2, &witness_2, &entries, &z));

        // Old witness for index 1 should not work
        assert!(!accum_2.has_index(1, &witness_1, &entries, &z));
        // Recompute witness for index 1
        let witness_1 = Witness::for_index(1, &state, &entries);
        assert!(accum_2.has_index(1, &witness_1, &entries, &z));

        let accum_3 = accum_2.remove_index(1, &entries, &mut state);
        assert!(!state.is_empty());
        let accum_3_3 = accum_3.remove_index(1, &entries, &mut state);
        assert_eq!(accum_3.0, accum_3_3.0);

        // Recompute witness for index 2
        let witness_2 = Witness::for_index(2, &state, &entries);
        assert!(accum_3.has_index(2, &witness_2, &entries, &z));
        // Recompute witness for index 1
        let witness_1 = Witness::for_index(1, &state, &entries);
        assert!(!accum_3.has_index(1, &witness_1, &entries, &z));

        let accum_4 = accum_3.remove_index(2, &entries, &mut state);
        assert!(state.is_empty());
        assert!(!accum_4.has_index(1, &witness_1, &entries, &z));
        // Recompute witness for index 2
        let witness_2 = Witness::for_index(2, &state, &entries);
        assert!(!accum_4.has_index(2, &witness_2, &entries, &z));

        // Removing an already removed item has no effect
        let accum_5 = accum_4.remove_index(1, &entries, &mut state);
        assert_eq!(accum_4.0, accum_5.0);
        let accum_6 = accum_4.remove_index(2, &entries, &mut state);
        assert_eq!(accum_4.0, accum_6.0);
    }

    #[test]
    fn test_accumulator_addition_removal_random_indices() {
        let size = 20;
        let (accum, mut state, entries, trapdoor, z) =
            setup_accumulator_for_testing(size, "test".as_bytes());

        let mut rng = thread_rng();
        let num_indices_to_add = 10;
        let mut indices_to_add = HashSet::new();
        while indices_to_add.len() < num_indices_to_add {
            indices_to_add.insert(rng.gen_range(1, size + 1));
        }

        let mut cur_accum = accum.clone();
        for i in &indices_to_add {
            cur_accum = cur_accum.add_index(*i, &entries, &mut state);
            let witness = Witness::for_index(*i, &state, &entries);
            assert!(cur_accum.has_index(*i, &witness, &entries, &z));
        }

        for i in &indices_to_add {
            let witness = Witness::for_index(*i, &state, &entries);
            assert!(cur_accum.has_index(*i, &witness, &entries, &z));
        }

        for i in &indices_to_add {
            cur_accum = cur_accum.remove_index(*i, &entries, &mut state);
            let witness = Witness::for_index(*i, &state, &entries);
            assert!(!cur_accum.has_index(*i, &witness, &entries, &z));
        }

        for i in &indices_to_add {
            let witness = Witness::for_index(*i, &state, &entries);
            assert!(!cur_accum.has_index(*i, &witness, &entries, &z));
        }

        assert!(cur_accum.is_empty());
    }

    #[test]
    fn test_accumulator_witness_update() {
        let size = 20;
        let (accum, mut state, entries, trapdoor, z) =
            setup_accumulator_for_testing(size, "test".as_bytes());

        // Do in order:
        // Add indices a, b, c.
        // Get witness for c
        // Add indices d, e.
        // Remove indices b and d
        // Update witness for c
        let a = 2;
        let b = 5;
        let c = 14;
        let d = 11;
        let e = 19;

        let accum_1 = accum.add_index(a, &entries, &mut state);
        let accum_2 = accum_1.add_index(b, &entries, &mut state);
        let accum_3 = accum_2.add_index(c, &entries, &mut state);

        let witness_c_old = Witness::for_index(c, &state, &entries);
        assert!(accum_3.has_index(c, &witness_c_old, &entries, &z));

        let accum_4 = accum_3.add_index(d, &entries, &mut state);
        let accum_5 = accum_4.add_index(e, &entries, &mut state);

        let accum_6 = accum_5.remove_index(d, &entries, &mut state);
        let accum_7 = accum_6.remove_index(b, &entries, &mut state);

        let witness_c_new = Witness::for_index(c, &state, &entries);
        assert!(accum_7.has_index(c, &witness_c_new, &entries, &z));

        let added: HashSet<usize> = [d, e].iter().cloned().collect();
        let removed: HashSet<usize> = [b, d].iter().cloned().collect();
        let witness_c_updated = witness_c_old.update(added, removed, &entries);
        assert!(accum_7.has_index(c, &witness_c_updated, &entries, &z));
    }

    #[test]
    fn test_accumulator_witness_using_trapdoor() {
        let size = 20;
        let (accum, mut state, entries, trapdoor, z) =
            setup_accumulator_for_testing(size, "test".as_bytes());

        let mut rng = thread_rng();
        let num_indices_to_add = 10;
        let mut indices_to_add = HashSet::new();
        while indices_to_add.len() < num_indices_to_add {
            indices_to_add.insert(rng.gen_range(1, size + 1));
        }

        let mut cur_accum = accum.clone();
        let mut witness: Option<Witness> = None;
        for i in &indices_to_add {
            let t = cur_accum.add_index_and_compute_witness(*i, &entries, &mut state, &trapdoor);
            cur_accum = t.0;
            witness = t.1;
            assert!(cur_accum.has_index(*i, &witness.unwrap(), &entries, &z));
        }

        for i in &indices_to_add {
            let witness =
                Witness::for_index_using_trapdoor(*i, &cur_accum, &entries, &state, &trapdoor);
            assert!(cur_accum.has_index(*i, &witness, &entries, &z));
        }

        for i in &indices_to_add {
            cur_accum = cur_accum.remove_index(*i, &entries, &mut state);
            let witness =
                Witness::for_index_using_trapdoor(*i, &cur_accum, &entries, &state, &trapdoor);
            assert!(!cur_accum.has_index(*i, &witness, &entries, &z));
        }
    }
}
