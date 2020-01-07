# Accumulator using Bilinear maps

Based on the paper An Accumulator [Based on Bilinear Maps and Efficient Revocation for Anonymous Credentials](https://eprint.iacr.org/2008/539.pdf). 
Modified to work with type-3 pairings. Adds 2 features not mentioned in the paper:
1. Ability to remove indices from the accumulator.
1. Efficient witness generation (independent of the size of the accumulator) using knowledge of trapdoor

Accumulator from section 3.2 of the paper

## API
1. Accumulator is defined over group G1. To initialize a new Accumulator, call `Accumulator::new`.
1. To track which indices are present in the accumulator so that they are not accidentally added again or removed when 
they were not present and to update witness, a trait `AccumulatorState` is defined. For testing, an in-memory implementation is present. 
1. For generating and querying entries which are added to the accumulator, a trait `AccumulatorEntries` is defined. 
For testing, an in-memory implementation is defined.
1. For a sample of how an accumulator is setup, look at testing function `setup_accumulator_for_testing`.

1. To add an index `idx` in the accumulator, use method `Accumulator::add_index`. The method returns a new accumulator and updates the `state`. 
Suppose `accum` is the accumulator before adding that index, `state` is an `AccumulatorState` and `entries` is an `AccumulatorEntries`, then this is how to add in index
    ```rust
    // indices are 1-based. `accum` does not have the index `idx` but `accum_1` does
    let accum_1 = accum.add_index(idx, &entries, &mut state);
    ```
   
1. To check presence of a value in an accumulator, a `Witness` is needed. To generate a witness, there are 2 methods, 
the slower one does not require a trapdoor and has complexity proportional to the size of the accumulator but the faster 
one using the trapdoor has constant asymptotic complexity.  
To generate a witness for index `idx` without using the trapdoor, use method `Witness::for_index` which iterates over the 
indices in `state` and gets the corresponding entries from `entries`.  
    ```rust
    let witness = Witness::for_index(idx, &state, &entries);
    ```
   
    To generate a witness for index `idx` using the trapdoor
    ```rust
    // `cur_accum` is the accumulator without `idx`. 
    let witness = Witness::for_index_using_trapdoor(idx, &cur_accum, &entries, &state, &trapdoor);
    ```
   
1. To check whether an index `idx` is present in the accumulator, use method `Accumulator::has_index`.
    ```rust
    // `witness` is a `Witness` and `z` = e(g1, g2)^{gamma^{size+1}} 
    accum_1.has_index(idx, &witness, &entries, &z);
    ```

1. To update the witness after some elements have been added or removed, the old witness can be updated using `Witness:update`.
    ```rust
    // `witness_old` is the old witness which is being updated, `added` and `removed` are the `HashSet`s of added and 
    removed indices. 
    let witness_updated = witness_old.update(added, removed, &entries);
    ```

1. To remove an index `idx`, use `Accumulator::remove_index` to get a new accumulator with the index removed.
    ```rust
    // indices are 1-based. `accum` has the index `idx` but `accum_1` does not
    let accum_1 = accum.remove_index(idx, &entries, &mut state);
    ```

1. If the entry updating the accumulator has access to trapdoor, there is a convenience method to add an index and 
efficiently compute the witness as well.
    ```rust
    let (new_accum, wit) = cur_accum.add_index_and_compute_witness(idx, &entries, &mut state, &trapdoor);
    ``` 


See the tests for detailed examples.

## TODO:
- Signature to prove knowledge of accumulated value.
- Check if for signatures, BBS+ can be avoided and PS can be used instead.
- Check if tradeoffs possible by switching groups G1 and G2.
- Convert asserts to errors

