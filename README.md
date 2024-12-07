# Agda Adjoint Logic

Encoding of Adjoint Logic in Agda based on Pruiksma, Chargin, Pfenning, and Reed's [Adjoint Logic](https://www.cs.cmu.edu/~fp/papers/adjoint18b.pdf). Currently, only ADJE, or Adjoint Logic with explicit structural rules, is encoded.

## How to Use

### ADJE

The ADJE module can be instantiated with the following inputs:

- `U : Set`, or the base type for base propositions.
- `BotMode : Mode`, or the bottom-most mode of the lattice.
- `_≥_ : Mode → Mode → Set`, or a preorder on modes.
- `_≥?_ : (m k : Mode)  → Dec (m ≥ k)`, or a decidable preorder on modes.

## References
- Pruiksma, Klaas, William Chargin, Frank Pfenning, and Jason Reed. "Adjoint logic." Unpublished manuscript, April (2018).
- Kokke, Wen. "Modelling Substructural Logics in Agda." (2014).

