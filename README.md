# Revocable Proof Systems — Lean 4 Formalization

A formal verification in Lean 4 (with Mathlib) of **Theorem 1** from:

> Miranda Christ and Joseph Bonneau.
> *"Limits on revocable proof systems, with applications to stateless blockchains."*
> [ePrint 2022/1478](https://eprint.iacr.org/2022/1478) / [FC 2023, LNCS 13951, Springer](https://link.springer.com/chapter/10.1007/978-3-031-47751-5_4)

## Background

### The Problem: Stateless Blockchains

In traditional blockchains like Bitcoin, every validator must store the entire system state — the set of all unspent transaction outputs (UTXOs). As the state grows (Bitcoin currently has over 85 million UTXOs requiring several GB), this raises centralization concerns: only well-funded organizations can afford to run validators.

**Stateless blockchains** attempt to solve this by having validators store only a small commitment to the state (e.g., a Merkle root). Users who wish to make a transaction must provide a *witness* (e.g., a Merkle proof) that their transaction is valid given the current state commitment.

### The Catch: Witness Staleness

The fundamental problem with stateless blockchains is that whenever the global state changes (i.e., someone else makes a transaction), existing witnesses may become invalid. Users must monitor the network and periodically refresh their witnesses — a significant departure from the traditional model where users can stay offline indefinitely.

### This Paper's Contribution

Christ and Bonneau prove that this trade-off is **fundamental and unavoidable**. They introduce the abstract notion of a *revocable proof system* (RPS) and show an information-theoretic lower bound: any RPS must either have a linear-sized global state or require a near-linear rate of witness updates. There is no "sweet spot" in between.

## The Paper's Definitions

### Revocable Proof System (Definition from Section 2)

A revocable proof system RPS = (Setup, ComputeState, Revoke, Verify) consists of four algorithms:

- **Setup(1^λ) → pp**: Generates public parameters.
- **ComputeState(pp, S) → V, (π₁, ..., πₙ)**: Given a valid set S of size n, outputs a global state V and a proof πᵢ for each statement sᵢ ∈ S.
- **Revoke(pp, S, T, V, (π₁, ..., πₙ)) → V', (π'₁, ..., π'ₙ)**: Given a revoked set T ⊆ S, outputs an updated global state V' and updated proofs.
- **Verify(pp, V, sᵢ, πᵢ) → {true, false}**: Verifies a proof against a global state.

**Correctness** requires that genuine proofs for non-revoked elements always verify:
for every S, T ⊆ S, and sᵢ ∈ S \ T, both Verify(pp, V, sᵢ, πᵢ) = true and Verify(pp, V', sᵢ, π'ᵢ) = true hold with probability 1.

**Security** requires that it is computationally hard for an adversary to produce a proof for a revoked element that still verifies against the updated state.

### k-good Revoked Set (Definition 3)

A revoked set T is **k-good** if, when T is revoked:

1. **All revoked elements fail**: For every sᵢ ∈ T, the original proof πᵢ no longer verifies against V'. This is a consequence of security.
2. **Few non-revoked elements change**: At most k non-revoked elements sⱼ ∈ (S \ T) have their original proofs πⱼ fail against V'. These are the elements whose witnesses must be updated.

## Theorem 1 (Original Statement)

> Let RPS = (Setup, ComputeState, Revoke, Verify) be a revocable proof system satisfying correctness, and let pp be any public parameters occurring with nonzero probability over Setup(1^λ). Let S be a set of size n, and let X\*\_k denote the set of subsets T ⊆ S that are k-good given RPS, S, and public parameters pp. Then |V|, the size of the global state in bits, satisfies:
>
> **|V| ≥ lg |X\*\_k| − ⌈k lg n⌉**

In words: the global state must be large enough to "pay for" the information content of the k-good sets, minus the information that can be communicated through the at most k changed witnesses.

## Formalization

### Abstraction Approach

Rather than formalizing all four RPS algorithms directly, we fix the public parameters pp and the initial output of ComputeState, and abstract the system into two essential functions:

```lean
structure RevocableProofSystem (S : Type*) (V : Type*) where
  revokedState : Finset S → V       -- Maps revoked set T to updated state V'
  failingSet   : V → Finset S       -- Maps state V' to {s ∈ S₀ : Verify(pp, V', s, πₛ) = false}
```

- `revokedState T` corresponds to `Revoke(pp, S₀, T, V₀, πs).fst` — the updated global state after revoking T.
- `failingSet v` corresponds to `{s ∈ S₀ : Verify(pp, v, s, πₛ) = false}` — the set of elements whose original proofs fail against state v.

This abstraction is sufficient because Theorem 1's proof only depends on these two functions (the proofs πᵢ and the Verify function are only accessed through `failingSet`).

### Lean Definitions (`RevocableProofSystem/Defs.lean`)

| Lean Definition | Paper Concept | Description |
|---|---|---|
| `RevocableProofSystem S V` | RPS after fixing pp, S₀ | Structure with `revokedState` and `failingSet` |
| `IsKGood rps S₀ k T` | Definition 3 | T ⊆ S₀ ∧ T ⊆ failingSet(revokedState(T)) ∧ \|failingSet(revokedState(T)) \ T\| ≤ k |
| `encode rps T` | Encoder A | Maps T to (revokedState(T), failingSet(revokedState(T)) \ T) |
| `decode rps (v, L)` | Decoder B | Maps (v, L) to failingSet(v) \ L |

### Theorem Statement (Cardinality Form)

The original bit-level statement |V| ≥ lg |X\*\_k| − ⌈k lg n⌉ is equivalent to the following cardinality bound, which is more natural to express in Lean:

> **|X\*\_k| ≤ |V\_type| × |{L ⊆ S₀ : |L| ≤ k}|**

where |V\_type| is the cardinality of the type of global states (corresponding to 2^|V| when V is a bit string of length |V|).

In Lean:

```lean
theorem theorem1 [Fintype V]
    (rps : RevocableProofSystem S V) (S₀ : Finset S) (k : ℕ)
    (h_fail_sub : ∀ (v : V), rps.failingSet v ⊆ S₀)
    (Xk : Finset (Finset S))
    (hXk : ∀ T ∈ Xk, IsKGood rps S₀ k T) :
    Xk.card ≤ Fintype.card V * (S₀.powerset.filter (fun L => L.card ≤ k)).card
```

### Proof Structure (`RevocableProofSystem/Theorem1.lean`)

The proof follows the paper's compression argument in three steps:

#### Step 1: Decoding Correctness (`decode_encode_eq`)

We show that for any k-good set T, decoding its encoding recovers T exactly:

```
decode(encode(T)) = failingSet(revokedState(T)) \ (failingSet(revokedState(T)) \ T) = T
```

This uses the Finset identity `B \ (B \ A) = A` when `A ⊆ B` (Mathlib's `Finset.sdiff_sdiff_eq_self`).

The proof that A ⊆ B (i.e., T ⊆ failingSet(revokedState(T))) comes directly from condition (1) of the k-good definition: all revoked elements must have failing proofs.

#### Step 2: Injectivity of the Encoding (`encode_injOn`)

From Step 1, if `encode(T₁) = encode(T₂)` for two k-good sets, then:

```
T₁ = decode(encode(T₁)) = decode(encode(T₂)) = T₂
```

Therefore `encode` is injective on the set of k-good subsets.

#### Step 3: Cardinality Bound (`theorem1`)

Since `encode` is injective and maps k-good sets into the finite product `V × {L ⊆ S₀ : |L| ≤ k}`, we conclude:

```
|X*_k| ≤ |V_type| × |{L ⊆ S₀ : |L| ≤ k}|
```

This uses Mathlib's `Finset.card_le_card_of_injOn`: if there is an injective function from Finset A into Finset B, then |A| ≤ |B|.

### Why This Implies the Paper's Statement

Taking log₂ of both sides of our cardinality bound:

```
lg |X*_k| ≤ lg |V_type| + lg |{L ⊆ S₀ : |L| ≤ k}|
```

Since |V\_type| = 2^|V| and |{L ⊆ S₀ : |L| ≤ k}| ≤ 2^(⌈k lg n⌉), this gives:

```
lg |X*_k| ≤ |V| + ⌈k lg n⌉
```

Rearranging: **|V| ≥ lg |X\*\_k| − ⌈k lg n⌉**, which is exactly the paper's Theorem 1.

## Building

Prerequisites: [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
# Fetch dependencies (downloads Mathlib and its precompiled cache)
lake update

# Build the project
lake build
```

The build should complete with no errors and no warnings.

## Project Structure

```
.
├── README.md
├── lakefile.lean                      # Lake build configuration (Mathlib dependency)
├── lean-toolchain                     # Lean version (v4.16.0)
├── RevocableProofSystem.lean          # Root module (imports Defs + Theorem1)
└── RevocableProofSystem/
    ├── Defs.lean                      # RPS definition, k-good, encode/decode
    └── Theorem1.lean                  # Theorem 1: proof via compression argument
```

## References

- Miranda Christ and Joseph Bonneau. "Limits on revocable proof systems, with applications to stateless blockchains." *Financial Cryptography and Data Security (FC 2023)*, LNCS 13951, Springer. [ePrint 2022/1478](https://eprint.iacr.org/2022/1478)
