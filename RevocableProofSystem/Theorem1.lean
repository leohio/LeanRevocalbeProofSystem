/-
# Theorem 1 — Main Lower Bound

Formalization of Theorem 1 from:
  "Limits on revocable proof systems, with applications to stateless blockchains"
  Miranda Christ and Joseph Bonneau (2022)
  https://eprint.iacr.org/2022/1478

## Theorem Statement (original)

Let RPS = (Setup, ComputeState, Revoke, Verify) be a revocable proof system
satisfying correctness, and let pp be any public parameters occurring with
nonzero probability over Setup(1^λ). Let S be a set of size n, and let X*_k
denote the set of subsets T ⊆ S that are k-good given RPS, S, and public
parameters pp. Then |V|, the size of the global state in bits, satisfies:

  |V| ≥ lg |X*_k| − ⌈k lg n⌉

## Equivalent Cardinality Formulation

The theorem is equivalent to the following cardinality bound:

  |X*_k| ≤ |V_type| × |{L ⊆ S₀ : |L| ≤ k}|

where |V_type| is the number of possible global states (= 2^|V| in bits).

## Proof Strategy

1. Construct an encoding function: T ↦ (revokedState(T), failingSet(revokedState(T)) \ T)
2. Show the encoding is injective on k-good sets via a decoding argument
3. Conclude by cardinality: |X*_k| ≤ |codomain of encoding|
-/

import RevocableProofSystem.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

open Finset

variable {S V : Type*} [DecidableEq S] [DecidableEq V]

/-! ## Step 1: Decoding correctness

We show that for any k-good set T, decoding the encoding of T recovers T exactly:
  decode(encode(T)) = T

This is the core of the compression argument.
-/

omit [DecidableEq V] in
/-- For any set T that is a subset of failingSet(revokedState(T)),
decoding the encoding of T recovers T exactly.
This is the key lemma: the encoding is a left inverse of decoding on k-good sets. -/
theorem decode_encode_eq (rps : RevocableProofSystem S V) (T : Finset S)
    (h_sub : T ⊆ rps.failingSet (rps.revokedState T)) :
    decode rps (encode rps T) = T := by
  unfold encode decode
  simp only
  -- Goal: failingSet(revokedState(T)) \ (failingSet(revokedState(T)) \ T) = T
  -- This follows from: if A ⊆ B then B \ (B \ A) = A
  exact Finset.sdiff_sdiff_eq_self h_sub

/-! ## Step 2: Injectivity of the encoding

Since decode ∘ encode = id on k-good sets, the encoding is injective.
-/

omit [DecidableEq V] in
/-- The encoding function is injective on k-good sets.
If two k-good sets have the same encoding, they are equal. -/
theorem encode_injOn (rps : RevocableProofSystem S V) (S₀ : Finset S) (k : ℕ) :
    Set.InjOn (encode rps) {T | IsKGood rps S₀ k T} := by
  intro T₁ hT₁ T₂ hT₂ h_eq
  have h1 : T₁ ⊆ rps.failingSet (rps.revokedState T₁) := hT₁.2.1
  have h2 : T₂ ⊆ rps.failingSet (rps.revokedState T₂) := hT₂.2.1
  -- Since decode ∘ encode = id on k-good sets:
  have := decode_encode_eq rps T₁ h1
  rw [h_eq] at this
  rw [decode_encode_eq rps T₂ h2] at this
  exact this.symm

/-! ## Step 3: Cardinality bound (Theorem 1)

The injectivity of the encoding, combined with bounds on the codomain,
gives us the main cardinality inequality.

### Theorem 1 (Cardinality Form)

For any collection Xk of k-good subsets of S₀:

  |Xk| ≤ |V_type| × |{L ⊆ S₀ : |L| ≤ k}|

where V_type is the finite type of possible global states.
-/

omit [DecidableEq V] in
/-- The encoding of a k-good set T maps into the product of global states and
small subsets: the second component has cardinality at most k. -/
theorem encode_snd_card_le (rps : RevocableProofSystem S V) (S₀ : Finset S) (k : ℕ)
    (T : Finset S) (hT : IsKGood rps S₀ k T) :
    (encode rps T).2.card ≤ k := by
  exact hT.2.2

omit [DecidableEq V] in
/-- The encoding of a k-good set has its second component as a subset of S₀,
provided the failingSet always returns subsets of S₀. -/
theorem encode_snd_sub (rps : RevocableProofSystem S V) (S₀ : Finset S)
    (T : Finset S) (h_fail_sub : rps.failingSet (rps.revokedState T) ⊆ S₀) :
    (encode rps T).2 ⊆ S₀ := by
  unfold encode
  simp only
  exact Finset.sdiff_subset.trans h_fail_sub

/-! ## Main Theorem

**Theorem 1** (Christ-Bonneau 2022): The number of k-good subsets is bounded
by the number of possible global states times the number of subsets of S₀
with at most k elements.

In the paper's notation with bits:
  |V| ≥ lg |X*_k| − ⌈k lg n⌉

is equivalent to:
  |X*_k| ≤ 2^|V| × n^k

Our formalization proves the tighter bound:
  |X*_k| ≤ |V_type| × |{L ⊆ S₀ : |L| ≤ k}|
-/

omit [DecidableEq V] in
/-- **Theorem 1** (Christ-Bonneau 2022).

Let `rps` be a revocable proof system, `S₀` the initial valid set of size n,
and `k` a bound on the number of proof updates. Let `Xk` be any collection of
k-good subsets of `S₀`. Then:

  `|Xk| ≤ |V_type| × |{L ⊆ S₀ : |L| ≤ k}|`

This is proved by constructing an injective encoding from Xk into the product
`V × {L ⊆ S₀ : |L| ≤ k}`, using the compression argument from the paper:
for each T, encode as (revokedState(T), failingSet(revokedState(T)) \ T),
and decode as failingSet(V') \ L. -/
theorem theorem1 [Fintype V]
    (rps : RevocableProofSystem S V) (S₀ : Finset S) (k : ℕ)
    (h_fail_sub : ∀ (v : V), rps.failingSet v ⊆ S₀)
    (Xk : Finset (Finset S))
    (hXk : ∀ T ∈ Xk, IsKGood rps S₀ k T) :
    Xk.card ≤ Fintype.card V * (S₀.powerset.filter (fun L => L.card ≤ k)).card := by
  -- We construct an injective function from Xk to V × {L ⊆ S₀ : |L| ≤ k}
  -- and then use cardinality bounds.
  -- Step 1: Define the target Finset in the product type
  let target := Finset.univ (α := V) ×ˢ (S₀.powerset.filter (fun L => L.card ≤ k))
  -- Step 2: Show encode maps Xk into target
  have h_encode_mem : ∀ T ∈ Xk, encode rps T ∈ target := by
    intro T hT
    simp only [target, mem_product, mem_univ, true_and, mem_filter, mem_powerset]
    constructor
    · exact encode_snd_sub rps S₀ T (h_fail_sub _)
    · exact encode_snd_card_le rps S₀ k T (hXk T hT)
  -- Step 3: Show encode is injective on Xk
  have h_inj : Set.InjOn (encode rps) (↑Xk : Set (Finset S)) := by
    intro T₁ hT₁ T₂ hT₂ h_eq
    exact encode_injOn rps S₀ k (hXk T₁ (mem_coe.mp hT₁)) (hXk T₂ (mem_coe.mp hT₂)) h_eq
  -- Step 4: Apply cardinality bound from injectivity
  have h_card_le := Finset.card_le_card_of_injOn (encode rps) h_encode_mem h_inj
  -- Step 5: Bound target cardinality
  calc Xk.card
      ≤ target.card := h_card_le
    _ = (Finset.univ (α := V)).card *
        (S₀.powerset.filter (fun L => L.card ≤ k)).card := card_product _ _
    _ = Fintype.card V *
        (S₀.powerset.filter (fun L => L.card ≤ k)).card := by
          rw [← Finset.card_univ]
