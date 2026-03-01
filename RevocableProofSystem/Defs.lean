/-
# Revocable Proof Systems — Definitions

Formalization of definitions from:
  "Limits on revocable proof systems, with applications to stateless blockchains"
  Miranda Christ and Joseph Bonneau (2022)
  https://eprint.iacr.org/2022/1478

A revocable proof system (RPS) maintains a global state V, a valid set S,
and proofs πᵢ for each element sᵢ ∈ S. The global state commits to the valid set,
such that proofs of elements in S can be verified. A subset T ⊆ S may later be
revoked, yielding an updated global state V'.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic

open Finset

/-! ## Definition: Revocable Proof System

We abstract a revocable proof system by two key functions, fixing public parameters
pp, an initial valid set S₀, and the output of ComputeState(pp, S₀) = (V₀, π₁,...,πₙ):

* `revokedState`: Given a revoked set T ⊆ S₀, produces the updated global state V'.
  This corresponds to Revoke(pp, S₀, T, V₀, (π₁,...,πₙ)).fst.
* `failingSet`: Given a global state V', returns the set of elements s ∈ S₀ whose
  original proofs πₛ fail against V', i.e., {s ∈ S₀ : Verify(pp, V', s, πₛ) = false}.

This abstraction captures the essential structure needed for Theorem 1.
-/

/-- An abstract revocable proof system with statement type `S` and global state type `V`.
This captures the behavior after fixing public parameters and initial state. -/
structure RevocableProofSystem (S : Type*) (V : Type*) where
  /-- Maps a revoked set T to the updated global state.
  Corresponds to `Revoke(pp, S₀, T, V₀, πs).fst`. -/
  revokedState : Finset S → V
  /-- Given a global state, returns elements of S₀ whose original proofs fail.
  i.e., `{s ∈ S₀ : Verify(pp, v, s, π_s) = false}`. -/
  failingSet : V → Finset S

/-! ## Definition 3: k-good revoked set (Christ-Bonneau 2022)

A revoked set T is k-good if:
1. For every revoked element sᵢ ∈ T, the original proof fails: Verify(pp, V', sᵢ, πᵢ) = false
2. At most k non-revoked elements sⱼ ∈ (S₀ \ T) have failing proofs

Condition (1) is a consequence of security.
Condition (2) says few proofs of non-revoked statements need updating.
-/

/-- A revoked set `T` is `k`-good with respect to an RPS and initial set `S₀` if:
1. All revoked elements have failing proofs: `T ⊆ failingSet(revokedState(T))`
2. At most `k` non-revoked elements have failing proofs:
   `|failingSet(revokedState(T)) \ T| ≤ k` -/
def IsKGood {S : Type*} {V : Type*} [DecidableEq S]
    (rps : RevocableProofSystem S V) (S₀ : Finset S) (k : ℕ)
    (T : Finset S) : Prop :=
  T ⊆ S₀ ∧
  T ⊆ rps.failingSet (rps.revokedState T) ∧
  (rps.failingSet (rps.revokedState T) \ T).card ≤ k

/-! ## Encoding and Decoding

The key to the proof of Theorem 1 is an encoding/decoding scheme.

**Encoding**: For T ∈ X*_k, encode T as the pair (V', L) where:
  - V' = revokedState(T)  (the updated global state)
  - L = failingSet(V') \ T  (non-revoked elements with failing proofs, |L| ≤ k)

**Decoding**: Given (V', L), recover T = failingSet(V') \ L.

The proof shows decode(encode(T)) = T for any k-good T, establishing injectivity.
-/

/-- Encode a revoked set T as a pair (updated state, list of changed non-revoked proofs). -/
def encode {S : Type*} {V : Type*} [DecidableEq S]
    (rps : RevocableProofSystem S V) (T : Finset S) : V × Finset S :=
  (rps.revokedState T, rps.failingSet (rps.revokedState T) \ T)

/-- Decode a pair (state, changed-proof-list) back to a revoked set. -/
def decode {S : Type*} {V : Type*} [DecidableEq S]
    (rps : RevocableProofSystem S V) (p : V × Finset S) : Finset S :=
  rps.failingSet p.1 \ p.2
