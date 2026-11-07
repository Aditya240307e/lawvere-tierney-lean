/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import LawvereTierney.Poset
public import Mathlib.Data.Fintype.Powerset

/-!
# Subset topologies on a well-founded poset

For a subset `X` of a preorder `P` there is a Grothendieck topology `ofSubset X` in which a sieve
on `p` is covering when it contains every element of `X` below `p`. Larger subsets give coarser
topologies, `⊤ ⊆ P` giving the trivial topology and `∅` the topology in which every sieve covers.

If `P` is a well-founded poset, every Grothendieck topology arises this way from exactly one
subset: the points `p` for which the sieve of strict predecessors of `p` is not covering. The proof
that such a topology contains `ofSubset X` is by well-founded induction, using transitivity.
In particular a finite poset with `n` elements has exactly `2 ^ n` Grothendieck topologies.

## Main definitions

* `CategoryTheory.GrothendieckTopology.ofSubset`: the topology of a subset.
* `CategoryTheory.GrothendieckTopology.uncovered`: the subset recovered from a topology.
* `CategoryTheory.GrothendieckTopology.orderIsoSubset`: topologies on a well-founded poset are
  subsets, with the order reversed.

## Main results

* `CategoryTheory.GrothendieckTopology.eq_ofSubset_uncovered`: on a well-founded preorder every
  topology is a subset topology.
* `CategoryTheory.GrothendieckTopology.card_eq_two_pow`: the number of topologies on a finite
  poset.

## References

* A. J. Lindenhovius, *Grothendieck topologies on posets*, arXiv:1405.4408. There the subset
  topologies are classified, and shown to be all topologies exactly when the poset is Artinian
  (every nonempty subset has a minimal element), which is `WellFoundedLT` here.
* J. Hemelaer, *Grothendieck topologies on posets*, arXiv:1811.10039, for the general case.
-/

@[expose] public section

universe u

namespace CategoryTheory

variable {P : Type u}

section Preorder

variable [Preorder P]

namespace Sieve

/-- The sieve on `p` of the elements strictly below `p`. -/
def strict (p : P) : Sieve p :=
  ofLowerSet (LowerSet.Iio p) p

theorem strict_apply {p q : P} (f : q ⟶ p) : strict p f ↔ q < p :=
  Iff.rfl

end Sieve

namespace GrothendieckTopology

/-- The topology in which a sieve on `p` covers when it contains all elements of `X` below `p`. -/
def ofSubset (X : Set P) : GrothendieckTopology P where
  sieves p := {S | ∀ ⦃q⦄ (h : q ≤ p), q ∈ X → S (homOfLE h)}
  top_mem' _ := fun _ _ _ => True.intro
  pullback_stable' _ _ _ f hS := fun _ h hr => hS (h.trans (leOfHom f)) hr
  transitive' _ _ hS _ hR := fun _ h hq => hR (hS h hq) le_rfl hq

theorem mem_ofSubset_iff {X : Set P} {p : P} {S : Sieve p} :
    S ∈ ofSubset X p ↔ ∀ ⦃q⦄ (h : q ≤ p), q ∈ X → S (homOfLE h) :=
  Iff.rfl

theorem ofSubset_anti : Antitone (ofSubset : Set P → GrothendieckTopology P) :=
  fun _ _ hXY _ _ hS _ h hq => hS h (hXY hq)

/-- The points whose sieve of strict predecessors is not covering. -/
def uncovered (J : GrothendieckTopology P) : Set P :=
  {p | Sieve.strict p ∉ J p}

theorem mem_uncovered_iff {J : GrothendieckTopology P} {p : P} :
    p ∈ J.uncovered ↔ Sieve.strict p ∉ J p :=
  Iff.rfl

/-- A topology is contained in the subset topology of its uncovered points. -/
theorem le_ofSubset_uncovered (J : GrothendieckTopology P) : J ≤ ofSubset J.uncovered := by
  intro p S hS q h hq
  by_contra hSq
  refine hq (J.superset_covering ?_ (J.pullback_stable (homOfLE h) hS))
  intro r g hg
  exact lt_of_le_not_ge (leOfHom g) fun hqr => hSq (S.downward_closed hg (homOfLE hqr))

/-- On a well-founded preorder the subset topology of the uncovered points is contained in the
topology. -/
theorem ofSubset_uncovered_le [WellFoundedLT P] (J : GrothendieckTopology P) :
    ofSubset J.uncovered ≤ J := by
  have key : ∀ (p : P) (S : Sieve p), S ∈ ofSubset J.uncovered p → S ∈ J p := by
    intro p
    induction p using WellFoundedLT.induction with
    | _ p ih =>
      intro S hS
      by_cases hp : Sieve.strict p ∈ J p
      · exact J.transitive hp S fun q f hf =>
          ih q hf _ ((ofSubset J.uncovered).pullback_stable f hS)
      · rw [Sieve.id_mem_iff_eq_top.1 (hS le_rfl hp)]
        exact J.top_mem p
  exact fun p S hS => key p S hS

theorem eq_ofSubset_uncovered [WellFoundedLT P] (J : GrothendieckTopology P) :
    J = ofSubset J.uncovered :=
  le_antisymm (le_ofSubset_uncovered J) (ofSubset_uncovered_le J)

end GrothendieckTopology

end Preorder

section PartialOrder

variable [PartialOrder P]

namespace GrothendieckTopology

theorem strict_mem_ofSubset_iff {X : Set P} {p : P} :
    Sieve.strict p ∈ ofSubset X p ↔ p ∉ X := by
  refine ⟨fun h hp => lt_irrefl p (h le_rfl hp), fun hp q h hq => ?_⟩
  exact lt_of_le_of_ne h fun e => hp (e ▸ hq)

@[simp]
theorem uncovered_ofSubset (X : Set P) : (ofSubset X).uncovered = X :=
  Set.ext fun _ => by rw [mem_uncovered_iff, strict_mem_ofSubset_iff, not_not]

theorem ofSubset_le_ofSubset_iff {X Y : Set P} : ofSubset X ≤ ofSubset Y ↔ Y ⊆ X := by
  refine ⟨fun h q hq => ?_, fun h => ofSubset_anti h⟩
  by_contra hqX
  have := h q (strict_mem_ofSubset_iff.2 hqX)
  exact strict_mem_ofSubset_iff.1 this hq

variable (P) in
/-- On a well-founded poset, Grothendieck topologies are the same as subsets, and larger subsets
give smaller topologies. -/
def orderIsoSubset [WellFoundedLT P] : (Set P)ᵒᵈ ≃o GrothendieckTopology P where
  toFun X := ofSubset (OrderDual.ofDual X)
  invFun J := OrderDual.toDual J.uncovered
  left_inv X := by simp
  right_inv J := (eq_ofSubset_uncovered J).symm
  map_rel_iff' := ofSubset_le_ofSubset_iff

/-- A finite poset with `n` elements has `2 ^ n` Grothendieck topologies. -/
theorem card_eq_two_pow [Fintype P] [Fintype (GrothendieckTopology P)] :
    Fintype.card (GrothendieckTopology P) = 2 ^ Fintype.card P := by
  have : WellFoundedLT P := Finite.wellFounded_of_trans_of_irrefl (· < ·)
  rw [← Fintype.card_set]
  exact Fintype.card_congr (orderIsoSubset P).symm.toEquiv

end GrothendieckTopology

end PartialOrder

end CategoryTheory
