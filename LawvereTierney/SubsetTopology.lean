/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import LawvereTierney.Poset
public import Mathlib.Data.Fintype.Powerset

/-!
# Subset topologies on a poset

For a subset `X` of a preorder `P` there is a Grothendieck topology `ofSubset X` in which a sieve
on `p` is covering when it contains every element of `X` below `p`. Larger subsets give coarser
topologies, `⊤ ⊆ P` giving the trivial topology and `∅` the topology in which every sieve covers.

If `P` is a well-founded poset, every Grothendieck topology arises this way from exactly one
subset: the points `p` for which the sieve of strict predecessors of `p` is not covering. The proof
that such a topology contains `ofSubset X` is by well-founded induction, using transitivity.
In particular a finite poset with `n` elements has exactly `2 ^ n` Grothendieck topologies.

Well-foundedness is also necessary. If `P` has a nonempty subset `X` without minimal elements, the
topology `meeting X`, in which a sieve covers `p` when it meets `X` below every `q ≤ p` that lies
above a point of `X`, is not a subset topology: all strict predecessor sieves cover for it, which
would force the subset to be empty, but the empty sieve does not cover a point of `X`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.ofSubset`: the topology of a subset.
* `CategoryTheory.GrothendieckTopology.uncovered`: the subset recovered from a topology.
* `CategoryTheory.GrothendieckTopology.orderIsoSubset`: topologies on a well-founded poset are
  subsets, with the order reversed.
* `CategoryTheory.GrothendieckTopology.meeting`: a topology that is not a subset topology when the
  subset has no minimal element.

## Main results

* `CategoryTheory.GrothendieckTopology.eq_ofSubset_uncovered`: on a well-founded preorder every
  topology is a subset topology.
* `CategoryTheory.GrothendieckTopology.wellFoundedLT_iff_forall_eq_ofSubset`: a poset is
  well-founded exactly when all of its topologies are subset topologies.
* `CategoryTheory.GrothendieckTopology.card_eq_two_pow`: the number of topologies on a finite
  poset.

## References

* [A. J. Lindenhovius, *Grothendieck topologies on posets*][Lindenhovius14]. There the subset
  topologies are introduced (Proposition 2.8) and shown to be all topologies exactly when the
  poset is Artinian (Theorem 2.12), that is, when every nonempty subset has a minimal element.
  This is `WellFoundedLT` here.
* [J. Hemelaer, *Grothendieck topologies on posets*][Hemelaer18], for posets that are not
  Artinian.
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

/-- The topology in which a sieve on `p` covers when, below every `q ≤ p` that lies above a point of
`X`, it contains a point of `X`. -/
def meeting (X : Set P) : GrothendieckTopology P where
  sieves p := {S | ∀ ⦃q⦄ (h : q ≤ p), (∃ x ∈ X, x ≤ q) →
    ∃ x ∈ X, ∃ hx : x ≤ q, S (homOfLE (hx.trans h))}
  top_mem' _ := fun _ _ ⟨x, hx, hxq⟩ => ⟨x, hx, hxq, True.intro⟩
  pullback_stable' _ _ _ f hS := fun _ h hq => hS (h.trans (leOfHom f)) hq
  transitive' _ _ hS _ hR := fun q h hq => by
    obtain ⟨x, hx, hxq, hxS⟩ := hS h hq
    obtain ⟨y, hy, hyx, hyR⟩ := hR hxS le_rfl ⟨x, hx, le_rfl⟩
    exact ⟨y, hy, hyx.trans hxq, hyR⟩

/-- If every point of `X` has a smaller point in `X`, the strict predecessors of any `p` cover
for `meeting X`. -/
theorem strict_mem_meeting {X : Set P} (hX : ∀ x ∈ X, ∃ y ∈ X, y < x) (p : P) :
    Sieve.strict p ∈ meeting X p := by
  rintro q h ⟨x, hx, hxq⟩
  obtain ⟨y, hy, hyx⟩ := hX x hx
  exact ⟨y, hy, (hyx.trans_le hxq).le, hyx.trans_le (hxq.trans h)⟩

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

/-- If `X` is nonempty and has no minimal element, `meeting X` is not a subset topology. -/
theorem meeting_ne_ofSubset {X : Set P} (hne : X.Nonempty) (hX : ∀ x ∈ X, ∃ y ∈ X, y < x)
    (Y : Set P) : meeting X ≠ ofSubset Y := by
  intro h
  have hY : Y = ∅ := Set.eq_empty_of_forall_notMem fun p hp => by
    have := strict_mem_meeting hX p
    rw [h, strict_mem_ofSubset_iff] at this
    exact this hp
  obtain ⟨p, hp⟩ := hne
  have hbot : (⊥ : Sieve p) ∈ meeting X p := by
    rw [h, hY]
    exact fun q _ hq => hq.elim
  obtain ⟨x, -, hx, hxbot⟩ := hbot le_rfl ⟨p, hp, le_rfl⟩
  exact hxbot

/-- Every Grothendieck topology on a poset is a subset topology exactly when the poset is
well-founded. -/
theorem wellFoundedLT_iff_forall_eq_ofSubset :
    WellFoundedLT P ↔ ∀ J : GrothendieckTopology P, ∃ X, J = ofSubset X := by
  refine ⟨fun _ J => ⟨_, eq_ofSubset_uncovered J⟩, fun h => ?_⟩
  by_contra hwf
  rw [WellFoundedLT, WellFounded.wellFounded_iff_has_min] at hwf
  push Not at hwf
  obtain ⟨X, hne, hX⟩ := hwf
  obtain ⟨Y, hY⟩ := h (meeting X)
  exact meeting_ne_ofSubset hne hX Y hY

/-- The integers carry a Grothendieck topology that is not a subset topology. -/
theorem exists_forall_ne_ofSubset_int : ∃ J : GrothendieckTopology ℤ, ∀ X, J ≠ ofSubset X :=
  ⟨meeting Set.univ,
    meeting_ne_ofSubset Set.univ_nonempty fun x _ => ⟨x - 1, Set.mem_univ _, by omega⟩⟩

/-- A finite poset with `n` elements has `2 ^ n` Grothendieck topologies. -/
theorem card_eq_two_pow [Fintype P] [Fintype (GrothendieckTopology P)] :
    Fintype.card (GrothendieckTopology P) = 2 ^ Fintype.card P := by
  have : WellFoundedLT P := Finite.wellFounded_of_trans_of_irrefl (· < ·)
  rw [← Fintype.card_set]
  exact Fintype.card_congr (orderIsoSubset P).symm.toEquiv

end GrothendieckTopology

end PartialOrder

end CategoryTheory
