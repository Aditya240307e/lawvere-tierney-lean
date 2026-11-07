/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Order.Nucleus
import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Principal

/-!
# Grothendieck topologies on a preorder

Let `P` be a preorder, viewed as a category. A sieve on `p` is the same thing as a lower set of `P`
contained in `Iic p`, and the lower sets of `P` are the subobjects of the terminal presheaf. A
Grothendieck topology `J` on `P` therefore acts on lower sets: `U` is sent to the set of points `p`
for which `U ∩ Iic p` is a covering sieve.

## Main definitions

* `CategoryTheory.Sieve.ofLowerSet`, `CategoryTheory.Sieve.toLowerSet`: the passage between sieves
  and lower sets.
* `CategoryTheory.GrothendieckTopology.toNucleus`: the nucleus on `LowerSet P` of a topology.
* `CategoryTheory.GrothendieckTopology.ofNucleus`: the topology of a nucleus.
* `CategoryTheory.GrothendieckTopology.orderIsoNucleus`: these are inverse order isomorphisms.

## Main results

* `CategoryTheory.GrothendieckTopology.toNucleus_ofNucleus`,
  `CategoryTheory.GrothendieckTopology.ofNucleus_toNucleus`: the two composites are the identity.

In other words every subtopos of the presheaf topos of a preorder is determined by the nucleus it
induces on the frame of subterminal objects.

## References

* [S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92], Chapter III.
* A. J. Lindenhovius, *Grothendieck topologies on posets*, arXiv:1405.4408, whose appendix compares
  such topologies with nuclei and sublocales of the frame of down-sets.
-/

universe u

namespace CategoryTheory

open CategoryTheory

variable {P : Type u} [Preorder P]

namespace Sieve

/-- The sieve on `p` consisting of the arrows whose source lies in the lower set `U`. -/
def ofLowerSet (U : LowerSet P) (p : P) : Sieve p where
  arrows q _ := q ∈ U
  downward_closed := fun hf g => U.lower (leOfHom g) hf

/-- The lower set of sources of the arrows of a sieve on `p`. -/
def toLowerSet {p : P} (S : Sieve p) : LowerSet P where
  carrier := {q | ∃ h : q ≤ p, S (homOfLE h)}
  lower' := by
    rintro q r hrq ⟨h, hq⟩
    exact ⟨hrq.trans h, S.downward_closed hq (homOfLE hrq)⟩

theorem mem_toLowerSet_iff {p q : P} {S : Sieve p} :
    q ∈ S.toLowerSet ↔ ∃ h : q ≤ p, S (homOfLE h) :=
  Iff.rfl

theorem ofLowerSet_apply {U : LowerSet P} {p q : P} (f : q ⟶ p) : ofLowerSet U p f ↔ q ∈ U :=
  Iff.rfl

@[simp]
theorem ofLowerSet_toLowerSet {p : P} (S : Sieve p) : ofLowerSet S.toLowerSet p = S :=
  Sieve.ext fun _ f => ⟨fun ⟨_, h⟩ => h, fun h => ⟨leOfHom f, h⟩⟩

theorem toLowerSet_ofLowerSet (U : LowerSet P) (p : P) :
    (ofLowerSet U p).toLowerSet = U ⊓ LowerSet.Iic p :=
  LowerSet.ext <| Set.ext fun _ => ⟨fun ⟨h, hq⟩ => ⟨hq, h⟩, fun ⟨hq, h⟩ => ⟨h, hq⟩⟩

theorem ofLowerSet_pullback (U : LowerSet P) {p q : P} (f : q ⟶ p) :
    (ofLowerSet U p).pullback f = ofLowerSet U q :=
  rfl

theorem toLowerSet_pullback {p q : P} (S : Sieve p) (f : q ⟶ p) :
    (S.pullback f).toLowerSet = S.toLowerSet ⊓ LowerSet.Iic q := by
  refine LowerSet.ext (Set.ext fun r => ⟨fun ⟨h, hr⟩ => ?_, fun ⟨⟨h, hr⟩, h'⟩ => ?_⟩)
  · exact ⟨⟨h.trans (leOfHom f), hr⟩, h⟩
  · exact ⟨h', hr⟩

end Sieve

namespace GrothendieckTopology

section Nucleus

variable (J : GrothendieckTopology P)

/-- The points covered by a lower set: `p` such that `U ∩ Iic p` is a covering sieve. -/
def closure (U : LowerSet P) : LowerSet P where
  carrier := {p | Sieve.ofLowerSet U p ∈ J p}
  lower' := fun _ _ hqp hp => by
    simpa [Sieve.ofLowerSet_pullback] using J.pullback_stable (homOfLE hqp) hp

theorem mem_closure_iff {U : LowerSet P} {p : P} : p ∈ J.closure U ↔ Sieve.ofLowerSet U p ∈ J p :=
  Iff.rfl

/-- The topology `J` as a nucleus on the lower sets of `P`. -/
def toNucleus : Nucleus (LowerSet P) where
  toFun := J.closure
  map_inf' U V := LowerSet.ext <| Set.ext fun p => by
    change Sieve.ofLowerSet (U ⊓ V) p ∈ J p ↔
      Sieve.ofLowerSet U p ∈ J p ∧ Sieve.ofLowerSet V p ∈ J p
    rw [← J.intersection_covering_iff]
    rfl
  idempotent' U := fun p hp => by
    refine J.transitive hp (Sieve.ofLowerSet U p) fun q f hf => ?_
    rw [Sieve.ofLowerSet_pullback]
    exact hf
  le_apply' U := fun p hp => by
    have : Sieve.ofLowerSet U p = ⊤ :=
      Sieve.ext fun _ f => iff_of_true (U.lower (leOfHom f) hp) True.intro
    change Sieve.ofLowerSet U p ∈ J p
    rw [this]
    exact J.top_mem p

theorem toNucleus_apply (U : LowerSet P) : J.toNucleus U = J.closure U :=
  rfl

end Nucleus

/-- The topology of a nucleus on the lower sets of `P`: a sieve on `p` covers when `p` lies in the
nucleus of its lower set. -/
def ofNucleus (n : Nucleus (LowerSet P)) : GrothendieckTopology P where
  sieves p := {S | p ∈ n S.toLowerSet}
  top_mem' p := n.le_apply (show p ∈ (⊤ : Sieve p).toLowerSet from ⟨le_rfl, True.intro⟩)
  pullback_stable' p q S f hS := by
    change q ∈ n (S.pullback f).toLowerSet
    rw [Sieve.toLowerSet_pullback, n.map_inf]
    exact ⟨(n S.toLowerSet).lower (leOfHom f) hS, n.le_apply (show q ∈ LowerSet.Iic q from le_rfl)⟩
  transitive' p S hS R hR := by
    have h : S.toLowerSet ≤ n R.toLowerSet := fun q ⟨h, hq⟩ => by
      have := hR hq
      change q ∈ n (R.pullback (homOfLE h)).toLowerSet at this
      rw [Sieve.toLowerSet_pullback, n.map_inf] at this
      exact this.1
    exact (n.idempotent R.toLowerSet).le (n.monotone h hS)

theorem mem_ofNucleus_iff {n : Nucleus (LowerSet P)} {p : P} {S : Sieve p} :
    S ∈ ofNucleus n p ↔ p ∈ n S.toLowerSet :=
  Iff.rfl

@[simp]
theorem toNucleus_ofNucleus (n : Nucleus (LowerSet P)) : (ofNucleus n).toNucleus = n := by
  refine DFunLike.ext _ _ fun U => LowerSet.ext (Set.ext fun p => ?_)
  change Sieve.ofLowerSet U p ∈ ofNucleus n p ↔ p ∈ n U
  rw [mem_ofNucleus_iff, Sieve.toLowerSet_ofLowerSet, n.map_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, n.le_apply (show p ∈ LowerSet.Iic p from le_rfl)⟩⟩

@[simp]
theorem ofNucleus_toNucleus (J : GrothendieckTopology P) : ofNucleus J.toNucleus = J := by
  refine GrothendieckTopology.ext (funext fun p => Set.ext fun S => ?_)
  change p ∈ J.toNucleus S.toLowerSet ↔ S ∈ J p
  rw [toNucleus_apply, mem_closure_iff, Sieve.ofLowerSet_toLowerSet]

theorem toNucleus_le_toNucleus_iff {J K : GrothendieckTopology P} :
    J.toNucleus ≤ K.toNucleus ↔ J ≤ K := by
  refine ⟨fun h p S hS => ?_, fun h U p hp => h p hp⟩
  have hp : p ∈ J.toNucleus S.toLowerSet := by
    change Sieve.ofLowerSet S.toLowerSet p ∈ J p
    rwa [Sieve.ofLowerSet_toLowerSet]
  have := h S.toLowerSet hp
  change Sieve.ofLowerSet S.toLowerSet p ∈ K p at this
  rwa [Sieve.ofLowerSet_toLowerSet] at this

variable (P) in
/-- Grothendieck topologies on a preorder are the same as nuclei on its lower sets. -/
def orderIsoNucleus : GrothendieckTopology P ≃o Nucleus (LowerSet P) where
  toFun := toNucleus
  invFun := ofNucleus
  left_inv := ofNucleus_toNucleus
  right_inv := toNucleus_ofNucleus
  map_rel_iff' := toNucleus_le_toNucleus_iff

end GrothendieckTopology

end CategoryTheory
