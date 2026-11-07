/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.Order.Nucleus

/-!
# Lawvere–Tierney topologies on a presheaf topos

The subobject classifier of the presheaf topos `Cᵒᵖ ⥤ Type _` is the presheaf of sieves, so a
morphism `j : Ω ⟶ Ω` is a family of maps `j X : Sieve X → Sieve X` that commute with pullback.
A Lawvere–Tierney topology is such a `j` with `true ≫ j = true`, `j ≫ j = j` and
`∧ ≫ j = (j × j) ≫ ∧`. Sieve by sieve these read `j ⊤ = ⊤`, `j (j S) = j S` and
`j (S ⊓ T) = j S ⊓ j T`, and this is the definition used in this file. The version with `Ω`
and `∧` as honest morphisms of presheaves is in `LawvereTierney.Textbook`.

The point of this file is that the data is the same as a Grothendieck topology on `C`: a covering
sieve is one that `j` sends to `⊤`, and `j` is recovered as the closure of a sieve.

## Main definitions

* `LawvereTierneyTopology C`: a Lawvere–Tierney topology on `Cᵒᵖ ⥤ Type _`.
* `LawvereTierneyTopology.nucleus`: at each object, `j` is a nucleus on the frame of sieves.
* `LawvereTierneyTopology.toGrothendieckTopology`, `LawvereTierneyTopology.ofGrothendieckTopology`:
  the two directions of the correspondence.
* `LawvereTierneyTopology.orderIsoGrothendieckTopology`: the correspondence as an order isomorphism.

## Main results

* `LawvereTierneyTopology.le_j`: `S ≤ j S` is a consequence of naturality and `j ⊤ = ⊤`.
* `LawvereTierneyTopology.monotone`: `j` is monotone.
* `LawvereTierneyTopology.ofMonotone`: conversely, monotonicity already implies that `j` preserves
  binary meets, so it could replace that axiom in the definition.

## References

* [S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92], Chapter V.
* <https://ncatlab.org/nlab/show/Lawvere-Tierney+topology>
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A Lawvere–Tierney topology on `Cᵒᵖ ⥤ Type _`, written sieve by sieve. -/
structure LawvereTierneyTopology where
  /-- The local operator at `X`. -/
  j : ∀ X : C, Sieve X → Sieve X
  /-- `j` is a morphism of presheaves. -/
  natural : ∀ {X Y : C} (f : Y ⟶ X) (S : Sieve X), (j X S).pullback f = j Y (S.pullback f)
  /-- `true ≫ j = true`. -/
  top : ∀ X : C, j X ⊤ = ⊤
  /-- `j ≫ j = j`. -/
  idem : ∀ (X : C) (S : Sieve X), j X (j X S) = j X S
  /-- `∧ ≫ j = (j × j) ≫ ∧`. -/
  inf : ∀ (X : C) (S T : Sieve X), j X (S ⊓ T) = j X S ⊓ j X T

namespace LawvereTierneyTopology

variable {C}

@[ext]
theorem ext {L M : LawvereTierneyTopology C} (h : ∀ X S, L.j X S = M.j X S) : L = M := by
  cases L
  cases M
  have : _ = _ := funext fun X => funext fun S => h X S
  subst this
  rfl

/-- The axiom `j (S ⊓ T) = j S ⊓ j T` follows from monotonicity of `j`, together with the other
three axioms. -/
def ofMonotone (j : ∀ X : C, Sieve X → Sieve X)
    (natural : ∀ {X Y : C} (f : Y ⟶ X) (S : Sieve X), (j X S).pullback f = j Y (S.pullback f))
    (top : ∀ X : C, j X ⊤ = ⊤) (idem : ∀ (X : C) (S : Sieve X), j X (j X S) = j X S)
    (mono : ∀ X : C, Monotone (j X)) : LawvereTierneyTopology C where
  j := j
  natural := natural
  top := top
  idem := idem
  inf X S T := by
    have key : ∀ {Y : C} (S' T' : Sieve Y), j Y S' = ⊤ → j Y T' = ⊤ → j Y (S' ⊓ T') = ⊤ := by
      intro Y S' T' hS hT
      have h : S' ≤ j Y (S' ⊓ T') := by
        intro Z g hg
        rw [Sieve.mem_iff_pullback_eq_top, natural, Sieve.pullback_inter,
          Sieve.pullback_eq_top_of_mem S' hg, top_inf_eq, ← natural, hT, Sieve.pullback_top]
      refine top_le_iff.1 ?_
      calc (⊤ : Sieve Y) = j Y S' := hS.symm
        _ ≤ j Y (j Y (S' ⊓ T')) := mono Y h
        _ = j Y (S' ⊓ T') := idem Y _
    refine le_antisymm (le_inf (mono X inf_le_left) (mono X inf_le_right)) ?_
    intro Y f hf
    rw [Sieve.mem_iff_pullback_eq_top, natural, Sieve.pullback_inter]
    refine key _ _ ?_ ?_
    · rw [← natural, ← Sieve.mem_iff_pullback_eq_top]
      exact hf.1
    · rw [← natural, ← Sieve.mem_iff_pullback_eq_top]
      exact hf.2

section Basic

variable (L : LawvereTierneyTopology C)

theorem monotone {X : C} : Monotone (L.j X) := fun S T h => by
  have := L.inf X S T
  rw [inf_eq_left.2 h] at this
  exact inf_eq_left.1 this.symm

/-- Naturality and `j ⊤ = ⊤` force `j` to be inflationary. -/
theorem le_j {X : C} (S : Sieve X) : S ≤ L.j X S := by
  intro Y f hf
  rw [Sieve.mem_iff_pullback_eq_top, L.natural, Sieve.pullback_eq_top_of_mem S hf, L.top]

/-- At each object, `j` is a nucleus on the frame of sieves. -/
def nucleus (X : C) : Nucleus (Sieve X) where
  toFun := L.j X
  map_inf' := L.inf X
  idempotent' S := (L.idem X S).le
  le_apply' S := L.le_j S

/-- The Grothendieck topology of `L`: a sieve covers exactly when `j` sends it to `⊤`. -/
def toGrothendieckTopology : GrothendieckTopology C :=
  topologyOfClosureOperator (fun X => (L.nucleus X).toClosureOperator)
    (fun ⦃_ _⦄ f S => (L.natural f S).symm)

theorem mem_toGrothendieckTopology {X : C} (S : Sieve X) :
    S ∈ L.toGrothendieckTopology X ↔ L.j X S = ⊤ :=
  Iff.rfl

end Basic

/-- The Lawvere–Tierney topology of a Grothendieck topology: `j` is the closure of a sieve. -/
def ofGrothendieckTopology (J : GrothendieckTopology C) : LawvereTierneyTopology C where
  j _ := J.close
  natural f S := (J.pullback_close f S).symm
  top _ := eq_top_iff.2 (J.le_close _)
  idem _ S := J.close_close S
  inf _ S T := Sieve.ext fun Y f => by
    change J.Covers (S ⊓ T) f ↔ J.Covers S f ∧ J.Covers T f
    rw [J.covers_iff, J.covers_iff, J.covers_iff, Sieve.pullback_inter,
      J.intersection_covering_iff]

theorem ofGrothendieckTopology_j (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    (ofGrothendieckTopology J).j X S = J.close S :=
  rfl

@[simp]
theorem toGrothendieckTopology_ofGrothendieckTopology (J : GrothendieckTopology C) :
    (ofGrothendieckTopology J).toGrothendieckTopology = J :=
  topologyOfClosureOperator_self J

@[simp]
theorem ofGrothendieckTopology_toGrothendieckTopology (L : LawvereTierneyTopology C) :
    ofGrothendieckTopology L.toGrothendieckTopology = L :=
  ext fun X S => topologyOfClosureOperator_close _ _ X S

theorem close_toGrothendieckTopology (L : LawvereTierneyTopology C) {X : C} (S : Sieve X) :
    L.toGrothendieckTopology.close S = L.j X S :=
  congrArg (fun M : LawvereTierneyTopology C => M.j X S)
    (ofGrothendieckTopology_toGrothendieckTopology L)

variable (C) in
/-- Grothendieck topologies on `C` correspond to Lawvere–Tierney topologies on `Cᵒᵖ ⥤ Type _`. -/
def equivGrothendieckTopology : GrothendieckTopology C ≃ LawvereTierneyTopology C where
  toFun := ofGrothendieckTopology
  invFun := toGrothendieckTopology
  left_inv := toGrothendieckTopology_ofGrothendieckTopology
  right_inv := ofGrothendieckTopology_toGrothendieckTopology

/-! ### The order -/

/-- `L ≤ M` when `M` closes up every sieve at least as much as `L` does. -/
instance : PartialOrder (LawvereTierneyTopology C) :=
  PartialOrder.lift (fun L X => L.j X) fun _ _ h => ext fun X S => congr_fun (congr_fun h X) S

theorem le_def {L M : LawvereTierneyTopology C} :
    L ≤ M ↔ ∀ (X : C) (S : Sieve X), L.j X S ≤ M.j X S :=
  Iff.rfl

theorem ofGrothendieckTopology_le_iff {J K : GrothendieckTopology C} :
    ofGrothendieckTopology J ≤ ofGrothendieckTopology K ↔ J ≤ K := by
  refine ⟨fun h X S hS => ?_, fun h X S Y f hf => ?_⟩
  · rw [← K.close_eq_top_iff_mem, eq_top_iff]
    have h' : J.close S ≤ K.close S := h X S
    rwa [(J.close_eq_top_iff_mem S).2 hS] at h'
  · exact h _ hf

variable (C) in
/-- The correspondence of `equivGrothendieckTopology` respects the order. -/
def orderIsoGrothendieckTopology : GrothendieckTopology C ≃o LawvereTierneyTopology C where
  toEquiv := equivGrothendieckTopology C
  map_rel_iff' := ofGrothendieckTopology_le_iff

/-! ### Two extreme cases -/

/-- The trivial topology, whose only covering sieves are the maximal ones, has `j = id`. -/
theorem ofGrothendieckTopology_bot_j {X : C} (S : Sieve X) :
    (ofGrothendieckTopology (⊥ : GrothendieckTopology C)).j X S = S := by
  refine Sieve.ext fun Y f => ?_
  change (⊥ : GrothendieckTopology C).Covers S f ↔ S f
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.bot_covering,
    ← Sieve.mem_iff_pullback_eq_top]

/-- The discrete topology, in which every sieve covers, has `j = ⊤`. -/
theorem ofGrothendieckTopology_top_j {X : C} (S : Sieve X) :
    (ofGrothendieckTopology (⊤ : GrothendieckTopology C)).j X S = ⊤ :=
  Sieve.ext fun _ _ => iff_of_true
    ((GrothendieckTopology.covers_iff _ _ _).2 GrothendieckTopology.top_covering) trivial

end LawvereTierneyTopology

end CategoryTheory
