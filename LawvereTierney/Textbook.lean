/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import LawvereTierney.Basic
public import Mathlib.CategoryTheory.Topos.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Lawvere–Tierney topologies as endomorphisms of `Ω`

`LawvereTierney.Basic` defines a Lawvere–Tierney topology by its components on sieves. Here the
definition is stated the way it appears in textbooks: a morphism `j : Ω ⟶ Ω` in the category of
presheaves such that `truth ≫ j = truth`, `j ≫ j = j` and `(j ⊗ j) ≫ ∧ = ∧ ≫ j`, where `∧` is the
internal meet `Ω ⊗ Ω ⟶ Ω`. The two definitions are equivalent.

## Main definitions

* `Presheaf.sieveInf`: the internal meet on the presheaf of sieves.
* `LawvereTierneyTopology.hom`: the morphism `Ω ⟶ Ω` underlying a Lawvere–Tierney topology.
* `TextbookTopology C`: the three equations above, as a structure.
* `LawvereTierneyTopology.equivTextbookTopology`: the equivalence of the two definitions.

## Main results

* `Presheaf.sieveInf_eq_χ`: `sieveInf` is the characteristic map of `⟨truth, truth⟩`, which is
  how `∧` is defined in an arbitrary topos.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

variable (C : Type u) [Category.{v} C]

namespace Presheaf

/-- The internal meet on the presheaf of sieves: at `X` it sends a pair of sieves to their
intersection. -/
def sieveInf : Functor.sieves C ⊗ Functor.sieves C ⟶ Functor.sieves C where
  app X := ↾fun p : Sieve X.unop × Sieve X.unop => (p.1 ⊓ p.2 : Sieve X.unop)
  naturality X Y f := by
    ext p
    exact (Sieve.pullback_inter (f := f.unop) p.1 p.2).symm

@[simp]
theorem sieveInf_app_apply {X : Cᵒᵖ} (S T : Sieve X.unop) :
    (sieveInf C).app X (S, T) = S ⊓ T :=
  rfl

variable {C}

theorem mem_inf_iff_pullback_eq_top {X : C} (S T : Sieve X) {Y : C} (f : Y ⟶ X) :
    (S ⊓ T) f ↔ ∃ _ : PUnit, (S.pullback f, T.pullback f) = (⊤, ⊤) := by
  simp [Prod.ext_iff, ← Sieve.mem_iff_pullback_eq_top]

variable (C) in
/-- `sieveInf` is the characteristic map of `⟨truth, truth⟩ : 1 ⟶ Ω ⊗ Ω`. -/
theorem sieveInf_eq_χ : sieveInf C = χ (lift (truth C) (truth C)) := by
  ext X ⟨S, T⟩
  exact Sieve.ext fun Y f => mem_inf_iff_pullback_eq_top S T f

end Presheaf

namespace LawvereTierneyTopology

variable {C}

/-- The morphism `Ω ⟶ Ω` underlying a Lawvere–Tierney topology. -/
def hom (L : LawvereTierneyTopology C) : Functor.sieves C ⟶ Functor.sieves C where
  app X := ↾fun S : Sieve X.unop => (L.j X.unop S : Sieve X.unop)
  naturality X Y f := by
    ext S
    exact (L.natural f.unop S).symm

@[simp]
theorem hom_app_apply (L : LawvereTierneyTopology C) {X : Cᵒᵖ} (S : Sieve X.unop) :
    L.hom.app X S = L.j X.unop S :=
  rfl

end LawvereTierneyTopology

/-- A Lawvere–Tierney topology in the language of the subobject classifier. -/
@[ext]
structure TextbookTopology where
  /-- The endomorphism `j : Ω ⟶ Ω`. -/
  j : Functor.sieves C ⟶ Functor.sieves C
  /-- `true ≫ j = true`. -/
  truth_comp : Presheaf.truth C ≫ j = Presheaf.truth C
  /-- `j ≫ j = j`. -/
  comp_self : j ≫ j = j
  /-- `(j × j) ≫ ∧ = ∧ ≫ j`. -/
  tensor_comp : (j ⊗ₘ j) ≫ Presheaf.sieveInf C = Presheaf.sieveInf C ≫ j

namespace LawvereTierneyTopology

variable {C}

/-- The three equations hold for `L.hom`. -/
def toTextbook (L : LawvereTierneyTopology C) : TextbookTopology C where
  j := L.hom
  truth_comp := by
    ext X ⟨⟩
    exact L.top X.unop
  comp_self := by
    ext X S
    exact L.idem X.unop S
  tensor_comp := by
    ext X ⟨S, T⟩
    exact (L.inf X.unop S T).symm

/-- Reading the three equations sieve by sieve. -/
def ofTextbook (T : TextbookTopology C) : LawvereTierneyTopology C where
  j X S := T.j.app (Opposite.op X) S
  natural f S := (NatTrans.naturality_apply T.j f.op S).symm
  top X := types_congr_hom (NatTrans.congr_app T.truth_comp (Opposite.op X)) PUnit.unit
  idem X S := types_congr_hom (NatTrans.congr_app T.comp_self (Opposite.op X)) S
  inf X S U := (types_congr_hom (NatTrans.congr_app T.tensor_comp (Opposite.op X)) (S, U)).symm

@[simp]
theorem ofTextbook_toTextbook (L : LawvereTierneyTopology C) : ofTextbook L.toTextbook = L :=
  ext fun _ _ => rfl

@[simp]
theorem toTextbook_ofTextbook (T : TextbookTopology C) : (ofTextbook T).toTextbook = T :=
  TextbookTopology.ext (by ext X S; rfl)

variable (C) in
/-- Lawvere–Tierney topologies, sieve by sieve or as endomorphisms of `Ω`. -/
def equivTextbookTopology : LawvereTierneyTopology C ≃ TextbookTopology C where
  toFun := toTextbook
  invFun := ofTextbook
  left_inv := ofTextbook_toTextbook
  right_inv := toTextbook_ofTextbook

end LawvereTierneyTopology

end CategoryTheory
