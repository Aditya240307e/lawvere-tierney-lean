/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/
import LawvereTierney.Closure
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Localization

/-!
# Sheaves for a Lawvere–Tierney topology

A presheaf is a sheaf for the Grothendieck topology of `j` exactly when it sees dense monomorphisms
as isomorphisms: every map from a dense subpresheaf `A ⊆ F` into `P` extends uniquely to `F`.
This is the description of `j`-sheaves used in the topos-theoretic definition, where a sheaf
is an object orthogonal to the dense monomorphisms.

Throughout, `C` is a small category and presheaves are valued in `Type u`.

## Main definitions

* `CategoryTheory.Sieve.toSubfunctor`: a sieve as a subpresheaf of a representable presheaf.

## Main results

* `LawvereTierneyTopology.isSheaf_iff_existsUnique_extension`: `P` is a sheaf for `j` if and only
  if it has unique extensions along dense monomorphisms.
* `LawvereTierneyTopology.Ω_obj_eq_fixedSieves`: the subobject classifier of the sheaf topos is the
  presheaf of sieves fixed by `j`.

## References

* [S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92], Chapter V.
-/

universe u

namespace CategoryTheory

open Opposite

namespace Sieve

variable {C : Type u} [SmallCategory C] {X : C}

/-- A sieve, as a subpresheaf of the representable presheaf at `X`. -/
def toSubfunctor (S : Sieve X) : Subfunctor (yoneda.obj X) where
  obj _ := {g | S g}
  map f _ hg := S.downward_closed hg f.unop

end Sieve

namespace LawvereTierneyTopology

variable {C : Type u} [SmallCategory C] (L : LawvereTierneyTopology C)

/-- A sheaf extends uniquely along any dense subpresheaf. -/
theorem existsUnique_extension_of_isSheaf {P F : Cᵒᵖ ⥤ Type u}
    (hP : Presieve.IsSheaf L.toGrothendieckTopology P) {A : Subfunctor F} (hA : L.IsDense A)
    (φ : A.toFunctor ⟶ P) : ∃! ψ : F ⟶ P, A.ι ≫ ψ = φ := by
  have : Presheaf.IsLocallySurjective L.toGrothendieckTopology A.ι :=
    (L.isDense_iff_isLocallySurjective).1 hA
  have : Presheaf.IsLocallyInjective L.toGrothendieckTopology A.ι :=
    Presheaf.isLocallyInjective_of_injective _ _ fun _ => Subtype.val_injective
  have hW : L.toGrothendieckTopology.W A.ι :=
    GrothendieckTopology.W_of_isLocallyBijective _ A.ι
  exact (hW P ((isSheaf_iff_isSheaf_of_type _ P).2 hP)).existsUnique φ

/-- A presheaf with unique extensions along dense subpresheaves is a sheaf. -/
theorem isSheaf_of_existsUnique_extension {P : Cᵒᵖ ⥤ Type u}
    (h : ∀ (F : Cᵒᵖ ⥤ Type u) (A : Subfunctor F), L.IsDense A →
      ∀ φ : A.toFunctor ⟶ P, ∃! ψ : F ⟶ P, A.ι ≫ ψ = φ) :
    Presieve.IsSheaf L.toGrothendieckTopology P := by
  intro X S hS
  rw [Presieve.isSheafFor_iff_yonedaSheafCondition]
  intro f
  refine h (yoneda.obj X) S.toSubfunctor ?_ f
  rw [isDense_iff]
  intro Y g
  have : S.toSubfunctor.sieveOfSection g = S.pullback g := Sieve.ext fun Z h => Iff.rfl
  rw [this, ← L.natural, (L.mem_toGrothendieckTopology S).1 hS, Sieve.pullback_top]

/-- A presheaf is a sheaf for the topology of `j` exactly when it has unique extensions along
dense monomorphisms. -/
theorem isSheaf_iff_existsUnique_extension (P : Cᵒᵖ ⥤ Type u) :
    Presieve.IsSheaf L.toGrothendieckTopology P ↔
      ∀ (F : Cᵒᵖ ⥤ Type u) (A : Subfunctor F), L.IsDense A →
        ∀ φ : A.toFunctor ⟶ P, ∃! ψ : F ⟶ P, A.ι ≫ ψ = φ :=
  ⟨fun hP _ _ hA φ => L.existsUnique_extension_of_isSheaf hP hA φ,
    L.isSheaf_of_existsUnique_extension⟩

/-- The classifier of the sheaf topos is the presheaf of sieves fixed by `j`. -/
theorem Ω_obj_eq_fixedSieves :
    (Sheaf.Ω L.toGrothendieckTopology).obj = L.fixedSieves.toFunctor := by
  rw [fixedSieves_eq_closedSieves]
  rfl

end LawvereTierneyTopology

end CategoryTheory
