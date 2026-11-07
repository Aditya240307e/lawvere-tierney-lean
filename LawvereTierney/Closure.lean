/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/
import LawvereTierney.Textbook
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Closure of subpresheaves

A Lawvere–Tierney topology `j` acts on subobjects: the closure of `A ⊆ F` is the subobject whose
characteristic map is `χ A ≫ j`. For presheaves of types this is the subpresheaf of sections of `F`
that lie in `A` on a covering sieve, which Mathlib calls `Subfunctor.sheafify` and which is used
here with the Grothendieck topology of `j`.

## Main definitions

* `LawvereTierneyTopology.closure`: the closure of a subpresheaf.
* `LawvereTierneyTopology.closureNucleus`: closure as a nucleus on the lattice of subpresheaves.
* `LawvereTierneyTopology.IsDense`: a subpresheaf whose closure is everything.
* `LawvereTierneyTopology.fixedSieves`: the sieves fixed by `j`, as a subpresheaf of `Ω`.

## Main results

* `LawvereTierneyTopology.sieveOfSection_closure`: the sieve of a section in the closure is `j`
  applied to the sieve of the section in the subpresheaf.
* `LawvereTierneyTopology.χ_closure`: `χ (closure A) = χ A ≫ j`.
* `LawvereTierneyTopology.closure_preimage`: closure commutes with pullback of subobjects.
* `LawvereTierneyTopology.isDense_iff_isLocallySurjective`: dense subpresheaves are the ones whose
  inclusion is locally surjective.
* `LawvereTierneyTopology.range_le_fixedSieves_iff`: `fixedSieves` is the equalizer of `j` and `𝟙`.

## References

* [S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92], Chapter V.
-/

universe w v u

namespace CategoryTheory

open Opposite

namespace LawvereTierneyTopology

variable {C : Type u} [Category.{v} C] (L : LawvereTierneyTopology C)

section Closure

variable {F : Cᵒᵖ ⥤ Type w} (A : Subfunctor F)

/-- The closure of a subpresheaf: the sections of `F` which lie in `A` on a covering sieve. -/
def closure : Subfunctor F := A.sheafify L.toGrothendieckTopology

variable {A}

theorem mem_closure_iff {X : Cᵒᵖ} {x : F.obj X} :
    x ∈ (L.closure A).obj X ↔ L.j X.unop (A.sieveOfSection x) = ⊤ :=
  Iff.rfl

theorem sieveOfSection_map {X Y : C} (f : Y ⟶ X) (x : F.obj (op X)) :
    A.sieveOfSection (F.map f.op x) = (A.sieveOfSection x).pullback f :=
  Sieve.ext fun Z g => by simp [Subfunctor.sieveOfSection]

theorem sieveOfSection_eq_top_iff {X : Cᵒᵖ} {x : F.obj X} :
    A.sieveOfSection x = ⊤ ↔ x ∈ A.obj X := by
  rw [← Sieve.id_mem_iff_eq_top]
  simp [Subfunctor.sieveOfSection]

theorem sieveOfSection_inf {X : Cᵒᵖ} (B : Subfunctor F) (x : F.obj X) :
    (A ⊓ B).sieveOfSection x = A.sieveOfSection x ⊓ B.sieveOfSection x :=
  rfl

/-- The sieve of a section of the closure is the closure of its sieve in `A`. -/
theorem sieveOfSection_closure {X : Cᵒᵖ} (x : F.obj X) :
    (L.closure A).sieveOfSection x = L.j X.unop (A.sieveOfSection x) := by
  refine Sieve.ext fun Y f => ?_
  change F.map f.op x ∈ (L.closure A).obj (op Y) ↔ _
  rw [mem_closure_iff, sieveOfSection_map, ← L.natural, ← Sieve.mem_iff_pullback_eq_top]

theorem le_closure : A ≤ L.closure A :=
  Subfunctor.le_sheafify _ A

theorem closure_mono {B : Subfunctor F} (h : A ≤ B) : L.closure A ≤ L.closure B := by
  intro X x hx
  rw [mem_closure_iff] at hx ⊢
  refine eq_top_iff.2 (hx ▸ L.monotone fun Y f hf => h _ hf)

@[simp]
theorem closure_closure : L.closure (L.closure A) = L.closure A := by
  refine Subfunctor.ext (funext fun X => Set.ext fun x => ?_)
  rw [mem_closure_iff, mem_closure_iff, sieveOfSection_closure, L.idem]

theorem closure_inf (B : Subfunctor F) : L.closure (A ⊓ B) = L.closure A ⊓ L.closure B := by
  refine Subfunctor.ext (funext fun X => Set.ext fun x => ?_)
  change _ ↔ _ ∧ _
  simp only [mem_closure_iff, sieveOfSection_inf, L.inf, inf_eq_top_iff]

variable (F) in
/-- Closure is a nucleus on the lattice of subpresheaves of `F`. -/
def closureNucleus : Nucleus (Subfunctor F) where
  toFun := L.closure
  map_inf' _ _ := L.closure_inf _
  idempotent' _ := (L.closure_closure).le
  le_apply' _ := L.le_closure

/-- Closure is stable under pullback of subobjects. -/
theorem closure_preimage {F' : Cᵒᵖ ⥤ Type w} (p : F' ⟶ F) :
    L.closure (A.preimage p) = (L.closure A).preimage p := by
  refine Subfunctor.ext (funext fun X => Set.ext fun x => ?_)
  have : (A.preimage p).sieveOfSection x = A.sieveOfSection (p.app X x) :=
    Sieve.ext fun Y f => by simp [Subfunctor.sieveOfSection, NatTrans.naturality_apply]
  simp [mem_closure_iff, this]

variable (A) in
/-- A subpresheaf is dense when its closure is the whole presheaf. -/
def IsDense : Prop := L.closure A = ⊤

theorem isDense_iff :
    L.IsDense A ↔ ∀ (X : Cᵒᵖ) (x : F.obj X), L.j X.unop (A.sieveOfSection x) = ⊤ := by
  simp [IsDense, Subfunctor.ext_iff, funext_iff, Set.ext_iff, mem_closure_iff]

theorem isDense_iff_isLocallySurjective :
    L.IsDense A ↔ Presheaf.IsLocallySurjective L.toGrothendieckTopology A.ι := by
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top', Subfunctor.range_ι]
  rfl

end Closure

section Classifier

variable {F : Cᵒᵖ ⥤ Type (max u v)}

theorem χ_ι_app_apply (A : Subfunctor F) {X : Cᵒᵖ} (x : F.obj X) :
    (Presheaf.χ A.ι).app X x = A.sieveOfSection x :=
  Sieve.ext fun Y f => by
    simp [Presheaf.χ, Subfunctor.sieveOfSection]
    rfl

/-- The characteristic map of the closure of `A` is `χ A` followed by `j`. -/
theorem χ_closure (A : Subfunctor F) :
    Presheaf.χ (L.closure A).ι = Presheaf.χ A.ι ≫ L.hom := by
  ext X x
  exact (χ_ι_app_apply _ x).trans ((sieveOfSection_closure L x).trans
    (congrArg (L.j X.unop) (χ_ι_app_apply A x).symm))

end Classifier

/-- The sieves fixed by `j`, as a subpresheaf of the presheaf of sieves. -/
def fixedSieves : Subfunctor (Functor.sieves C) where
  obj X := {S | L.j X.unop S = S}
  map {_ _} f _ hS := (L.natural f.unop _).symm.trans (congrArg (·.pullback f.unop) hS)

theorem fixedSieves_eq_closedSieves :
    L.fixedSieves = Functor.closedSieves L.toGrothendieckTopology := by
  refine Subfunctor.ext (funext fun X => Set.ext fun (S : Sieve X.unop) => ?_)
  change L.j X.unop S = S ↔ L.toGrothendieckTopology.IsClosed S
  rw [GrothendieckTopology.isClosed_iff_close_eq_self, close_toGrothendieckTopology]

/-- `fixedSieves` is the equalizer of `j` and the identity of `Ω`. -/
theorem range_le_fixedSieves_iff {G : Cᵒᵖ ⥤ Type (max u v)} (φ : G ⟶ Functor.sieves C) :
    Subfunctor.range φ ≤ L.fixedSieves ↔ φ ≫ L.hom = φ := by
  refine ⟨fun h => ?_, fun h X S => ?_⟩
  · ext X g
    exact h X ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact types_congr_hom (NatTrans.congr_app h X) g

end LawvereTierneyTopology

end CategoryTheory
