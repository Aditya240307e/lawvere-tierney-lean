/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/
import LawvereTierney.Closure
import LawvereTierney.Heyting
import Mathlib.Order.Heyting.Regular

/-!
# The double negation topology

On the presheaf topos of `C`, negation of sieves is the one from `LawvereTierney.Heyting`, and
`S ↦ Sᶜᶜ` is a Lawvere–Tierney topology. Its Grothendieck topology is the dense topology of
Mathlib: a sieve covers when every arrow into `X` can be refined into the sieve.

The sieves fixed by the double negation topology are the regular elements of the Heyting algebra of
sieves, which form a Boolean algebra. In the sheaf topos for this topology the law of excluded
middle therefore holds, even though it fails in the presheaf topos in general
(see `LawvereTierney.Examples`).

## Main definitions

* `LawvereTierneyTopology.doubleNegation C`: the topology `j S = Sᶜᶜ`.

## Main results

* `LawvereTierneyTopology.doubleNegation_toGrothendieckTopology`: its Grothendieck topology is
  `GrothendieckTopology.dense`.
* `LawvereTierneyTopology.sup_compl_mem_dense`: `S ⊔ Sᶜ` always covers for the dense topology.
* `LawvereTierneyTopology.mem_fixedSieves_doubleNegation_iff`: fixed sieves are regular sieves.

## References

* [S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92], Chapter VI.
-/

universe v u

namespace CategoryTheory

namespace LawvereTierneyTopology

variable (C : Type u) [Category.{v} C]

/-- The double negation topology: `j S = Sᶜᶜ`. -/
def doubleNegation : LawvereTierneyTopology C where
  j _ S := Sᶜᶜ
  natural f S := by rw [Sieve.pullback_compl, Sieve.pullback_compl]
  top _ := by rw [compl_top, compl_bot]
  idem _ S := by rw [compl_compl_compl]
  inf _ S T := compl_compl_inf_distrib S T

variable {C}

@[simp]
theorem doubleNegation_j {X : C} (S : Sieve X) : (doubleNegation C).j X S = Sᶜᶜ :=
  rfl

theorem compl_compl_eq_top_iff {X : C} (S : Sieve X) :
    Sᶜᶜ = ⊤ ↔ S ∈ (GrothendieckTopology.dense : GrothendieckTopology C) X := by
  rw [GrothendieckTopology.dense_covering, ← Sieve.id_mem_iff_eq_top]
  simp only [Sieve.compl_apply, Category.comp_id, not_forall, not_not]

theorem doubleNegation_toGrothendieckTopology :
    (doubleNegation C).toGrothendieckTopology = GrothendieckTopology.dense :=
  GrothendieckTopology.ext (funext fun _ => Set.ext fun S => compl_compl_eq_top_iff S)

theorem ofGrothendieckTopology_dense :
    ofGrothendieckTopology (GrothendieckTopology.dense : GrothendieckTopology C) =
      doubleNegation C := by
  rw [← doubleNegation_toGrothendieckTopology, ofGrothendieckTopology_toGrothendieckTopology]

/-- Excluded middle holds for the covering sieves of the dense topology. -/
theorem sup_compl_mem_dense {X : C} (S : Sieve X) :
    S ⊔ Sᶜ ∈ (GrothendieckTopology.dense : GrothendieckTopology C) X := by
  rw [← compl_compl_eq_top_iff, compl_sup, inf_compl_eq_bot, compl_bot]

theorem mem_fixedSieves_doubleNegation_iff {X : Cᵒᵖ} (S : Sieve X.unop) :
    S ∈ (doubleNegation C).fixedSieves.obj X ↔ Heyting.IsRegular S :=
  Iff.rfl

end LawvereTierneyTopology

end CategoryTheory
