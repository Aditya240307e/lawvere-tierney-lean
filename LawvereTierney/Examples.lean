/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/

module

public import LawvereTierney.DoubleNegation
public import Mathlib.Order.Fin.Basic

/-!
# The presheaf topos of the two-element chain

Take `C = Fin 2`, the poset `0 ≤ 1` seen as a category. The sieve `S` on `1` consisting of the
arrows out of `0` is not maximal, and its negation is empty, so `S ⊔ Sᶜ ≠ ⊤`. The internal logic of
the presheaf topos of `C` is therefore not classical. For the double negation topology, `S` is
a covering sieve, so excluded middle is restored on passing to sheaves
(see `LawvereTierney.SheafForcing`).

## Main results

* `LawvereTierneyTopology.Examples.sup_compl_ne_top`: excluded middle fails for `twoChainSieve`.
* `LawvereTierneyTopology.Examples.twoChainSieve_mem_dense`: but `twoChainSieve` covers `1` for the
  dense topology.
-/

@[expose] public section

namespace CategoryTheory

namespace LawvereTierneyTopology

namespace Examples

/-- The sieve on `1 : Fin 2` of the arrows whose source is `0`. -/
def twoChainSieve : Sieve (1 : Fin 2) where
  arrows Y _ := Y = 0
  downward_closed := by
    rintro Y Z f rfl g
    exact Fin.le_zero_iff.1 g.down.down

theorem compl_twoChainSieve : twoChainSieveᶜ = ⊥ := by
  refine le_bot_iff.1 fun Y f hf => ?_
  exact hf (homOfLE (Fin.zero_le _)) rfl

/-- Excluded middle fails in the internal logic of the presheaf topos of the two-element chain. -/
theorem sup_compl_ne_top : twoChainSieve ⊔ twoChainSieveᶜ ≠ ⊤ := by
  intro h
  have h1 : (twoChainSieve ⊔ twoChainSieveᶜ) (𝟙 (1 : Fin 2)) := by
    rw [h]
    exact Sieve.top_apply _
  rcases (Sieve.union_apply _).1 h1 with h2 | h2
  · exact absurd (show (1 : Fin 2) = 0 from h2) (by decide)
  · exact h2 (homOfLE (Fin.zero_le _)) rfl

theorem not_forall_sup_compl_eq_top : ¬ ∀ S : Sieve (1 : Fin 2), S ⊔ Sᶜ = ⊤ :=
  fun h => sup_compl_ne_top (h twoChainSieve)

/-- The sieve is not regular, so it is not a closed sieve for the double negation topology. -/
theorem not_isRegular_twoChainSieve : ¬ Heyting.IsRegular twoChainSieve := by
  intro h
  rw [Heyting.IsRegular, compl_twoChainSieve, compl_bot] at h
  have h1 : twoChainSieve (𝟙 (1 : Fin 2)) := h ▸ Sieve.top_apply _
  exact absurd (show (1 : Fin 2) = 0 from h1) (by decide)

theorem twoChainSieve_mem_dense :
    twoChainSieve ∈ (GrothendieckTopology.dense : GrothendieckTopology (Fin 2)) 1 := by
  rw [← compl_compl_eq_top_iff, compl_twoChainSieve, compl_bot]

end Examples

end LawvereTierneyTopology

end CategoryTheory
