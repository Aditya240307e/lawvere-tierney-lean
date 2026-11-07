/-
Copyright (c) 2026 Aditya Ekbote. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ekbote
-/
import LawvereTierney.Examples
import LawvereTierney.Logic
import LawvereTierney.SheafForcing

/-!
# Classical principles in the internal logic

By soundness (`IPC.Derives.eval_eq_top`), a formula whose value is not `⊤` under some valuation in
some Heyting algebra cannot be derived. The Heyting algebra of sieves on `1` in the presheaf topos
of the chain `0 ≤ 1` (see `LawvereTierney.Examples`) is such a witness for the two best known
classical principles. In the sheaf semantics of the double negation topology, on the other hand,
excluded middle holds for every valuation.

## Main results

* `IPC.not_derives_lem`: `p ∨ ¬p` is not derivable.
* `IPC.not_derives_doubleNegation_elim`: `¬¬p ⇨ p` is not derivable.
* `IPC.eval_lem_doubleNegation`: `φ ∨ ¬φ` has value `⊤` under every valuation in the closed
  subpresheaves for the double negation topology.
-/

universe w v u

namespace IPC

open CategoryTheory LawvereTierneyTopology LawvereTierneyTopology.Examples

/-- Excluded middle for one variable. -/
def lem : Formula Unit :=
  .atom () ⊔ (.atom ())ᶜ

/-- Double negation elimination for one variable. -/
def doubleNegationElim : Formula Unit :=
  (.atom ())ᶜᶜ ⇨ .atom ()

theorem not_derives_lem : ¬ Derives ∅ lem := fun d => by
  have := d.eval_eq_top (H := Sieve (1 : Fin 2)) fun _ => twoChainSieve
  exact sup_compl_ne_top (by simpa [lem] using this)

theorem not_derives_doubleNegation_elim : ¬ Derives ∅ doubleNegationElim := fun d => by
  have := d.eval_eq_top (H := Sieve (1 : Fin 2)) fun _ => twoChainSieve
  simp only [doubleNegationElim, eval_himp, eval_compl, eval_atom, compl_twoChainSieve,
    compl_bot, top_himp] at this
  have h1 : twoChainSieve (𝟙 (1 : Fin 2)) := this ▸ Sieve.top_apply _
  exact absurd (show (1 : Fin 2) = 0 from h1) (by decide)

/-- Excluded middle is valid in the sheaf semantics of the double negation topology. -/
theorem eval_lem_doubleNegation {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {α : Type*} (v : α → (doubleNegation C).closedSubobjects F) (φ : Formula α) :
    eval v (φ ⊔ φᶜ) = ⊤ := by
  rw [eval_sup, eval_compl]
  exact (isCompl_compl_doubleNegation (eval v φ)).sup_eq_top

end IPC
