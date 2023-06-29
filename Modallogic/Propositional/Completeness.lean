import Modallogic.Propositional.Formula
import Modallogic.Propositional.Semantics
import Modallogic.Propositional.Syntax.HilbertStyle

namespace Modallogic.Propositional

namespace Completeness

open Semantics
open Syntax.HilbertStyle.Provable

variable {α β : Type} (φ : Formula α)  (Γ : Formulae α)

lemma incosistent_explosion (h : inconsistent Γ) : (Γ ⊢ₚ ψ) := by
  apply Exists.elim h;
  intro φ h;
  have h1 : {φ, ¬ₚφ} ⊆ Γ := by
    intro x h2;
    cases h2 with
    | inl h2 => rw [h2]; exact h.left
    | inr h2 => rw [h2]; exact h.right
  exact weakening_subset ({φ, ¬ₚφ}) Γ ψ h1 (explosion φ ψ);

lemma intro_inconsistent' : (∃ φ, ((Γ ⊢ₚ φ) ∧ (Γ ⊢ₚ ¬ₚφ))) → (Γ ⊢ₚ ψ) := by
  intro h;
  apply Exists.elim h;
  intro φ h1;
  sorry

lemma intro_inconsistent : (∃ φ, ((Γ ⊢ₚ φ) ∧ (Γ ⊢ₚ ¬ₚφ))) → (inconsistent Γ) := by
  intro h;
  sorry

theorem iff_inconsistent_provable : (inconsistent (Γ ∪ {φ})) ↔ (Γ ⊢ₚ φ) := by
  apply Iff.intro;
  . intro h; sorry;
  . intro h;
    apply intro_inconsistent;
    apply Exists.intro φ;
    sorry

theorem expansion_inconsistent : (Γ ⊬ₚ φ) → (consistent (Γ ∪ {φ})) := by
  have h1 := (iff_inconsistent_provable φ Γ).mp;
  contrapose!;
  rw [consistent];
  push_neg;
  exact h1

theorem weak_completeness : (⊨ₚ φ) → (⊢ₚ φ) := by sorry

end Completeness

end Modallogic.Propositional
