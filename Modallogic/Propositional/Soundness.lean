import Modallogic.Propositional.Formula
import Modallogic.Propositional.Semantics
import Modallogic.Propositional.Syntax.HilbertStyle

namespace Modallogic.Propositional

namespace Soundness

open Semantics
open Syntax.HilbertStyle

variable {α β : Type} (φ : Formula α)  (Γ : Formulae α)

theorem theorem_valid : (Theorem φ) → (⊨ₚ φ) := by
  intro h
  induction h with
  | ax1 => intro V; exact fun a _ => a
  | ax2 => intro V; exact fun a b c => a c (b c)
  | ax3 => intro V; simp [Semantics.Satisfy]; exact not_imp_not.mp
  | mp _ _ ih₁ ih₂ => apply Valid.mp _ _ ih₁ ih₂

theorem weak_soundness : (⊢ₚ φ) → (⊨ₚ φ) := by
  intro h;
  apply theorem_valid;
  apply Provable.to_theorem _ h;

theorem soundness : (Γ ⊢ₚ φ) → (Γ ⊨ₚ φ) := by
  intro h;
  induction h with
  | thm _ ih => apply Consequence.valid_consequence Γ _ (theorem_valid _ ih);
  | ctx _ ih => intro V h2; apply h2 _ ih;
  | mp _ _ _ _ ih1 ih2 => exact Consequence.mp _ _ _ ih1 ih2;

end Soundness

end Modallogic.Propositional
