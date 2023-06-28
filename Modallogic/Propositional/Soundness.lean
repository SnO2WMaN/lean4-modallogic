import Modallogic.Propositional.Formula
import Modallogic.Propositional.HilbertProof
import Modallogic.Propositional.Semantics

namespace Modallogic.Propositional

namespace Soundness

open HilbertProof
open Semantics

variable {α β : Type} (φ : Formula α)  (Γ : Formulae α)

theorem theorem_valid : (HTheorem φ) → (⊨ₚ φ) := by
  intro h
  induction h with
  | ax1 => intro V; exact fun a _ => a
  | ax2 => intro V; exact fun a b c => a c (b c)
  | ax3 => intro V; simp [Semantics.Satisfy]; exact not_imp_not.mp
  | mp _ _ ih₁ ih₂ => apply Valid.mp _ _ ih₁ ih₂

theorem weak_soundness : (⊢ₚ φ) → (⊨ₚ φ) := by
  intro h;
  apply theorem_valid;
  apply HProvable.to_theorem _ h;

theorem soundness : (Γ ⊢ₚ φ) → (Γ ⊨ₚ φ) := by
  intro h;
  induction h with
  | thm h => apply Consequence.valid_consequence Γ _ (theorem_valid φ h);
  | ctx h => intro V h2; apply h2 _ h;

end Soundness

end Modallogic.Propositional
