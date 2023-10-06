import ModalLogic.PropositionalLogic.DeductionSystem.Notations
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal0
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal
import ModalLogic.PropositionalLogic.DeductionSystem.Intuitional

open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem
open IsMinimal HasMP HasDT

open Finset 
attribute [simp] union_comm insert_eq

namespace ModalLogic.PropositionalLogic.DeductionSystem

variable [DecidableEq α] [HasImply α] [HasDisj α] [HasConj α] [HasNeg α]
variable {D : DeductionSystem α} [IsClassical D]

lemma contrapose₃ : (Γ ⊢ᵈ[D] (~φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (~ψ ⇒ φ)) := by
  sorry
  /-
  intro H₁;
  
  -- repeat apply DT.mpr;
  have h₁ : (Γ ∪ {~φ} ∪ {~ψ}) ⊢ᵈ[D] ψ := ↑(DT.mp H₁);
  have h₂ : (Γ ∪ {~φ} ∪ {~ψ}) ⊢ᵈ[D] ψ ⇒ ⊥ := by simp;
  have h₃ : (Γ ∪ {~φ} ∪ {~ψ}) ⊢ᵈ[D] ⊥ := MP h₂ h₁;
  sorry
  -/

lemma contrapose₄ : (Γ ⊢ᵈ[D] (~φ ⇒ ~ψ)) → (Γ ⊢ᵈ[D] (ψ ⇒ φ)) := by
  sorry
  /-
  simp;
  intro H;
  repeat apply DT.mpr;
  sorry
  -/

lemma imply_elim_ant_dne : (Γ ⊢ᵈ[D] (~~φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (φ ⇒ ψ)) := by
  intro H₁;
  exact contrapose₄ (contrapose₃ H₁);

variable [HasBot α] [HasNegDef α] in
lemma imply_elim_con_dne : (Γ ⊢ᵈ[D] (φ ⇒ ~~ψ)) → (Γ ⊢ᵈ[D] (φ ⇒ ψ)) := by
  intro H₁;
  exact contrapose₄ (contrapose₂ H₁);

end ModalLogic.PropositionalLogic.DeductionSystem