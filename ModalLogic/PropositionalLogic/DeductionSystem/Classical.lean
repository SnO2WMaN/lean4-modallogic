import ModalLogic.SupplymentSimp
import ModalLogic.PropositionalLogic.DeductionSystem.Notations
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal0
import ModalLogic.PropositionalLogic.DeductionSystem.Minimal
import ModalLogic.PropositionalLogic.DeductionSystem.Intuitional

open ModalLogic.PropositionalLogic
open Axioms
open DeductionSystem IsMinimal HasElimImply HasElimDN 

namespace ModalLogic.PropositionalLogic.DeductionSystem

variable [DecidableEq α] [HasImply α] [HasDisj α] [HasConj α] [HasNeg α]
variable {D : DeductionSystem α} [IsClassical D]

variable [HasBot α] [HasNegDef α]

@[simp]
lemma Contrapose₃ : (Γ ⊢ᵈ[D] (~φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (~ψ ⇒ φ)) := by
  intro H;
  have h₁ : (Γ ∪ {~ψ}) ⊢ᵈ[D] ~ψ := by simp;
  have h₂ : (Γ ∪ {~ψ}) ⊢ᵈ[D] ~ψ ⇒ ~~φ := contrapose₁ H;
  have h₃ : (Γ ∪ {~ψ}) ⊢ᵈ[D] ~~φ := ElimImply' ⟨h₂, h₁⟩;
  aesop;
alias contrapose₃ := Contrapose₃

@[simp]
lemma Contrapose₄ : (Γ ⊢ᵈ[D] (~φ ⇒ ~ψ)) → (Γ ⊢ᵈ[D] (ψ ⇒ φ)) := by
  intro H;
  have h₁ : (Γ ∪ {ψ}) ⊢ᵈ[D] ψ := by simp;
  have h₂ : (Γ ∪ {ψ}) ⊢ᵈ[D] ~~ψ := IntroDN h₁;
  have h₃ : (Γ ∪ {ψ}) ⊢ᵈ[D] ~~ψ ⇒ ~~φ := contrapose₁ H;
  have h₄ : (Γ ∪ {ψ}) ⊢ᵈ[D] ~~φ := ElimImply' ⟨h₃, h₂⟩;
  aesop;
alias contrapose₄ := Contrapose₄

lemma ElimImplyAntDN : (Γ ⊢ᵈ[D] (~~φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (φ ⇒ ψ)) := by
  intro H₁;
  exact contrapose₄ (contrapose₃ H₁);
alias imply_elim_ant_dne := ElimImplyAntDN

variable [HasBot α] [HasNegDef α] in
lemma ElimImplyConDN : (Γ ⊢ᵈ[D] (φ ⇒ ~~ψ)) → (Γ ⊢ᵈ[D] (φ ⇒ ψ)) := by
  intro H₁;
  exact contrapose₄ (contrapose₂ H₁);
alias imply_elim_con_dne := ElimImplyConDN

end ModalLogic.PropositionalLogic.DeductionSystem