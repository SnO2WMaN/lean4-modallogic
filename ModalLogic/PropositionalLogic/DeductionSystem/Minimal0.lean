import ModalLogic.SupplymentSimp
import ModalLogic.PropositionalLogic.DeductionSystem.Notations

open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem
open HasWeakenContext HasIntroImply HasElimImply

namespace ModalLogic.PropositionalLogic.DeductionSystem

variable [DecidableEq α] [HasImply α]
variable {D : DeductionSystem α} [IsMinimal₀ D]
 
theorem K (φ ψ) : Γ ⊢ᵈ[D] (Axioms.K φ ψ) := by aesop;

@[simp] 
theorem K' {φ ψ} : Γ ⊢ᵈ[D] (Axioms.K φ ψ) := K φ ψ

theorem S (φ ψ ξ) : Γ ⊢ᵈ[D] (Axioms.S φ ψ ξ) := by
  simp only [Axioms.S];
  have h₁ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ {φ ⇒ ψ} ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ {φ ⇒ ψ} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ := by simp;
  have h₃ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ {φ ⇒ ψ} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ ⇒ ξ := by simp;
  have h₄ := ElimImply ⟨h₂, h₁⟩;
  have h₅ := ElimImply ⟨h₃, h₁⟩;
  have h₆ := ElimImply ⟨h₅, h₄⟩;
  aesop;

@[simp] 
theorem S' {φ ψ ξ} : Γ ⊢ᵈ[D] (Axioms.S φ ψ ξ) := S φ ψ ξ

lemma ImplyTrans : ((Γ ⊢ᵈ[D] (φ ⇒ ψ)) ∧ (Γ ⊢ᵈ[D] (ψ ⇒ ξ))) → (Γ ⊢ᵈ[D] (φ ⇒ ξ)) := by
  intro H₁;
  have H₁l : (Γ ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ := H₁.left;
  have H₁r : (Γ ∪ {φ}) ⊢ᵈ[D] ψ ⇒ ξ := H₁.right;
  have h₁ : (Γ ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ := ElimImply ⟨H₁l, h₁⟩;
  have h₃ := ElimImply ⟨H₁r, h₂⟩;
  aesop;
alias imply_trans := ImplyTrans

variable [HasBot α] [HasNeg α] [HasNegDef α]

@[simp]
theorem DNI : Γ ⊢ᵈ[D] (Axioms.DNI φ) := by
  simp only [Axioms.DNI, HasNegDef.NegDef];
  have h₁ : (Γ ∪ {φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ ⇒ ⊥ := by simp;
  have h₃ := ElimImply ⟨h₂, h₁⟩;
  aesop;

@[simp]
theorem IntroDN : (Γ ⊢ᵈ[D] (φ)) → (Γ ⊢ᵈ[D] (~~φ)) := by
  intro H;
  have := ElimImply ⟨(DNI : Γ ⊢ᵈ[D] Axioms.DNI φ), H⟩;
  aesop;

@[simp]
theorem Contrapose₁ : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (~ψ ⇒ ~φ)) := by
  intro H₁;
  simp [HasNegDef.NegDef];

  have H₁ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ := H₁;
  have h₁ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] ψ ⇒ ⊥ := by simp;
  have h₂ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₃ := ElimImply ⟨H₁, h₂⟩;
  have h₄ := ElimImply ⟨h₁, h₃⟩;
  aesop;
alias contrapose₁ := Contrapose₁

lemma CON₁ : Γ ⊢ᵈ[D] (Axioms.Con₁ φ ψ) := by
  have h₁ : (Γ ∪ {φ ⇒ ψ, ~ψ}) ⊢ᵈ[D] φ ⇒ ψ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ψ, ~ψ}) ⊢ᵈ[D] ~ψ := by simp;
  have h₃ := contrapose₁ h₁;
  have h₄ := ElimImply ⟨h₃, h₂⟩;
  aesop;

@[simp]
theorem Contrapose₂ : (Γ ⊢ᵈ[D] (φ ⇒ ~ψ)) → (Γ ⊢ᵈ[D] (ψ ⇒ ~φ)) := by
  intro H;
  have H₁ : (Γ ∪ {ψ} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ~ψ := H;
  have h₁ : (Γ ∪ {ψ} ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {ψ} ∪ {φ}) ⊢ᵈ[D] ψ := by simp;
  have h₃ := ElimImply ⟨H₁, h₁⟩;
  have h₄ := ElimNeg ⟨h₃, h₂⟩;
  aesop;
alias contrapose₂ := Contrapose₂

lemma CON₂ : Γ ⊢ᵈ[D] (Axioms.Con₂ φ ψ) := by
  have h₁ : (Γ ∪ {φ ⇒ ~ψ} ∪ {ψ}) ⊢ᵈ[D] φ ⇒ ~ψ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ~ψ} ∪ {ψ}) ⊢ᵈ[D] ψ := by simp;
  have h₃ := contrapose₂ h₁;
  have _ := ElimImply ⟨h₃, h₂⟩;
  aesop;

lemma DT : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) → ((Γ ∪ {φ}) ⊢ᵈ[D] ψ) := by
  intro H;
  exact ElimImply' ⟨WeakenContext H, (by simp)⟩;

end ModalLogic.PropositionalLogic.DeductionSystem