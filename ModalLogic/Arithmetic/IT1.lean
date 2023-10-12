import ModalLogic.PropositionalLogic.DeductionSystem
import ModalLogic.Arithmetic.Notation

open ModalLogic.PropositionalLogic DeductionSystem HasElimDN
open ModalLogic.Arithmetic.Arithmetic Derivability1

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α} {Γ : Context (Sentence α)} 
variable [HasFixedPointTheorem T Γ] [Derivability1 T Γ Γ]

/-- Unprovablility side of Gödel's 1st incompleteness theorem. -/
theorem GoedelSentenceUnprovability [IsMinimal T.toDeductionSystem] (hG : GoedelSentence T Γ G) : (IsHBConsistent T Γ) → (⊬ₐ[T ∔ Γ] G) := by
  intro hConsistent;
  
  intro hPG;

  have h₁ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](G) := D1 hPG;
  have h₂ : ⊢ₐ[T ∔ Γ] ~~Pr[T ∔ Γ](G) := IntroDN h₁;
  have h₃ : ⊢ₐ[T ∔ Γ] ~G := equiv_pick_neg_right hG h₂;
  have h₄ : ⊬ₐ[T ∔ Γ] ~G := hConsistent G hPG;
  exact h₄ h₃;

/-- Unrefutability side of Gödel's 1st incompleteness theorem. -/
theorem GoedelSentenceUnrefutability [IsClassical T.toDeductionSystem] (hG : GoedelSentence T Γ G) : (IsSigma1Sounds T Γ) → (⊬ₐ[T ∔ Γ] ~G) := by
  intro hSounds;
  have hConsistent := HBConsistent_of_Sigma1Soundness hSounds;

  intro hRG;

  have h₁ := equiv_pick_left (equiv_neg hG) hRG;
  have h₂ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](G) := ElimDN h₁;
  have h₃ : ⊢ₐ[T ∔ Γ] G :=  hSounds.Sigma1Sounds G h₂;
  have h₄ : ⊬ₐ[T ∔ Γ] ~G := hConsistent G h₃;
  exact h₄ hRG;

/-- Gödel's 1st incompleteness theorem. -/
theorem GoedelIT1 [IsClassical T.toDeductionSystem] : (IsSigma1Sounds T Γ) → (Incompleteness T Γ) := by
  intro hSounds;
  have ⟨G, hG⟩ := T.existsGoedelSentence Γ;

  have p : (⊬ₐ[T ∔ Γ] G) := GoedelSentenceUnprovability hG (HBConsistent_of_Sigma1Soundness hSounds);
  have r : (⊬ₐ[T ∔ Γ] ~G) := GoedelSentenceUnrefutability hG hSounds;
  exact ⟨G, ⟨p, r⟩⟩;

end ModalLogic.Arithmetic