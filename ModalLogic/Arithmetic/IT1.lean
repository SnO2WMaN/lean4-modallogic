import Aesop
import ModalLogic.Arithmetic.Notation

open ModalLogic.PropositionalLogic.DeductionSystem
open ModalLogic.Arithmetic.Arithmetic Derivability1

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α}
variable [HasDT T.toDeductionSystem] [HasMP T.toDeductionSystem] [HasExplode T.toDeductionSystem] [HasDNElim T.toDeductionSystem]
variable [HasFixedPoint T] [HasGoedelSentence T] [Derivability1 T]

/--
  Unprovablility side of Gödel's 1st incompleteness theorem.
-/
theorem GoedelSentenceUnprovability (hG : GoedelSentence T G) : (IsHBConsistent T) → (⊬ₐ[T] G) := by
  intro hConsistent;
  
  intro hPG;

  have h₁ : ⊢ₐ[T] Pr[T](G) := D1 hPG;
  have h₂ : ⊢ₐ[T] ~ₐ~ₐPr[T](G) := T.deducible_negneg_intro h₁;
  have h₃ : ⊢ₐ[T] ~ₐG := T.deducible_equiv_neg_right hG h₂;
  have h₄ : ⊬ₐ[T] ~ₐG := hConsistent G hPG;

  exact h₄ h₃;

/--
  Unrefutability side of Gödel's 1st incompleteness theorem.
-/
theorem GoedelSentenceUnrefutability (hG : GoedelSentence T G) : (IsSigma1Sounds T) → (⊬ₐ[T] ~ₐG) := by
  intro hSounds;

  -- have ⟨G, hG⟩ := T.existsGoedelSentence;
  -- apply Exists.intro G;

  have hConsistent := HBConsistent_of_Sigma1Soundness hSounds;

  intro hRG;

  have h₁ := deducible_equiv_left (deducible_equiv_neg hG) hRG;
  have h₂ : ⊢ₐ[T] Pr[T](G) := deducible_negneg_elim h₁;
  have h₃ : ⊢ₐ[T] G :=  hSounds.Sigma1Sounds G h₂;
  have h₄ : ⊬ₐ[T] ~ₐG := hConsistent G h₃;

  exact h₄ hRG;

/--
  Gödel's 1st incompleteness theorem.
-/
theorem GoedelIT1 : (IsSigma1Sounds T) → (Incompleteness T) := by
  intro hSounds;
  have ⟨G, hG⟩ := T.existsGoedelSentence;

  have p : (⊬ₐ[T] G) := GoedelSentenceUnprovability hG (HBConsistent_of_Sigma1Soundness hSounds);
  have r : (⊬ₐ[T] ~ₐG) := GoedelSentenceUnrefutability hG hSounds;
  exact ⟨G, ⟨p, r⟩⟩;

end ModalLogic.Arithmetic