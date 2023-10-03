import Aesop
import ModalLogic.Arithmetic.Notation
import ModalLogic.Arithmetic.IT1

open ModalLogic.PropositionalLogic.Axioms
open ModalLogic.PropositionalLogic.DeductionSystem
open ModalLogic.Arithmetic.Arithmetic Derivability1 Derivability2

namespace ModalLogic.Arithmetic

variable [DecidableEq α] {T : Arithmetic α}
variable [HasDT T.toDeductionSystem] [HasMP T.toDeductionSystem] [HasExplode T.toDeductionSystem] [HasDNElim T.toDeductionSystem]
variable [HasFixedPoint T] [HasGoedelSentence T]
variable [Derivability1 T] [Derivability2 T] [FormalizedSigma1Completeness T]

lemma GoedelIT2.lem1 : ∀ (σ : Sentence α), ⊢ₐ[T] ~Pr[T](σ) ⇒ ConL[T] := by
  intro σ; 
  have h₁ : ⊢ₐ[T] Pr[T](⊥ ⇒ σ) := D1 (T.deducible_EFQ σ);
  have h₂ : ⊢ₐ[T] (Pr[T](⊥) ⇒ Pr[T](σ)) := deducible_MP D2 h₁;
  have h₃ : ⊢ₐ[T] ~Pr[T](σ) ⇒ ~Pr[T](⊥) := deducible_contrapose₁ h₂;
  exact h₃;

lemma GoedelIT2.lem2
  (U : Arithmetic α) (hTU : ∀ {σ}, (⊢ₐ[T] σ) → (⊢ₐ[U] σ))
  : (⊢ₐ[U] ConL[T] ⇒ ~Pr[T](σ)) ↔ (⊢ₐ[U] Pr[T](σ) ⇒ Pr[T](~σ)) := by
  apply Iff.intro;
  . sorry
  . sorry

variable {hG : GoedelSentence T G}
lemma GoedelIT2.lem3 : ⊢ₐ[T] (ConL[T] ⇒ₐ ~Pr[T](G)) := by
  have h₁ : ⊢ₐ[T] ~ₐG ⇒ₐ Pr[T](~G) := FormalizedSigma1Completeness.FS1C;
  have h₂ : ⊢ₐ[T] ~ₐ~ₐPr[T](G) ⇒ₐ ~ₐG := T.deducible_contrapose₁ (deducible_equiv_mp hG);
  have h₃ : ⊢ₐ[T] ~ₐ~ₐPr[T](G) ⇒ₐ Pr[T](~ₐG) := deducible_imply_trans (⟨h₂, h₁⟩);
  have h₄ : ⊢ₐ[T] Pr[T](G) ⇒ₐ Pr[T](~ₐG) := deducible_imply_elim_ant_dne h₃;
  exact (GoedelIT2.lem2 T (by simp)).mpr h₄; 

@[simp]
theorem equiv_LConsistencyOf_GoedelSentence (hG : GoedelSentence T G) : ⊢ₐ[T] G ⇔ ConL[T] := by
  have h₁ : ⊢ₐ[T] ~ₐPr[T](G) ⇒ ConL[T] := GoedelIT2.lem1 G;
  have h₂ : ⊢ₐ[T] ConL[T] ⇒ₐ ~ₐPr[T](G) := sorry;
  have h₃ : ⊢ₐ[T] ~Pr[T](G) ⇔ₐ ConL[T] := sorry;
  have h₄ := T.deducible_equiv_trans hG h₃;
  exact h₄;

/--
  Unprovability side of Gödel's 2nd incompleteness theorem.
-/
theorem Unprovable_LConsistencyOf_of_HBConsistent : (IsHBConsistent T) → (⊬ₐ[T] ConL[T]) := by
  intro hConsistent;
  have ⟨G, hG⟩ := T.existsGoedelSentence;
  have h₁ : ⊢ₐ[T] G ⇔ ConL[T] := equiv_LConsistencyOf_GoedelSentence hG;
  have h₂ : ⊬ₐ[T] G := GoedelSentenceUnprovability hG hConsistent;
  exact undeducible_equiv_left h₁ h₂;

/--
  Unrefutability side of Gödel's 2nd incompleteness theorem.
-/
theorem Unrefutable_LConsistencyOf_of_Soundness : (IsSigma1Sounds T) → (⊬ₐ[T] ~ₐConL[T]) := by
  intro hSounds;
  have ⟨G, hG⟩ := T.existsGoedelSentence;
  have h₁ : ⊢ₐ[T] ~ₐG ⇔ₐ ~ₐConL[T] := deducible_equiv_neg (equiv_LConsistencyOf_GoedelSentence hG)
  have h₂ : ⊬ₐ[T] ~ₐG := GoedelSentenceUnrefutability hG hSounds;
  exact undeducible_equiv_left h₁ h₂;

end ModalLogic.Arithmetic