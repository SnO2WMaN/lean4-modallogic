import Aesop
import ModalLogic.Arithmetic.Notation
import ModalLogic.Arithmetic.IT1

open ModalLogic.PropositionalLogic 
open Axioms
open DeductionSystem HasMP
open ModalLogic.Arithmetic.Arithmetic Derivability1 Derivability2

namespace ModalLogic.Arithmetic

variable [DecidableEq α]
variable {T U : Arithmetic α} {Γ Δ : Context (Sentence α)}

variable [HasDT T.toDeductionSystem] [HasMP T.toDeductionSystem] [HasExplode T.toDeductionSystem] [HasDNElim T.toDeductionSystem]
variable [HasFixedPointTheorem T Γ] [HasGoedelSentence T Γ]
variable [Derivability1 T Γ] [Derivability2 T Γ] [FormalizedSigma1Completeness T Γ]

variable [HasMP U.toDeductionSystem] [HasDT U.toDeductionSystem]

lemma GoedelIT2.lem1 : ∀ (σ : Sentence α), ⊢ₐ[T ∔ Γ] (~ₐPr[T ∔ Γ](σ) ⇒ₐ ConL[T ∔ Γ]) := by
  intro σ; 
  have h₁ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](⊥ₐ ⇒ₐ σ) := D1 (T.deducible_EFQ σ);
  have h₂ : ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](⊥ₐ) ⇒ₐ Pr[T ∔ Γ](σ)) := MP D2 h₁;
  have h₃ : ⊢ₐ[T ∔ Γ] ~ₐPr[T ∔ Γ](σ) ⇒ₐ ~ₐPr[T ∔ Γ](⊥ₐ) := deducible_contrapose₁ h₂;
  exact h₃;

lemma GoedelIT2.lem2 (hTU : ∀ {σ}, (⊢ₐ[T ∔ Γ] σ) → (⊢ₐ[U ∔ Δ] σ))
  : (⊢ₐ[U ∔ Δ] (ConL[T ∔ Γ] ⇒ₐ ~ₐPr[T ∔ Γ](σ))) ↔ (⊢ₐ[U ∔ Δ] (Pr[T ∔ Γ](σ) ⇒ₐ Pr[T ∔ Γ](~ₐσ))) := by
  apply Iff.intro;
  . intro H;
    have h₁ : ⊢ₐ[U ∔ Δ] ~ₐPr[T ∔ Γ](~ₐσ) ⇒ₐ ConL[T ∔ Γ] := hTU (GoedelIT2.lem1 (~ₐσ));
    have h₂ : ⊢ₐ[U ∔ Δ] ~ₐPr[T ∔ Γ](~ₐσ) ⇒ ~ₐPr[T ∔ Γ](σ) := deducible_imply_trans ⟨h₁, H⟩;
    exact U.deducible_contrapose₄ h₂;
  . intro H;
    have h₁ : ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](~ₐσ)) ⇒ₐ Pr[T ∔ Γ](⊥ₐ) := Provable.noContradiction;
    have h₂ : ⊢ₐ[U ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](~ₐσ)) ⇒ₐ Pr[T ∔ Γ](⊥ₐ) := hTU h₁;
    have h₃ : ⊢ₐ[U ∔ Δ] Pr[T ∔ Γ](σ) ⇒ₐ Pr[T ∔ Γ](⊥ₐ) := deducible_ant_conj_elim_left ⟨h₂, H⟩;
    exact U.deducible_contrapose₁ h₃;

lemma GoedelIT2.lem3 (hG : GoedelSentence T Γ G ): ⊢ₐ[T ∔ Γ] (ConL[T ∔ Γ] ⇒ₐ ~ₐPr[T ∔ Γ](G)) := by
  have h₁ : ⊢ₐ[T ∔ Γ] ~ₐG ⇒ₐ Pr[T ∔ Γ](~ₐG) := FormalizedSigma1Completeness.FS1C;
  have h₂ : ⊢ₐ[T ∔ Γ] ~ₐ~ₐPr[T ∔ Γ](G) ⇒ₐ ~ₐG := deducible_contrapose₁ (deducible_equiv_mp hG);
  have h₃ : ⊢ₐ[T ∔ Γ] ~ₐ~ₐPr[T ∔ Γ](G) ⇒ₐ Pr[T ∔ Γ](~ₐG) := deducible_imply_trans (⟨h₂, h₁⟩);
  have h₄ : ⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](G) ⇒ₐ Pr[T ∔ Γ](~ₐG) := deducible_imply_elim_ant_dne h₃;
  exact (GoedelIT2.lem2 (by simp)).mpr h₄;

/-- Every Gödel sentence is equivalent to sentence expresses Löb Consistency of T -/
@[simp]
theorem equiv_LConsistencyOf_GoedelSentence (hG : GoedelSentence T Γ G) : ⊢ₐ[T ∔ Γ] (G ⇔ₐ ConL[T ∔ Γ]) := by
  have h₁ : ⊢ₐ[T ∔ Γ] (~ₐPr[T ∔ Γ](G) ⇒ₐ ConL[T ∔ Γ]) := GoedelIT2.lem1 G;
  have h₂ : ⊢ₐ[T ∔ Γ] (ConL[T ∔ Γ] ⇒ₐ ~ₐPr[T ∔ Γ](G)) := GoedelIT2.lem3 hG;
  have h₃ : ⊢ₐ[T ∔ Γ] (~ₐPr[T ∔ Γ](G) ⇔ₐ ConL[T ∔ Γ]) := deducible_equiv_intro ⟨h₁, h₂⟩;
  exact deducible_equiv_trans hG h₃;

/-- Unprovability side of Gödel's 2nd incompleteness theorem. -/
theorem LConsistencyOfUnprovablility_of_HBConsistent : (IsHBConsistent T Γ) → (⊬ₐ[T ∔ Γ] ConL[T ∔ Γ]) := by
  intro hConsistent;
  have ⟨G, hG⟩ := T.existsGoedelSentence Γ;
  have h₁ : ⊢ₐ[T ∔ Γ] G ⇔ₐ ConL[T ∔ Γ] := equiv_LConsistencyOf_GoedelSentence hG;
  have h₂ : ⊬ₐ[T ∔ Γ] G := GoedelSentenceUnprovability hG hConsistent;
  exact undeducible_equiv_left h₁ h₂;

lemma HBInconsistent_of_LConsistencyOfProvability : (⊢ₐ[T ∔ Γ] ConL[T ∔ Γ]) → (IsHBInconsistent T Γ) := by
  exact λ h₁ h₂ => (LConsistencyOfUnprovablility_of_HBConsistent h₂) h₁

/-- Unrefutability side of Gödel's 2nd incompleteness theorem. -/
theorem LConsistencyOfUnrefutability_of_Soundness : (IsSigma1Sounds T Γ) → (⊬ₐ[T ∔ Γ] ~ₐConL[T ∔ Γ]) := by
  intro hSounds;
  have ⟨G, hG⟩ := T.existsGoedelSentence Γ;
  have h₁ : ⊢ₐ[T ∔ Γ] ~ₐG ⇔ₐ ~ₐConL[T ∔ Γ] := deducible_equiv_neg (equiv_LConsistencyOf_GoedelSentence hG)
  have h₂ : ⊬ₐ[T ∔ Γ] ~ₐG := GoedelSentenceUnrefutability hG hSounds;
  exact undeducible_equiv_left h₁ h₂;

end ModalLogic.Arithmetic