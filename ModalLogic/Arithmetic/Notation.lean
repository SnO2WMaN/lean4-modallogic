import ModalLogic.PropositionalLogic.DeductionSystem

open ModalLogic.PropositionalLogic DeductionSystem

namespace ModalLogic.Arithmetic

inductive Sentence (α : Type u)
| Contradiction : Sentence α
| Imply : Sentence α → Sentence α → Sentence α
deriving DecidableEq, Repr

notation "⊥ₐ" => Sentence.Contradiction
infixl:62 " ⇒ₐ " => Sentence.Imply

namespace Sentence

instance : HasBot (Sentence α) := ⟨Contradiction⟩
instance : HasImply (Sentence α) := ⟨Imply⟩

variable (φ ψ : Sentence α)

@[simp] def Neg := φ ⇒ₐ ⊥ₐ
prefix:64 "~ₐ" => Neg
instance : HasNeg (Sentence α) := ⟨Neg⟩

@[simp] def def_Neg : φ ⇒ₐ ⊥ₐ = ~ₐφ := rfl
instance : HasNegDef (Sentence α) := ⟨def_Neg⟩

@[simp] def Disj := (~ₐφ) ⇒ₐ ψ
infixl:63 " ⋎ₐ " => Disj
instance : HasDisj (Sentence α) := ⟨Disj⟩

@[simp] def def_Disj : (~ₐφ) ⇒ₐ ψ = φ ⋎ₐ ψ := rfl
instance : HasDisjDef (Sentence α) := ⟨def_Disj⟩

@[simp] def Conj := ~ₐ(φ ⇒ ~ψ)
infixl:63 " ⋏ₐ " => Conj
instance : HasConj (Sentence α) := ⟨Conj⟩

@[simp] def def_Conj : ~ₐ(φ ⇒ ~ψ) = φ ⋏ₐ ψ := rfl
instance : HasConjDef (Sentence α) := ⟨def_Conj⟩

@[simp] def Equiv := (φ ⇒ₐ ψ) ⋏ₐ (ψ ⇒ₐ φ)
infixl:61 " ⇔ₐ " => Equiv
instance : PropositionalLogic.HasEquiv (Sentence α) := ⟨Equiv⟩

@[simp]
def def_Equiv : (φ ⇒ₐ ψ) ⋏ₐ (ψ ⇒ₐ φ) = φ ⇔ₐ ψ := rfl
instance : HasEquivDef (Sentence α) := ⟨def_Equiv⟩

end Sentence

open Sentence

structure Arithmetic (α) [DecidableEq α] extends DeductionSystem (Sentence α) where 
  Provable : (Context (Sentence α)) → (Sentence α) → (Sentence α)

notation "Pr[" T " ∔ " Γ "](" σ ")" => Arithmetic.Provable T Γ σ
notation "Pr[" T "](" σ ")" => Pr[T ∔ ∅](σ)

variable [DecidableEq α]
private def Arithmetic.Deducible_def (T : Arithmetic α) (Γ σ) := T.Deducts Γ σ

notation:20 "⊢ₐ[" T " ∔ " Γ "] " σ => Arithmetic.Deducible_def T Γ σ
notation:20 "⊬ₐ[" T " ∔ " Γ "] " σ => ¬(⊢ₐ[T ∔ Γ] σ)

notation:20 "⊢ₐ[" T "] " σ => ⊢ₐ[T ∔ ∅] σ
notation:20 "⊬ₐ[" T "] " σ => ¬(⊢ₐ[T] σ)

namespace Arithmetic

variable (T : Arithmetic α) (Γ Δ : Context (Sentence α))

class IsSigma1Sounds extends Arithmetic α where 
  Sigma1Sounds : ∀ σ, (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Γ] σ)

class HasFixedPointTheorem extends Arithmetic α where
  /-- Fixed point theorem (Diagonal lemma) -/
  FP (P : Sentence α → Sentence α) : ∃ σ, ⊢ₐ[T ∔ Γ] (σ ⇔ₐ (P σ))

class HasFormalDeductionTheorem extends Arithmetic α where
  /-- Formalized deduction theorem -/
  FDT {σ π : Sentence α} : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⇒ₐ π) ⇔ₐ Pr[T ∔ Γ ∪ {σ}](π))

lemma HasFormalDeductionTheorem.FDT_neg {T : Arithmetic α} {Γ Δ} [IsMinimal T.toDeductionSystem] [HasFormalDeductionTheorem T Γ Δ] {σ π} 
  : (⊢ₐ[T ∔ Δ] ~ₐPr[T ∔ Γ](σ ⇒ₐ π) ⇔ₐ ~ₐPr[T ∔ Γ ∪ {σ}](π)) := by
  suffices (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⇒ₐ π) ⇔ₐ Pr[T ∔ Γ ∪ {σ}](π)) from by exact T.equiv_neg this;
  exact HasFormalDeductionTheorem.FDT

def Incompleteness := ∃ σ, (⊬ₐ[T ∔ Γ] σ) ∧ (⊬ₐ[T ∔ Γ] ~ₐσ)

-- Löb style Consistent 
@[simp] def LInconsistent := (⊢ₐ[T ∔ Γ] ⊥ₐ)
@[simp] def LConsistent := ¬(LInconsistent T Γ)

@[simp] def LConsistencyOf : Sentence α := ~ₐPr[T ∔ Γ](⊥ₐ)
notation "ConL[" T " ∔ " Γ "]" => Arithmetic.LConsistencyOf T Γ
notation "ConL[" T "]" => ConL[T ∔ ∅]

-- Hilbert-Bernays style Consistent 
@[simp] def IsHBConsistent := ∀ σ, (⊢ₐ[T ∔ Γ] σ) → (⊬ₐ[T ∔ Γ] ~ₐσ)
@[simp] def IsHBInconsistent := ¬(IsHBConsistent T Γ)

axiom HBConsistent_of_Sigma1Soundness {T : Arithmetic α} {Γ} : IsSigma1Sounds T Γ → IsHBConsistent T Γ

-- Gödel style Consistent 
@[simp] def GConsistent := ∃ σ, (⊬ₐ[T ∔ Γ] σ) 
@[simp] def GInconsistent := ¬(GConsistent T Γ)

class Derivability1 extends Arithmetic α where
  D1  : ∀ {σ}, (⊢ₐ[T ∔ Δ] σ) → (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ)))

class Derivability2 extends Arithmetic α where
  D2 : ∀ {σ π}, ⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ ⇒ₐ π) ⇒ₐ (Pr[T ∔ Γ](σ) ⇒ₐ Pr[T ∔ Γ](π)))

class Derivability3 extends Arithmetic α where
  D3 : ∀ {σ}, ⊢ₐ[T ∔ Δ] ((Pr[T ∔ Γ](σ)) ⇒ₐ Pr[T ∔ Γ](Pr[T ∔ Γ](σ)))

class FormalizedSigma1Completeness extends Arithmetic α where
  FS1C : ∀ {σ}, ⊢ₐ[T ∔ Δ] (σ ⇒ₐ Pr[T ∔ Γ](σ))

section

variable {T : Arithmetic α} [IsMinimal T.toDeductionSystem]
variable {Γ Δ} {σ π : Sentence α}
variable [Derivability1 T Γ Δ] [Derivability2 T Γ Δ] [Derivability3 T Γ Δ]

open HasElimImply HasIntroConj
open Derivability1 Derivability2

lemma Provable.conj_distribute : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ₐ π)) → (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](π))) := by
  intro H;
  simp only [Conj] at H;
  sorry

lemma Provable.PrIntroConj :  (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](π))) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ₐ π)) := by
  intro H;
  simp only [Conj] at H;
  sorry

lemma Provable.PrIntroDN : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](~ₐ~ₐσ)) := λ H => ElimImply' ⟨ElimImply' ⟨D2, D1 DNI⟩, H⟩

lemma Provable.not_pr_negneg_intro : (⊢ₐ[T ∔ Δ] ~ₐPr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Δ] ~ₐPr[T ∔ Γ](~ₐ~ₐσ)) := by
  intro H;
  sorry

lemma Provable.noContradiction' : (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](~ₐσ))) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥ₐ)) := by
  have h₁ : ⊢ₐ[T ∔ Δ] (σ ⋏ₐ ~ₐσ) ⇒ₐ ⊥ₐ := NonContradiction;
  have h₂ : ⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ₐ ~ₐσ) ⇒ₐ Pr[T ∔ Γ](⊥ₐ) := ElimImply' ⟨D2, (D1 h₁)⟩;
  have h₃ : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](~ₐσ)) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥ₐ)) := λ h => ElimImply' ⟨h₂, PrIntroConj h⟩;
  assumption;

lemma Provable.noContradiction : (⊢ₐ[T ∔ Δ] (Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](~ₐσ)) ⇒ₐ Pr[T ∔ Γ](⊥ₐ)) := by
  have h₁ : ⊢ₐ[T ∔ Δ] (σ ⋏ₐ ~ₐσ) ⇒ₐ ⊥ₐ := NonContradiction;
  have h₂ : ⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⋏ₐ ~ₐσ) ⇒ₐ Pr[T ∔ Γ](⊥ₐ) := ElimImply' ⟨D2, (D1 h₁)⟩;
  have h₃ : (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ) ⋏ₐ Pr[T ∔ Γ](~ₐσ)) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥ₐ)) := λ h => ElimImply' ⟨h₂, PrIntroConj h⟩;
  have h₄ : ((⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ)) ∧ (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](~ₐσ))) → (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](⊥ₐ)) := λ h => h₃ (IntroConj' h);
  sorry

end

section ProvablilityFixedPoints

@[simp] def GoedelSentence (G : Sentence α) := ⊢ₐ[T ∔ Γ] (G ⇔ₐ ~ₐPr[T ∔ Γ](G))

lemma existsGoedelSentence {T : Arithmetic α} (Γ) [HasFixedPointTheorem T Γ] : ∃ G, GoedelSentence T Γ G := HasFixedPointTheorem.FP (λ σ => ~ₐPr[T ∔ Γ](σ))


@[simp] def HenkinSentence (H : Sentence α) := ⊢ₐ[T ∔ Γ] (H ⇔ₐ Pr[T ∔ Γ](H))

lemma existsHenkinSentence {T : Arithmetic α} {Γ} [HasFixedPointTheorem T Γ] : ∃ H, HenkinSentence T Γ H := HasFixedPointTheorem.FP (λ σ => (Pr[T ∔ Γ](σ)))


@[simp] def JeroslowSentence (J : Sentence α) := ⊢ₐ[T ∔ Γ] (J ⇔ₐ Pr[T ∔ Γ](~ₐJ))

@[simp] def NotJeroslowSentence (NJ : Sentence α) := ⊢ₐ[T ∔ Γ] (NJ ⇔ₐ ~ₐPr[T ∔ Γ](~ₐNJ))


@[simp] def KreiselSentence (σ : Sentence α) (K : Sentence α) := ⊢ₐ[T ∔ Γ] (K ⇔ₐ (Pr[T ∔ Γ](K) ⇒ₐ σ))

lemma existsKreiselSentence {T : Arithmetic α} {Γ} [HasFixedPointTheorem T Γ] (σ) : ∃ K, KreiselSentence T Γ σ K := HasFixedPointTheorem.FP (λ π => (Pr[T ∔ Γ](π) ⇒ₐ σ))

end ProvablilityFixedPoints

end Arithmetic

end ModalLogic.Arithmetic