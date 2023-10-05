import ModalLogic.PropositionalLogic.DeductionSystem

open ModalLogic.PropositionalLogic DeductionSystem

namespace ModalLogic.Arithmetic

inductive Sentence (α : Type u)
| Contradiction : Sentence α
| Imply : Sentence α → Sentence α → Sentence α
deriving DecidableEq, Repr

notation "⊥ₐ" => Sentence.Contradiction
infixl:63 " ⇒ₐ " => Sentence.Imply

namespace Sentence

instance : HasBot (Sentence α) := ⟨Contradiction⟩
instance : HasImply (Sentence α) := ⟨Imply⟩

variable (φ ψ : Sentence α)

@[simp] def Neg := φ ⇒ₐ ⊥ₐ
prefix:70 "~ₐ" => Neg
instance : HasNeg (Sentence α) := ⟨Neg⟩

@[simp] def def_Neg : φ ⇒ₐ ⊥ₐ = ~ₐφ := rfl
instance : HasNegDef (Sentence α) := ⟨def_Neg⟩

@[simp] def Disj := (~ₐφ) ⇒ₐ ψ
infixl:64 " ⋎ₐ " => Disj
instance : HasDisj (Sentence α) := ⟨Disj⟩

@[simp] def def_Disj : (~ₐφ) ⇒ₐ ψ = φ ⋎ₐ ψ := rfl
instance : HasDisjDef (Sentence α) := ⟨def_Disj⟩

@[simp] def Conj := ~ₐ(φ ⇒ ~ψ)
infixl:65 " ⋏ₐ " => Conj
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

variable [DecidableEq α]

structure Arithmetic (α) extends DeductionSystem (Sentence α) where 
  Provable : (Context (Sentence α)) → (Sentence α) → (Sentence α)

notation "Pr[" T " ∔ " Γ "](" σ ")" => Arithmetic.Provable T Γ σ
notation "Pr[" T "](" σ ")" => Pr[T ∔ ∅](σ)

def Arithmetic.Proves_def (T : Arithmetic α) (σ : Sentence α) := T.Proves σ

def Arithmetic.Deducible_def (T : Arithmetic α) (Γ σ) := T.Deducts Γ σ

notation:20 "⊢ₐ[" T " ∔ " Γ "] " σ => Arithmetic.Deducible_def T Γ σ
notation:20 "⊬ₐ[" T " ∔ " Γ "] " σ => ¬(Arithmetic.Deducible_def T Γ σ)

notation:20 "⊢ₐ[" T "] " σ => Arithmetic.Deducible_def T ∅ σ
notation:20 "⊬ₐ[" T "] " σ => ¬(⊢ₐ[T] σ)

-- notation:20 "⊢ₐ[" T "] " σ => Arithmetic.Proves_def T σ 

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

lemma HasFormalDeductionTheorem.FDT_neg {T : Arithmetic α} {Γ Δ} [HasMP T.toDeductionSystem] [HasDT T.toDeductionSystem] [HasFormalDeductionTheorem T Γ Δ] {σ π} 
  : (⊢ₐ[T ∔ Δ] ~ₐPr[T ∔ Γ](σ ⇒ₐ π) ⇔ₐ ~ₐPr[T ∔ Γ ∪ {σ}](π)) := by
  suffices (⊢ₐ[T ∔ Δ] Pr[T ∔ Γ](σ ⇒ₐ π) ⇔ₐ Pr[T ∔ Γ ∪ {σ}](π)) from by exact T.deducible_equiv_neg this;
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
  D1  : ∀ {σ}, (⊢ₐ[T ∔ Γ] σ) → (⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](σ)))

class Derivability2 extends Arithmetic α where
  D2 : ∀ {σ π}, ⊢ₐ[T ∔ Γ] (Pr[T ∔ Γ](σ ⇒ₐ π) ⇒ₐ (Pr[T ∔ Γ](σ) ⇒ₐ Pr[T ∔ Γ](π)))

class Derivability3 extends Arithmetic α where
  D3 : ∀ {σ}, ⊢ₐ[T ∔ Γ] ((Pr[T ∔ Γ](σ)) ⇒ₐ Pr[T ∔ Γ](Pr[T ∔ Γ](σ)))

class FormalizedSigma1Completeness extends Arithmetic α where
  FS1C : ∀ {σ}, ⊢ₐ[T ∔ Γ] (σ ⇒ₐ Pr[T ∔ Γ](σ))

lemma pr_negneg_intro {T : Arithmetic α} [HasMP T.toDeductionSystem] {Γ} [Derivability2 T Γ] {σ} : (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Γ] Pr[T ∔ Γ](~ₐ~ₐσ)) := by
  intro H;
  sorry

lemma not_pr_negneg_intro {T : Arithmetic α} [HasMP T.toDeductionSystem] {Γ} [Derivability2 T Γ] {σ} : (⊢ₐ[T ∔ Γ] ~ₐPr[T ∔ Γ](σ)) → (⊢ₐ[T ∔ Γ] ~ₐPr[T ∔ Γ](~ₐ~ₐσ)) := by
  intro H;
  sorry

@[simp] def GoedelSentence (G : Sentence α) := ⊢ₐ[T ∔ Γ] (G ⇔ₐ ~ₐPr[T ∔ Γ](G))

class HasGoedelSentence extends Arithmetic α where 
  hasGoedel : ∃ G, GoedelSentence T Γ G

def existsGoedelSentence {T : Arithmetic α} (Γ) [HasGoedelSentence T Γ] : ∃ G, GoedelSentence T Γ G := HasGoedelSentence.hasGoedel

/-
lemma HasGoedelSentence_of_HasFixedPointTheorem {T : Arithmetic α} : HasFixedPointTheorem T → HasGoedelSentence T := by 
  intro h;
  exact ⟨(HasFixedPointTheorem.FP (λ σ => ~ₐPr[T](σ)))⟩
-/

@[simp] def HenkinSentence (H : Sentence α) := ⊢ₐ[T ∔ Γ] (H ⇔ₐ Pr[T ∔ Γ](H))

class HasHenkinSentence where 
  hasHenkin : ∃ H, HenkinSentence T Γ H

@[simp] def JeroslowSentence (J : Sentence α) := ⊢ₐ[T ∔ Γ] (J ⇔ₐ Pr[T ∔ Γ](~ₐJ))

@[simp] def NotJeroslowSentence (NJ : Sentence α) := ⊢ₐ[T ∔ Γ] (NJ ⇔ₐ ~ₐPr[T ∔ Γ](~ₐNJ))

@[simp] def KreiselSentence (σ : Sentence α) (K : Sentence α) := ⊢ₐ[T ∔ Γ] (K ⇔ₐ (Pr[T ∔ Γ](K) ⇒ₐ σ))

class HasKreiselSentence extends Arithmetic α where 
  hasKriesel (σ : Sentence α) : ∃ K, KreiselSentence T Γ σ K 
  
def existsKreiselSentence {T : Arithmetic α} (Γ) [HasKreiselSentence T Γ] : ∀ (σ : Sentence α), ∃ (K : Sentence α), KreiselSentence T Γ σ K := HasKreiselSentence.hasKriesel

/-
lemma HasKreiselSentence_of_HasFixedPointTheorem {T : Arithmetic α} : HasFixedPointTheorem T → HasKreiselSentence T := by 
  intro h;
  exact ⟨λ σ => HasFixedPointTheorem.FP (λ π => (Pr[T](π) ⇒ₐ σ))⟩
-/

end Arithmetic

end ModalLogic.Arithmetic