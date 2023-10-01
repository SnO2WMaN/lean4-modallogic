import Aesop
import Mathlib.Logic.Basic
import ModalLogic.Normal.Notation

namespace ModalLogic.Incompleteness

inductive ArithmeticFormula (α : Type u) : Type u
| contradiction : ArithmeticFormula α
| imply : ArithmeticFormula α → ArithmeticFormula α → ArithmeticFormula α
deriving DecidableEq, Repr

notation "⊥ₐ" => ArithmeticFormula.contradiction
infixr:43 " ⇒ₐ " => ArithmeticFormula.imply

variable (σ π : ArithmeticFormula α)

@[simp] def ArithmeticFormula.neg := σ ⇒ₐ ⊥ₐ
prefix:45 "~ₐ" => ArithmeticFormula.neg

@[simp] def ArithmeticFormula.disj := ~ₐσ ⇒ₐ π
infixl:44 " ⋎ₐ " => ArithmeticFormula.disj

@[simp] def ArithmeticFormula.conj := ~ₐσ ⋎ₐ ~ₐπ
infixl:44 " ⋏ₐ " => ArithmeticFormula.conj

@[simp] def ArithmeticFormula.iff := (σ ⇒ₐ π) ⋏ₐ (π ⇒ₐ σ)
infixl:42 " ⇔ₐ " => ArithmeticFormula.iff

structure Arithmetic (α) where
  bew : ArithmeticFormula α → ArithmeticFormula α
  Provable : ArithmeticFormula α → Prop
  ax1 (σ π) : Provable (σ ⇒ₐ (π ⇒ₐ σ))
  ax2 (σ π ρ) : Provable ((σ ⇒ₐ (π ⇒ₐ ρ)) ⇒ₐ ((σ ⇒ₐ π) ⇒ₐ (σ ⇒ₐ ρ)))
  ax3 (σ π) : Provable ((~ₐσ ⇒ₐ ~ₐπ) ⇒ₐ (π ⇒ₐ σ))
  mpₐ {σ π} : Provable (σ ⇒ₐ π) ↔ (Provable σ → Provable π) -- TODO: ↔ではない筈．
  -- modusponens {σ π} : (Provable (σ ⇒ₐ π)) → (Provable σ) → (Provable π)
  -- implyformalize {σ π} : (Provable σ → Provable π) → Provable (σ ⇒ₐ π)

notation:60 "Pr[" T "](" σ ")" => Arithmetic.bew T σ
notation:20 "⊢ₐ[" T "] " σ => Arithmetic.Provable T σ

namespace Arithmetic

variable (T : Arithmetic α)

@[simp] def ax1_def (σ π) : ⊢ₐ[T] σ ⇒ₐ (π ⇒ₐ σ) := T.ax1 σ π
@[simp] def ax2_def (σ π ρ) : ⊢ₐ[T] (σ ⇒ₐ (π ⇒ₐ ρ)) ⇒ₐ ((σ ⇒ₐ π) ⇒ₐ (σ ⇒ₐ ρ)) := T.ax2 σ π ρ
@[simp] def ax3_def (σ π) : ⊢ₐ[T] ((~ₐσ ⇒ₐ ~ₐπ) ⇒ₐ (π ⇒ₐ σ)) := T.ax3 σ π
@[simp] def mpₐ_def {σ π} : (⊢ₐ[T] σ ⇒ₐ π) ↔ ((⊢ₐ[T] σ) → (⊢ₐ[T] π)) := T.mpₐ
-- @[simp] def modusponens_def {σ π} : (⊢ₐ[T] (σ ⇒ₐ π)) → (⊢ₐ[T] σ) → (⊢ₐ[T] π) := T.modusponens

def Unprovable (σ : ArithmeticFormula α) := ¬(⊢ₐ[T] σ)
notation:20 "⊬ₐ[" T "] " σ  => Arithmetic.Unprovable T σ

section
  open Arithmetic ArithmeticFormula
  variable {T : Arithmetic α} {σ π ρ : ArithmeticFormula α} [DecidableEq (ArithmeticFormula α)]

  -- lemma impₐ_intro : (⊢ₐ[T] π) → (⊢ₐ[T] σ ⇒ₐ π) := (modusponens T (ax1 T π σ))

  -- lemma iff_dneₐ : (⊢ₐ[T] σ) ↔ (⊢ₐ[T] ~ₐ~ₐσ) := by
  --   apply Iff.intro;
  --   . intro h;
  --     simp [neg];
  --     
  --   . intro h;
  --     simp [neg] at h;
  --     have h₁ := (@deduction _ T (σ ⇒ₐ ⊥ₐ) ⊥ₐ).mp h;
  --     have h₂ := (@deduction _ T σ ⊥ₐ).mp;
  --     -- have h₃ := peirce (⊢ₐ[T] σ ⇒ₐ ⊥ₐ) (⊢ₐ[T] ⊥ₐ);
  --     -- exact impₐ_intro (impₐ_elim (@ax3 _ T (~ₐσ) σ h));


  abbrev Context (α) := Finset (ArithmeticFormula α)
  instance : Coe (ArithmeticFormula α) (Context α) := ⟨λ σ => {σ}⟩

  def ContextualProvable (T) (Γ : Context α) (σ : ArithmeticFormula α) := (⊢ₐ[T] σ) ∨ (∃ π ∈ Γ, (⊢ₐ[T] π ⇒ₐ σ) ∧ (⊢ₐ[T] π))
  notation Γ " ⊢ₐ[" T "] " σ => Arithmetic.ContextualProvable T Γ σ
  
  instance : Coe (⊢ₐ[T] σ) (Γ ⊢ₐ[T] σ) := ⟨λ h => Or.intro_left _ h⟩
  
  lemma ContextualProvable.weakening {Γ Δ : Context α} {σ : ArithmeticFormula α} : (Γ ⊆ Δ) → (Γ ⊢ₐ[T] σ) → (Δ ⊢ₐ[T] σ) := by
    intro h₁ h₂;
    cases h₂ with
    | inl h₂ => exact Or.intro_left _ (by aesop);
    | inr h₂ => exact Or.intro_right _ (by aesop);


  @[simp]
  lemma ContextualProvable.deduction {T : Arithmetic α} {Γ : Context α} {σ π : ArithmeticFormula α} : ((Γ ∪ {π}) ⊢ₐ[T] σ) ↔ (Γ ⊢ₐ[T] π ⇒ₐ σ) := by 
    apply Iff.intro;
    . intro h;
      sorry
      -- exact deduction.mp h;
    . intro h;
      cases h with
      | inl h => 
        sorry
      | inr h => 
        match h with
        | ⟨ρ, _, h₂, h₃⟩ => 
          simp [mpₐ] at h₂;
          have h₄ := h₂ h₃;
          rw [←mpₐ] at h₄;
          sorry
          -- exact deduction.mpr h₄;

  lemma ContextualProvable.Provable {T : Arithmetic α} {Γ : Context α} {σ : ArithmeticFormula α} : (Γ ⊢ₐ[T] σ) → (⊢ₐ[T] σ) := by
    intro h;
    cases h with
    | inl h => exact h;
    | inr h => 
      match h with
      | ⟨π, _, h₂, h₃⟩ => simp [mpₐ] at h₂; exact h₂ h₃;

  open ContextualProvable

  lemma idₐ : (⊢ₐ[T] σ ⇒ₐ σ) := by simp [mpₐ];

  lemma impₐ_trans : (⊢ₐ[T] σ ⇒ₐ π) → (⊢ₐ[T] π ⇒ₐ ρ) → (⊢ₐ[T] σ ⇒ₐ ρ) := by aesop;

  lemma excludeMiddleₐ : (⊢ₐ[T] σ ⋎ₐ ~ₐσ) := by simp [disj, neg, mpₐ];

  @[simp]
  lemma inst_dneₐ : (⊢ₐ[T] σ) → (⊢ₐ[T] ~ₐ~ₐσ) := by aesop;
  
  @[simp]
  lemma elim_dneₐ : (⊢ₐ[T] ~ₐ~ₐσ) → (⊢ₐ[T] σ) := by sorry;

  lemma iff_dneₐ : (⊢ₐ[T] σ) ↔ (⊢ₐ[T] ~ₐ~ₐσ) := ⟨inst_dneₐ, elim_dneₐ⟩

  @[simp]
  lemma contraposeₐ : (⊢ₐ[T] σ ⇒ₐ π) ↔ (⊢ₐ[T] (~ₐπ) ⇒ₐ (~ₐσ)) := by
    apply Iff.intro;
    . aesop;
    . exact λ h => (mpₐ _).mp (ax3 _ _ _) h;

  lemma explosionₐ (σ) : (⊢ₐ[T] ⊥ₐ ⇒ₐ σ) := by aesop;
      
  lemma impₐ_iff_dneₐ_impₐ : (⊢ₐ[T] σ ⇒ₐ π) ↔ (⊢ₐ[T] ~ₐ~ₐσ ⇒ₐ ~ₐ~ₐπ) := by
    apply Iff.intro;
    . intro h; exact contraposeₐ.mp (contraposeₐ.mp h);
    . intro h; exact contraposeₐ.mpr (contraposeₐ.mpr h);
    
  lemma impₐ_intro_con (σ) : (⊢ₐ[T] π) → (⊢ₐ[T] σ ⇒ₐ π) := by aesop

  lemma elim_impₐ_ant_dneₐ : (⊢ₐ[T] ~ₐ~ₐσ ⇒ₐ π) → (⊢ₐ[T] σ ⇒ₐ π) := by aesop;

  lemma elim_impₐ_con_dneₐ : (⊢ₐ[T] σ ⇒ₐ ~ₐ~ₐπ) → (⊢ₐ[T] σ ⇒ₐ π) := by
    intro h;
    have h₁ := (mpₐ _).mp h;
    rw [←iff_dneₐ] at h₁;
    aesop;

  axiom disj_eq_disj : (⊢ₐ[T] σ ⋎ₐ π) ↔ ((⊢ₐ[T] σ) ∨ (⊢ₐ[T] π))

  @[simp]
  lemma conjₐ_eq_conj : (⊢ₐ[T] σ ⋏ₐ π) ↔ ((⊢ₐ[T] σ) ∧ (⊢ₐ[T] π)) := by
    apply Iff.intro;
    . intro h;
      -- simp [conj, disj] at h;
      -- have h₁ := (mpₐ _).mp h;
      sorry
    . intro h;
      sorry
    
  axiom nonContradictionₐ : (⊢ₐ[T] ~ₐ(σ ⋏ₐ ~ₐσ))

  lemma intro_conjₐ : (⊢ₐ[T] σ) → (⊢ₐ[T] π) → (⊢ₐ[T] σ ⋏ₐ π) := by 
    intro h₁ h₂;
    simp only [conjₐ_eq_conj];
    exact ⟨h₁, h₂⟩;

  lemma conjₐ_left : (⊢ₐ[T] σ ⋏ₐ π) → (⊢ₐ[T] σ) := λ h => (conjₐ_eq_conj.mp h).left

  lemma conjₐ_right : (⊢ₐ[T] σ ⋏ₐ π) → (⊢ₐ[T] π) := λ h => (conjₐ_eq_conj.mp h).right

  @[simp]
  axiom conjₐ_comm : (⊢ₐ[T] σ ⋏ₐ π) ↔ (⊢ₐ[T] π ⋏ₐ σ)

  axiom conjₐ_elim_left : (⊢ₐ[T] σ ⋏ₐ π) → (⊢ₐ[T] σ ⇒ₐ π) → (⊢ₐ[T] σ)

  lemma conjₐ_elim_right : (⊢ₐ[T] σ ⋏ₐ π) → (⊢ₐ[T] π ⇒ₐ σ) → (⊢ₐ[T] π) := λ h₁ h₂ => conjₐ_elim_left (conjₐ_comm.mp h₁) h₂
  
  axiom conjₐ_contract : (⊢ₐ[T] σ ⋏ₐ σ) ↔ (⊢ₐ[T] σ)

  lemma elim_impₐ_ant_conjₐ_left : (⊢ₐ[T] (σ ⋏ₐ π) ⇒ₐ ρ) → (⊢ₐ[T] σ ⇒ₐ π) → (⊢ₐ[T] σ ⇒ₐ ρ) := by 
    intro h₁ h₂;
    have h₃ := (mpₐ _).mp h₁;
    have h₄ := λ hm => by
      have H1 := h₃ hm;
      have H2 := conjₐ_elim_left hm h₂;
      exact H2;
    sorry;
  
  lemma elim_impₐ_ant_conjₐ_right : (⊢ₐ[T] (σ ⋏ₐ π) ⇒ₐ ρ) → (⊢ₐ[T] π ⇒ₐ σ) → (⊢ₐ[T] π ⇒ₐ ρ) := by sorry
    /-
    intro h₁ h₂;
    have h₃ := (mpₐ _).mp h₁;
    rw [conjₐ_comm] at h₃;
    -/

  @[simp]
  lemma iffₐ_eq_iff : (⊢ₐ[T] σ ⇔ₐ π) ↔ ((⊢ₐ[T] σ) ↔ (⊢ₐ[T] π)) := by simp only [iff, conjₐ_eq_conj]; aesop;

  lemma intro_iffₐ : (⊢ₐ[T] σ ⇒ₐ π) → (⊢ₐ[T] π ⇒ₐ σ) → (⊢ₐ[T] σ ⇔ₐ π) := λ h₁ h₂ => intro_conjₐ h₁ h₂

  @[simp] 
  lemma iffₐ_comm : (⊢ₐ[T] σ ⇔ₐ π) ↔ (⊢ₐ[T] π ⇔ₐ σ) := by aesop;

  lemma iffₐ_mp : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] σ ⇒ₐ π) := λ h => (mpₐ _).mpr (iffₐ_eq_iff.mp h).mp
  lemma iffₐ_mpr : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] π ⇒ₐ σ) := λ h => iffₐ_mp (iffₐ_comm.mp h)

  lemma iffₐ_negₐ : (⊢ₐ[T] σ ⇔ₐ π) ↔ (⊢ₐ[T] ~ₐσ ⇔ₐ ~ₐπ) := by
    simp only [iff, conjₐ_eq_conj];
    apply Iff.intro
    . intro h; exact ⟨contraposeₐ.mp h.right, contraposeₐ.mp h.left⟩;
    . intro h; exact ⟨contraposeₐ.mpr h.right, contraposeₐ.mpr h.left⟩;

  lemma iffₐ_right : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] σ) → (⊢ₐ[T] π) := λ h => (mpₐ _).mp (conjₐ_left h)

  lemma iffₐ_left : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] π) → (⊢ₐ[T] σ) := λ h₁ h₂ => iffₐ_right (iffₐ_comm.mp h₁) h₂

  lemma iffₐ_negₐ_right : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] ~ₐσ) → (⊢ₐ[T] ~ₐπ) := λ h₁ h₂ => iffₐ_right (iffₐ_negₐ.mp h₁) h₂
  
  lemma iffₐ_negₐ_left : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] ~ₐπ) → (⊢ₐ[T] ~ₐσ) := λ h₁ h₂ => iffₐ_left (iffₐ_negₐ.mp h₁) h₂

  lemma iffₐ_trans : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] π ⇔ₐ ρ) → (⊢ₐ[T] σ ⇔ₐ ρ) := by
    simp only [iff];
    intro h₁ h₂;
    apply intro_conjₐ;
    . exact impₐ_trans (conjₐ_left h₁) (conjₐ_left h₂);
    . exact impₐ_trans (conjₐ_right h₂) (conjₐ_right h₁);

  lemma iffₐ_intro_impₐ_left : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] σ ⇒ₐ π) := by
    intro h;
    rw [iffₐ_eq_iff] at h;
    exact (mpₐ _).mpr (Iff.mp h);

  lemma iffₐ_intro_impₐ_right : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] π ⇒ₐ σ) := λ h => iffₐ_intro_impₐ_left (iffₐ_comm.mp h)

  lemma iffₐ_unprovable_left : (⊢ₐ[T] σ ⇔ₐ π) → (⊬ₐ[T] σ) → (⊬ₐ[T] π) := by
    intro h₁ h₂;
    simp only [iffₐ_eq_iff] at h₁;
    exact (h₁.not).mp h₂;

  lemma iffₐ_unprovable_right : (⊢ₐ[T] σ ⇔ₐ π) → (⊬ₐ[T] π) → (⊬ₐ[T] σ) := λ h₁ h₂ => iffₐ_unprovable_left (iffₐ_comm.mp h₁) h₂
  
end

section ArithmeticConditions
  variable (T : Arithmetic α)

  -- Σ₁ Soundness
  def Sigma₁Soundness := ∀ σ, (⊢ₐ[T] Pr[T](σ)) → (⊢ₐ[T] σ) -- TODO: Σ₁健全性ではない．
  class IsSigma₁Sounds where Sigma₁Sounds : ∀ σ, (⊢ₐ[T] Pr[T](σ)) → (⊢ₐ[T] σ)

  class HasFixedPoint (T : Arithmetic α) where 
    hasFP (P : ArithmeticFormula α → ArithmeticFormula α) : ∃ σ, ⊢ₐ[T] (σ ⇔ₐ (P σ))

  class Incompleteness (T : Arithmetic α) where
    incompleteness : ∃ σ, (⊬ₐ[T] σ) ∧ (⊬ₐ[T] ~ₐσ)

end ArithmeticConditions

section Consistency
  variable (T : Arithmetic α)

  -- Löb style Consistent 
  @[simp] def LConsistent := (⊬ₐ[T] ⊥ₐ)
  class IsLConsistent where LConsistent : LConsistent T

  @[simp] def LInconsistent := ¬(LConsistent T)
  class IsLInconsistent where LInconsistent : LInconsistent T

  @[simp] def LConsistencyOf : ArithmeticFormula α := ~ₐPr[T](⊥ₐ)
  notation "ConL[" T "]" => Arithmetic.LConsistencyOf T

  -- Hilbert-Bernays style Consistent 
  @[simp] def HBConsistent := ∀ σ, (⊢ₐ[T] σ) → (⊬ₐ[T] ~ₐσ)
  class IsHBConsistent where HBConsistent : HBConsistent T

  @[simp] def HBInconsistent := ¬(HBConsistent T)
  class IsHBInconsistent where HBInconsistent : HBInconsistent T

  axiom HBConsistent_of_Soundness {T : Arithmetic α} : IsSigma₁Sounds T → IsHBConsistent T

  -- Gödel style Consistent 
  @[simp] def GConsistent := ∃ σ, (⊬ₐ[T] σ)
  class IsGConsistent where GConsistent : GConsistent T

  @[simp] def GInconsistent := ¬(GConsistent T)
  class IsGInconsistent where GInconsistent : GInconsistent T

end Consistency

section ProvablilityFixedPoints

  variable (T : Arithmetic α) 

  @[simp] def GoedelSentence (G : ArithmeticFormula α) := ⊢ₐ[T] (G ⇔ₐ ~ₐPr[T](G))
  class IsGoedelSentence (T : Arithmetic α) (G : ArithmeticFormula α) where 
    goedel : GoedelSentence T G
  class HasGoedelSentence where hasGoedel : ∃ G, GoedelSentence T G
  lemma HasGoedelSentence_of_HasFixedPoint {T : Arithmetic α} : HasFixedPoint T → HasGoedelSentence T := by 
    intro h;
    exact ⟨(HasFixedPoint.hasFP (λ σ => ~ₐPr[T](σ)))⟩

  @[simp] def HenkinSentence (H : ArithmeticFormula α) := ⊢ₐ[T] (H ⇔ₐ Pr[T](H))
  @[simp] def JeroslowSentence (J : ArithmeticFormula α) := ⊢ₐ[T] (J ⇔ₐ Pr[T](~ₐJ))
  @[simp] def NotJeroslowSentence (NJ : ArithmeticFormula α) := ⊢ₐ[T] (NJ ⇔ₐ ~ₐPr[T](~ₐNJ))

  @[simp] def KreiselSentence (σ : ArithmeticFormula α) (K : ArithmeticFormula α) := ⊢ₐ[T] (K ⇔ₐ (Pr[T](K) ⇒ₐ σ))
  class IsKreiselSentence (T : Arithmetic α) (σ : ArithmeticFormula α) (K : ArithmeticFormula α) where 
    kreisel : KreiselSentence T σ K
  class HasKreiselSentence where hasKriesel (σ : ArithmeticFormula α) : ∃ K, KreiselSentence T σ K 
  lemma HasKreiselSentence_of_HasFixedPoint {T : Arithmetic α} : HasFixedPoint T → HasKreiselSentence T := by 
    intro h;
    exact ⟨λ σ => HasFixedPoint.hasFP (λ π => (Pr[T](π) ⇒ₐ σ))⟩

end ProvablilityFixedPoints

section DerivabilityConditions

  class Derivability1 (T : Arithmetic α) where
    D1 {σ} : (⊢ₐ[T] σ) → (⊢ₐ[T] Pr[T](σ))
    
  attribute [simp] Derivability1.D1 

  class Derivability2 (T : Arithmetic α) where
    D2 {σ π} : ⊢ₐ[T] (Pr[T](σ ⇒ₐ π)) ⇒ₐ ((Pr[T](σ)) ⇒ₐ (Pr[T](π)))

  attribute [simp] Derivability2.D2

  lemma Derivability2.D2' {T : Arithmetic α} [Derivability2 T] : ∀ {σ π}, ⊢ₐ[T] (Pr[T](σ ⋏ₐ π)) ⇔ₐ ((Pr[T](σ)) ⋏ₐ (Pr[T](π))) := by sorry

  class Derivability3 (T : Arithmetic α) where
    D3 {σ} : ⊢ₐ[T] (Pr[T](σ)) ⇒ₐ (Pr[T](Pr[T](σ)))

  attribute [simp] Derivability3.D3 

  class FormalizedSigma₁Completeness (T : Arithmetic α) where
    FS1C : ∀ {σ}, ⊢ₐ[T] (σ ⇒ₐ Pr[T](σ)) -- TODO: Σ₁という制約がない．

  instance [FormalizedSigma₁Completeness T] : (Derivability3 T) := ⟨FormalizedSigma₁Completeness.FS1C⟩

  attribute [simp] FormalizedSigma₁Completeness.FS1C

end DerivabilityConditions

section
  variable {T U : Arithmetic α} [Derivability1 T] [Derivability2 T] [Derivability3 T] {σ π ρ : ArithmeticFormula α} 

  lemma bew_dneₐ : (⊢ₐ[T] Pr[T](σ)) ↔ (⊢ₐ[T] Pr[T](~ₐ~ₐσ)) := by
    simp [ArithmeticFormula.neg, mpₐ];
    apply Iff.intro;
    . intro h; sorry
    . intro h; sorry

  @[simp]
  lemma distribute_bew : (⊢ₐ[U] Pr[T](σ ⋏ₐ π)) ↔ (⊢ₐ[U] Pr[T](σ) ⋏ₐ Pr[T](π)) := by
    apply Iff.intro;
    . intro h;
      simp [ArithmeticFormula.conj, ArithmeticFormula.disj] at h;
      -- have h2 := (mpₐ _).mp (@hD2 (~ₐ~ₐσ) (~ₐπ)) h;
      sorry
    . intro h;
      simp [ArithmeticFormula.conj, ArithmeticFormula.disj];
      -- have h2 := (mpₐ _).mp (@hD2 (~ₐ~ₐσ) (~ₐπ))
      sorry

  lemma formalized_distibute_bew : (⊢ₐ[T] Pr[T](σ ⋏ₐ π) ⇔ₐ Pr[T](σ) ⋏ₐ Pr[T](π)) := by
    apply intro_iffₐ;
    . simp only [mpₐ]; apply distribute_bew.mp;
    . simp only [mpₐ]; apply distribute_bew.mpr;
    
end

end Arithmetic

section GoedelIT1

open Arithmetic Arithmetic Derivability1

variable [Derivability1 T]

variable {T : Arithmetic α} [Derivability1 T] 
variable {G} [hG : IsGoedelSentence T G] 

/--
  Unprovablility side of Gödel's 1st incompleteness theorem.
-/
theorem Unprovable_GoedelSentence_of_HBConsistent [hC : IsHBConsistent T] : (⊬ₐ[T] G) := by
  intro hPG;

  have h₁ : ⊢ₐ[T] Pr[T](G) := D1 hPG;
  have h₂ : ⊢ₐ[T] ~ₐG := iffₐ_negₐ_left hG.goedel (iff_dneₐ.mp h₁)

  have h₃ : ⊬ₐ[T] ~ₐG := hC.HBConsistent G hPG;

  exact h₃ h₂;

/--
  Unrefutability side of Gödel's 1st incompleteness theorem.
-/
theorem Unrefutable_GoedelSentence_of_Soundness [hS : IsSigma₁Sounds T] : (⊬ₐ[T] ~ₐG) := by
  intro hRG;
  have hC := HBConsistent_of_Soundness hS;

  have h₁ : ⊢ₐ[T] Pr[T](G) := elim_dneₐ (iffₐ_right (iffₐ_negₐ.mp hG.goedel) hRG)
  have h₂ : ⊢ₐ[T] G := hS.Sigma₁Sounds G h₁;
  have h₃ : ⊬ₐ[T] ~ₐG := hC.HBConsistent G h₂;

  exact h₃ hRG;

variable [hFP : HasFixedPoint T]
/--
  Gödel's 1st incompleteness theorem.
-/
theorem GoedelIT1 [hS : IsSigma₁Sounds T] : Incompleteness T := by
  have := HBConsistent_of_Soundness hS;
  -- have a := (HasGoedelSentence_of_HasFixedPoint hFP).hasGoedel
  exact ⟨G, Unprovable_GoedelSentence_of_HBConsistent, Unrefutable_GoedelSentence_of_Soundness⟩

end GoedelIT1

section GoedelIT2

open Arithmetic Arithmetic Derivability1 Derivability2 

variable {T : Arithmetic α} [Derivability1 T] [Derivability2 T]

lemma GoedelIT2.lem1 : ∀ (σ : ArithmeticFormula α), ⊢ₐ[T] ~ₐPr[T](σ) ⇒ₐ ConL[T] := by
  intro σ; 
  have h₁ : ⊢ₐ[T] Pr[T](⊥ₐ) ⇒ₐ Pr[T](σ) := (mpₐ T).mp D2 (D1 (explosionₐ σ));
  have h₂ : ⊢ₐ[T] ~ₐPr[T](σ) ⇒ₐ ~ₐPr[T](⊥ₐ) := contraposeₐ.mp h₁;
  exact h₂;

lemma GoedelIT2.lem2
  (U : Arithmetic α)
  (hTU : ∀ {σ}, (⊢ₐ[T] σ) → (⊢ₐ[U] σ))
  (σ : ArithmeticFormula α) : (⊢ₐ[U] ConL[T] ⇒ₐ ~ₐPr[T](σ)) ↔ (⊢ₐ[U] Pr[T](σ) ⇒ₐ Pr[T](~ₐσ)) := by
  apply Iff.intro;
  . intro H;
    have h₁ : ⊢ₐ[U] ~ₐPr[T](~ₐσ) ⇒ₐ ConL[T] := hTU (GoedelIT2.lem1 _);
    have h₂ : ⊢ₐ[U] ~ₐPr[T](~ₐσ) ⇒ₐ ~ₐPr[T](σ) := impₐ_trans h₁ H;
    exact contraposeₐ.mpr h₂;
  . intro h;
    sorry
    /-
    have h₁ : ⊢ₐ[T] σ ⋏ₐ ~ₐσ ⇒ₐ ⊥ₐ := nonContradictionₐ;
    
    have h₂ := (mpₐ _).mp (hTU ((mpₐ _).mp hD2 (hD1 h₁)));
    rw [distribute_bew] at h₂;

    have h₃ := (mpₐ _).mpr h₂;
    have h₄ : ⊢ₐ[U] Pr[T](σ) ⇒ₐ Pr[T](⊥ₐ) := by sorry;

    exact contraposeₐ.mp h₄;
    -/

variable {G : ArithmeticFormula α} [IsGoedelSentence T G] [FormalizedSigma₁Completeness T]

lemma GoedelIT2.lem3 : ⊢ₐ[T] (ConL[T] ⇒ₐ ~ₐPr[T](G)) := by
  have h₁ := contraposeₐ.mp (iffₐ_intro_impₐ_right (iffₐ_comm.mp (@IsGoedelSentence.goedel _ T G _)));
  have h₂ : ⊢ₐ[T] ~ₐG ⇒ₐ Pr[T](~ₐG) := FormalizedSigma₁Completeness.FS1C;
  have h₃ := elim_impₐ_ant_dneₐ (impₐ_trans h₁ h₂);
  exact (@GoedelIT2.lem2 _ T _ _ T (by simp) G).mpr h₃

theorem GoedelSentence_iffₐ_LConsistencyOf : (⊢ₐ[T] G ⇔ₐ ConL[T]) := by
  have h₁ :  ⊢ₐ[T] ~ₐPr[T](G) ⇒ₐ ConL[T] := GoedelIT2.lem1 G;
  have h₂ :  ⊢ₐ[T] ConL[T] ⇒ₐ ~ₐPr[T](G) := GoedelIT2.lem3;
  exact iffₐ_trans IsGoedelSentence.goedel (intro_iffₐ h₁ h₂);

/--
  Unprovability side of Gödel's 2nd incompleteness theorem.
-/
theorem Unprovable_LConsistencyOf_of_HBConsistent [hC : IsHBConsistent T] : (⊬ₐ[T] ConL[T]) := by
  have h₁ : ⊢ₐ[T] G ⇔ₐ ConL[T] := GoedelSentence_iffₐ_LConsistencyOf;
  have h₂ : ⊬ₐ[T] G := Unprovable_GoedelSentence_of_HBConsistent;
  exact iffₐ_unprovable_left h₁ h₂;

/--
  Unrefutability side of Gödel's 2nd incompleteness theorem.
-/
theorem Unrefutable_LConsistencyOf_of_Soundness [hS : IsSigma₁Sounds T] : (⊬ₐ[T] ~ₐConL[T]) := by
  have h₁ : ⊢ₐ[T] ~ₐG ⇔ₐ ~ₐConL[T] := iffₐ_negₐ.mp GoedelSentence_iffₐ_LConsistencyOf
  have h₂ : ⊬ₐ[T] ~ₐG := Unrefutable_GoedelSentence_of_Soundness;
  exact iffₐ_unprovable_left h₁ h₂

#print axioms Unrefutable_LConsistencyOf_of_Soundness

end GoedelIT2

section Loeb_without_GoedelIT2

open Arithmetic Arithmetic Derivability1 Derivability2

variable {T : Arithmetic α} [hFP : HasFixedPoint T] [Derivability1 T] [Derivability2 T] [Derivability3 T]

/--
  Proof of Löb's Theorem without Gödel's 2nd incompleteness theorem.
-/
theorem Loeb_without_GoedelIT2 {σ} : (⊢ₐ[T] σ) ↔ (⊢ₐ[T] Pr[T](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . exact λ H => impₐ_intro_con (Pr[T](σ)) H;
  . intro H;
    have ⟨K, hK⟩ := (HasKreiselSentence_of_HasFixedPoint hFP).hasKriesel σ
    have h₁ : ⊢ₐ[T] K ⇒ₐ Pr[T](K) ⇒ₐ σ := iffₐ_mp hK;
    have h₂ : ⊢ₐ[T] K ⇒ₐ Pr[T](K) := (mpₐ _).mpr D1;
    have h₃ : ⊢ₐ[T] (K ⇒ₐ Pr[T](K)) ⇒ₐ K ⇒ₐ σ := (mpₐ _).mp (ax2 _ _ _ _) h₁;
    have h₄ : ⊢ₐ[T] K ⇒ₐ σ := (mpₐ _).mp h₃ h₂;
    have h₅ : ⊢ₐ[T] Pr[T](K) ⇒ₐ Pr[T](σ) := (mpₐ _).mp D2 (D1 h₄);
    have h₆ : ⊢ₐ[T] Pr[T](K) ⇒ₐ σ := impₐ_trans h₅ H;
    have h₇ : ⊢ₐ[T] K := (iffₐ_eq_iff.mp hK).mpr h₆;
    have h₈ : ⊢ₐ[T] Pr[T](K) := Derivability1.D1 h₇;
    have h₉ : ⊢ₐ[T] σ := (mpₐ _).mp h₆ h₈;
    assumption;

#print axioms Loeb_without_GoedelIT2

lemma LInconsistent_of_Provable_LConsistencyOf : (⊢ₐ[T] ConL[T]) → (LInconsistent T) := by
  intro h₁;
  have h₂ : ⊢ₐ[T] ⊥ₐ := Loeb_without_GoedelIT2.mpr h₁;
  aesop

/--
  Another proof of unprovability side of Gödel's 2nd incompleteness theorem via Löb's Theorem.
-/
theorem Unprovable_LConsistencyOf_of_LInconsistent : (LConsistent T) → (⊬ₐ[T] ConL[T]) := by
  apply imp_not_comm.mp;
  exact λ h => LInconsistent_of_Provable_LConsistencyOf h;

end Loeb_without_GoedelIT2

end ModalLogic.Incompleteness