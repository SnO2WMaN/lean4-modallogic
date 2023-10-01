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

def ArithmeticFormula.neg := σ ⇒ₐ ⊥ₐ
prefix:45 "~ₐ" => ArithmeticFormula.neg

def ArithmeticFormula.disj := ~ₐσ ⇒ₐ π
infixl:44 " ⋎ₐ " => ArithmeticFormula.disj

def ArithmeticFormula.conj := ~ₐσ ⋎ₐ ~ₐπ
infixl:44 " ⋏ₐ " => ArithmeticFormula.conj

def ArithmeticFormula.iff := (σ ⇒ₐ π) ⋏ₐ (π ⇒ₐ σ)
infixl:42 " ⇔ₐ " => ArithmeticFormula.iff

structure Arithmetic (α) where
  bew : ArithmeticFormula α → ArithmeticFormula α
  Provable : ArithmeticFormula α → Prop
  ax1 (σ π) : Provable (σ ⇒ₐ (π ⇒ₐ σ))
  ax2 (σ π ρ) : Provable ((σ ⇒ₐ (π ⇒ₐ ρ)) ⇒ₐ ((σ ⇒ₐ π) ⇒ₐ (σ ⇒ₐ ρ)))
  ax3 (σ π) : Provable ((~ₐσ ⇒ₐ ~ₐπ) ⇒ₐ (π ⇒ₐ σ))
  mpₐ {σ π} : Provable (σ ⇒ₐ π) ↔ Provable σ → Provable π

notation:60 "Pr[" T "](" σ ")" => Arithmetic.bew T σ
notation:20 "⊢ₐ[" T "] " σ => Arithmetic.Provable T σ

namespace Arithmetic

variable (T : Arithmetic α)

def Unprovable (σ : ArithmeticFormula α) := ¬(⊢ₐ[T] σ)
notation:20 "⊬ₐ[" T "] " σ  => Arithmetic.Unprovable T σ

section
  open Arithmetic ArithmeticFormula
  variable {T : Arithmetic α} {σ π ρ : ArithmeticFormula α} [DecidableEq (ArithmeticFormula α)]

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

  lemma impₐ_trans : (⊢ₐ[T] σ ⇒ₐ π) → (⊢ₐ[T] π ⇒ₐ ρ) → (⊢ₐ[T] σ ⇒ₐ ρ) := by
    simp [mpₐ];
    intro h₁ h₂ h₃;
    exact h₂ (h₁ h₃);

  lemma excludeMiddleₐ : (⊢ₐ[T] σ ⋎ₐ ~ₐσ) := by simp [disj, neg, mpₐ];

  lemma nonContradictionₐ : (⊢ₐ[T] ~ₐ(σ ⋏ₐ ~ₐσ)) := by sorry

  lemma inst_dneₐ : (⊢ₐ[T] σ) → (⊢ₐ[T] ~ₐ~ₐσ) := by
    simp [neg, mpₐ];
    intro h₁ h₂;
    exact h₂ h₁;
  
  @[simp]
  lemma elim_dneₐ : (⊢ₐ[T] ~ₐ~ₐσ) → (⊢ₐ[T] σ) := by sorry
    -- simp [neg];
    -- intro h;
    -- simp [emptyContext] at h;
    -- have h := deduction.mpr h;

  lemma iff_dneₐ : (⊢ₐ[T] σ) ↔ (⊢ₐ[T] ~ₐ~ₐσ) := ⟨inst_dneₐ, elim_dneₐ⟩

  lemma contraposeₐ : (⊢ₐ[T] σ ⇒ₐ π) ↔ (⊢ₐ[T] (~ₐπ) ⇒ₐ (~ₐσ)) := by
    apply Iff.intro;
    . simp [neg, mpₐ];
      exact λ h₁ h₂ h => h₂ (h₁ h)
    . sorry;


  lemma explosionₐ (σ) : (⊢ₐ[T] ⊥ₐ ⇒ₐ σ) := by 
    rw [contraposeₐ];
    sorry
      
  lemma impₐ_iff_dneₐ_impₐ : (⊢ₐ[T] σ ⇒ₐ π) ↔ (⊢ₐ[T] ~ₐ~ₐσ ⇒ₐ ~ₐ~ₐπ) := by
    apply Iff.intro;
    . intro h; exact contraposeₐ.mp (contraposeₐ.mp h);
    . intro h; exact contraposeₐ.mpr (contraposeₐ.mpr h);
  axiom impₐ_intro_con (σ) : (⊢ₐ[T] π) → (⊢ₐ[T] σ ⇒ₐ π)

  lemma elim_impₐ_ant_dneₐ : (⊢ₐ[T] ~ₐ~ₐσ ⇒ₐ π) → (⊢ₐ[T] σ ⇒ₐ π) := by 
    intro h;
    have h₁ := (mpₐ _).mp h;
    rw [←iff_dneₐ] at h₁;
    exact (mpₐ T).mpr h₁;
  lemma elim_impₐ_con_dneₐ : (⊢ₐ[T] σ ⇒ₐ ~ₐ~ₐπ) → (⊢ₐ[T] σ ⇒ₐ π) := by
    intro h;
    have h₁ := (mpₐ _).mp h;
    rw [←iff_dneₐ] at h₁;
    exact (mpₐ T).mpr h₁;

  lemma disj_eq_disj : (⊢ₐ[T] σ ⋎ₐ π) ↔ ((⊢ₐ[T] σ) ∨ (⊢ₐ[T] π)) := by
    apply Iff.intro;
    . sorry
    . sorry

  lemma conjₐ_eq_conj : (⊢ₐ[T] σ ⋏ₐ π) ↔ ((⊢ₐ[T] σ) ∧ (⊢ₐ[T] π)) := by
    apply Iff.intro;
    . sorry
    . sorry

  lemma intro_conjₐ : (⊢ₐ[T] σ) → (⊢ₐ[T] π) → (⊢ₐ[T] σ ⋏ₐ π) := by 
    intro h₁ h₂;
    simp [conjₐ_eq_conj];
    exact ⟨h₁, h₂⟩;
  lemma conjₐ_left : (⊢ₐ[T] σ ⋏ₐ π) → (⊢ₐ[T] σ) := λ h => (conjₐ_eq_conj.mp h).left
  lemma conjₐ_right : (⊢ₐ[T] σ ⋏ₐ π) → (⊢ₐ[T] π) := λ h => (conjₐ_eq_conj.mp h).right
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

  lemma iffₐ_eq_iff : (⊢ₐ[T] σ ⇔ₐ π) ↔ ((⊢ₐ[T] σ) ↔ (⊢ₐ[T] π)) := by
    simp [ArithmeticFormula.iff, conjₐ_eq_conj];
    apply Iff.intro;
    . intro h;
      have hl := (mpₐ _).mp h.left;
      have hr := (mpₐ _).mp h.right;
      exact ⟨hl, hr⟩;
    . intro h;
      have hl := (mpₐ _).mpr h.mp;
      have hr := (mpₐ _).mpr h.mpr;
      exact ⟨hl, hr⟩;

  lemma intro_iffₐ : (⊢ₐ[T] σ ⇒ₐ π) → (⊢ₐ[T] π ⇒ₐ σ) → (⊢ₐ[T] σ ⇔ₐ π) := λ h₁ h₂ => intro_conjₐ h₁ h₂

  lemma iffₐ_comm : (⊢ₐ[T] σ ⇔ₐ π) ↔ (⊢ₐ[T] π ⇔ₐ σ) := by
    apply Iff.intro <;> exact λ h => iffₐ_eq_iff.mpr (Iff.comm.mp (iffₐ_eq_iff.mp h))

  lemma iffₐ_negₐ : (⊢ₐ[T] σ ⇔ₐ π) ↔ (⊢ₐ[T] ~ₐσ ⇔ₐ ~ₐπ) := by
    simp [ArithmeticFormula.iff, conjₐ_eq_conj];
    apply Iff.intro
    . intro h; exact ⟨contraposeₐ.mp h.right, contraposeₐ.mp h.left⟩;
    . intro h; exact ⟨contraposeₐ.mpr h.right, contraposeₐ.mpr h.left⟩;
    
  lemma iffₐ_right : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] σ) → (⊢ₐ[T] π) := λ h => (mpₐ _).mp (conjₐ_left h)
  lemma iffₐ_left : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] π) → (⊢ₐ[T] σ) := λ h₁ h₂ => iffₐ_right (iffₐ_comm.mp h₁) h₂
  lemma iffₐ_negₐ_right : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] ~ₐσ) → (⊢ₐ[T] ~ₐπ) := λ h₁ h₂ => iffₐ_right (iffₐ_negₐ.mp h₁) h₂
  lemma iffₐ_negₐ_left : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] ~ₐπ) → (⊢ₐ[T] ~ₐσ) := λ h₁ h₂ => iffₐ_left (iffₐ_negₐ.mp h₁) h₂

  lemma iffₐ_trans : (⊢ₐ[T] σ ⇔ₐ π) → (⊢ₐ[T] π ⇔ₐ ρ) → (⊢ₐ[T] σ ⇔ₐ ρ) := by
    simp [ArithmeticFormula.iff];
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
    simp [iffₐ_eq_iff] at h₁;
    exact (h₁.not).mp h₂;
  lemma iffₐ_unprovable_right : (⊢ₐ[T] σ ⇔ₐ π) → (⊬ₐ[T] π) → (⊬ₐ[T] σ) := λ h₁ h₂ => iffₐ_unprovable_left (iffₐ_comm.mp h₁) h₂
  
end

/-- Löb style Consistent -/
@[simp] def LConsistent := (⊬ₐ[T] ⊥ₐ)
@[simp] def LInconsistent := ¬(LConsistent T)

def LConsistencyOf : ArithmeticFormula α := ~ₐPr[T](⊥ₐ)
notation "ConL[" T "]" => Arithmetic.LConsistencyOf T

/-- Hilbert-Bernays style Consistent -/
@[simp] def HBConsistent := ∀ σ, (⊢ₐ[T] σ) → (⊬ₐ[T] ~ₐσ)
@[simp] def HBInconsistent := ¬(HBConsistent T)

/-- Gödel style Consistent -/
@[simp] def GConsistent := ∃ σ, (⊬ₐ[T] σ)
@[simp] def GInconsistent := ¬(GConsistent T)

class LConsistent_eq_HBConsistent (T : Arithmetic α) where
  L_iff_HB : LConsistent T ↔ HBConsistent T

class HBConsistent_eq_GConsistent (T : Arithmetic α) where
  HB_iff_G : LConsistent T ↔ HBConsistent T

class GConsistent_eq_LConsistent (T : Arithmetic α) where
  G_iff_L : GConsistent T ↔ LConsistent T

def Sigma₁Soundness := ∀ σ, (⊢ₐ[T] Pr[T](σ)) → (⊢ₐ[T] σ) -- TODO: Σ₁健全性ではない．
axiom HBConsistent_of_Soundness {T : Arithmetic α} : Sigma₁Soundness T → HBConsistent T

class Sigma₁Soundness₂ (T : Arithmetic α) where
  Sigma₁Sounds : ∀ σ, (⊢ₐ[T] Pr[T](σ)) → (⊢ₐ[T] σ)
axiom HBConsistent_of_Soundness₂ {T : Arithmetic α} : Sigma₁Soundness₂ T → HBConsistent T

class HasFixedPoint (T : Arithmetic α) where 
  hasFP (P : ArithmeticFormula α → ArithmeticFormula α) : ∃ σ, ⊢ₐ[T] (σ ⇔ₐ (P σ))

class Derivability1 (T : Arithmetic α) where
  D1 {σ} : (⊢ₐ[T] σ) → (⊢ₐ[T] Pr[T](σ))

class Derivability2 (T : Arithmetic α) where
  D2 {σ π} : ⊢ₐ[T] (Pr[T](σ ⇒ₐ π)) ⇒ₐ ((Pr[T](σ)) ⇒ₐ (Pr[T](π)))

lemma Derivability2.D2' {T : Arithmetic α} [Derivability2 T] : ∀ {σ π}, ⊢ₐ[T] (Pr[T](σ ⋏ₐ π)) ⇔ₐ ((Pr[T](σ)) ⋏ₐ (Pr[T](π))) := by sorry

class Derivability3 (T : Arithmetic α) where
  D3 {σ} : ⊢ₐ[T] (Pr[T](σ)) ⇒ₐ (Pr[T](Pr[T](σ)))

class FormalizedSigma₁Completeness (T : Arithmetic α) where
  FS1C : ∀ {σ}, ⊢ₐ[T] (σ ⇒ₐ Pr[T](σ)) -- TODO: Σ₁という制約がない．

lemma Derivability3_of_FormalizedSigma₁Completeness [FormalizedSigma₁Completeness T] : (Derivability3 T) := ⟨FormalizedSigma₁Completeness.FS1C⟩

class Incompleteness (T : Arithmetic α) where
  incompleteness : ∃ σ, (⊬ₐ[T] σ) ∧ (⊬ₐ[T] ~ₐσ)

section
  variable {T U : Arithmetic α} [Derivability1 T] [Derivability2 T] [Derivability3 T] {σ π ρ : ArithmeticFormula α} 

  lemma bew_dneₐ : (⊢ₐ[T] Pr[T](σ)) ↔ (⊢ₐ[T] Pr[T](~ₐ~ₐσ)) := by
    simp [ArithmeticFormula.neg, mpₐ];
    apply Iff.intro;
    . intro h; sorry
    . intro h; sorry

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
    . simp [mpₐ]; apply distribute_bew.mp;
    . simp [mpₐ]; apply distribute_bew.mpr;

end

end Arithmetic

section GoedelIT1

open Arithmetic Arithmetic Derivability1

variable [Derivability1 T]

class GoedelSentence (T : Arithmetic α) (G : ArithmeticFormula α) where 
  goedel : ⊢ₐ[T] (G ⇔ₐ ~ₐPr[T](G))

@[simp]
def GoedelSentence₂ (T : Arithmetic α) (G : ArithmeticFormula α) := ⊢ₐ[T] (G ⇔ₐ ~ₐPr[T](G))

class HasGoedelSentence (T : Arithmetic α) where
  hasGoedel : ∃ G, GoedelSentence₂ T G

instance (T : Arithmetic α) [HasFixedPoint T] : HasGoedelSentence T := ⟨(HasFixedPoint.hasFP (λ σ => ~ₐPr[T](σ)))⟩

variable {T : Arithmetic α} [HasFixedPoint T] [Derivability1 T] [GoedelSentence T G]
variable {G : ArithmeticFormula α} {hG : GoedelSentence₂ T G}

/--
  Unprovablility side of Gödel's 1st incompleteness theorem.
-/
theorem Unprovable_GoedelSentence_of_HBConsistent : HBConsistent T → (⊬ₐ[T] G) := by
  intro hC hPG;

  have h₁ : ⊢ₐ[T] Pr[T](G) := D1 hPG;
  have h₂ : ⊢ₐ[T] ~ₐG := iffₐ_negₐ_left hG (iff_dneₐ.mp h₁)

  have h₃ : ⊬ₐ[T] ~ₐG := hC G hPG;

  exact h₃ h₂;

/--
  Unrefutability side of Gödel's 1st incompleteness theorem.
-/
theorem Unrefutable_GoedelSentence_of_Soundness : Sigma₁Soundness₂ T → (⊬ₐ[T] ~ₐG) := by
  intro hS hRG;
  have hC := HBConsistent_of_Soundness₂ hS;

  have h₁ : ⊢ₐ[T] Pr[T](G) := elim_dneₐ (iffₐ_right (iffₐ_negₐ.mp hG) hRG)
  have h₂ : ⊢ₐ[T] G := hS.Sigma₁Sounds G h₁;
  have h₃ : ⊬ₐ[T] ~ₐG := hC G h₂;

  exact h₃ hRG;

variable {G : ArithmeticFormula α} [GoedelSentence T G]

/--
  Unprovablility side of Gödel's 1st incompleteness theorem.
-/
theorem Unprovable_of_HBConsistent : HBConsistent T → (⊬ₐ[T] G) := by
  intro hC hP_G;

  have hP_BG : ⊢ₐ[T] Pr[T](G) := D1 hP_G;

  have hP_nG : ⊢ₐ[T] (~ₐG) := iffₐ_negₐ_left GoedelSentence.goedel (iff_dneₐ.mp hP_BG)

  simp [HBConsistent, HBInconsistent] at hC;
  exact hC G hP_G hP_nG;

/--
  Unrefutability side of Gödel's 1st incompleteness theorem.
-/
theorem Unrefutable_of_Soundness : Sigma₁Soundness T → (⊬ₐ[T] ~ₐG) := by
  intro hS hP_nG;
  have hC := HBConsistent_of_Soundness hS;

  have hP_BG : ⊢ₐ[T] Pr[T](G) := elim_dneₐ (iffₐ_right (iffₐ_negₐ.mp GoedelSentence.goedel) hP_nG)
  
  simp [Sigma₁Soundness] at hS;
  have hP_G := hS G hP_BG;
 
  simp [HBConsistent, HBInconsistent] at hC;
  exact hC G hP_G hP_nG;

theorem GoedelIT1 : Sigma₁Soundness T → Incompleteness T := by
  intro hS;
  have h₂ :  ⊬ₐ[T] G := Unprovable_of_HBConsistent (HBConsistent_of_Soundness hS);
  have h₃ :  ⊬ₐ[T] ~ₐG := Unrefutable_of_Soundness hS;
  exact ⟨G, h₂, h₃⟩

end GoedelIT1

section GoedelIT2

open Arithmetic Arithmetic Derivability1 Derivability2 

variable {G : ArithmeticFormula α} [GoedelSentence T G] [Derivability1 T] [Derivability2 T]

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

variable [FormalizedSigma₁Completeness T]
lemma GoedelIT2.lem3 : ⊢ₐ[T] (ConL[T] ⇒ₐ ~ₐPr[T](G)) := by
  have h₁ := contraposeₐ.mp (iffₐ_intro_impₐ_right (iffₐ_comm.mp (@GoedelSentence.goedel _ T G _)));
  have h₂ : ⊢ₐ[T] ~ₐG ⇒ₐ Pr[T](~ₐG) := FormalizedSigma₁Completeness.FS1C;
  have h₃ := elim_impₐ_ant_dneₐ (impₐ_trans h₁ h₂);
  exact (@GoedelIT2.lem2 _ T _ _ T (by simp) G).mpr h₃

theorem GoedelSentence_iffₐ_LConsistencyOf : (⊢ₐ[T] G ⇔ₐ ConL[T]) := by
  have h₁ :  ⊢ₐ[T] ~ₐPr[T](G) ⇒ₐ ConL[T] := GoedelIT2.lem1 G;
  have h₂ :  ⊢ₐ[T] ConL[T] ⇒ₐ ~ₐPr[T](G) := GoedelIT2.lem3;
  exact iffₐ_trans GoedelSentence.goedel (intro_iffₐ h₁ h₂);

/--
  Unprovability side of Gödel's 2nd incompleteness theorem.
-/
theorem Unprovable_LConsistencyOf_of_HBConsistent : HBConsistent T → (⊬ₐ[T] ConL[T]) := by
  intro hC;
  have h₁ : ⊢ₐ[T] G ⇔ₐ ConL[T] := GoedelSentence_iffₐ_LConsistencyOf;
  have h₂ : ⊬ₐ[T] G := Unprovable_of_HBConsistent hC;
  exact iffₐ_unprovable_left h₁ h₂;

/--
  Unrefutability side of Gödel's 2nd incompleteness theorem.
-/
theorem Unrefutable_LConsistencyOf_of_Soundness : Sigma₁Soundness T → (⊬ₐ[T] ~ₐConL[T]) := by
  intro hS;
  have h₁ : ⊢ₐ[T] ~ₐG ⇔ₐ ~ₐConL[T] := iffₐ_negₐ.mp GoedelSentence_iffₐ_LConsistencyOf
  have h₂ : ⊬ₐ[T] ~ₐG := Unrefutable_of_Soundness hS;
  exact iffₐ_unprovable_left h₁ h₂

#print axioms Unrefutable_LConsistencyOf_of_Soundness

end GoedelIT2

/-
section Loeb_without_GoedelIT2

variable [HasFixedPoint T] [Derivability1 T] [Derivability2 T] [Derivability3 T]
theorem Loeb_with_GoedelIt2 {σ} : (⊢ₐ[T] σ) ↔ (⊢ₐ[T] Pr[T](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . exact λ H => impₐ_intro_con (Pr[T](σ)) H;
  . intro H;
    have h₁ := contraposeₐ.mp H;
    have h₂ := (@Derivability2.D2' _ T _ (~ₐσ) ⊥ₐ);
    have h₂₁ := contraposeₐ.mp h₂;

end Loeb_without_GoedelIT2
-/

section Loeb_without_GoedelIT2

open Arithmetic Arithmetic Derivability1 Derivability2

variable {T : Arithmetic α} [HasFixedPoint T] 

axiom KrieselSentence (T : Arithmetic α) (σ : ArithmeticFormula α) : ∃ K, ⊢ₐ[T] (K ⇔ₐ (Pr[T](K) ⇒ₐ σ))
-- def KrieselSentence₂ (T : Arithmetic α) [HasFixedPoint T] (σ : ArithmeticFormula α) := @HasFixedPoint.hasFP _ T _ (λ π => (Pr[T](π) ⇒ₐ σ))

def KreiselSentence₂ (T : Arithmetic α) (σ : ArithmeticFormula α) (K : ArithmeticFormula α) := ⊢ₐ[T] (K ⇔ₐ (Pr[T](K) ⇒ₐ σ))

class HasKreiselSentence (T : Arithmetic α) where 
  hasKriesel (σ : ArithmeticFormula α) : ∃ K, KreiselSentence₂ T σ K 

instance (T : Arithmetic α) [HasFixedPoint T] : HasKreiselSentence T := ⟨λ σ => HasFixedPoint.hasFP (λ π => (Pr[T](π) ⇒ₐ σ))⟩

variable [HasFixedPoint T] [Derivability1 T] [Derivability2 T] [Derivability3 T]

/--
  Proof of Löb's Theorem without Gödel's 2nd incompleteness theorem.
-/
theorem Loeb_without_GoedelIT2 {σ} : (⊢ₐ[T] σ) ↔ (⊢ₐ[T] Pr[T](σ) ⇒ₐ σ) := by
  apply Iff.intro;
  . exact λ H => impₐ_intro_con (Pr[T](σ)) H;
  . intro H;
    -- have a : ⊢ₐ[T] K ⇔ₐ Pr[T](K) ⇒ₐ σ := KreiselSentence₂.kreisel
    have ⟨K, hK⟩ := KrieselSentence T σ; 
    have h₁ : ⊢ₐ[T] Pr[T](K) ⇒ₐ Pr[T](Pr[T](K) ⇒ₐ σ) := by
      have hK' := iffₐ_eq_iff.mp hK;
      
      -- have hK'l := hK'.mp;
      -- have hK'r := hK'.mpr;
      
      have h₁l : (⊢ₐ[T] K) → (⊢ₐ[T] Pr[T](K)) := Derivability1.D1;
      have h₁r : (⊢ₐ[T] (Pr[T](K) ⇒ₐ σ)) → (⊢ₐ[T] Pr[T](Pr[T](K) ⇒ₐ σ)) := Derivability1.D1;



      -- have h₁r := (iffₐ_eq_iff.mp hK).mp;
      -- have h2 := λ h => h₁l (h₁r h);
      
      -- have hKl := hK'.mp;
      -- have hkr := hK'.mpr;

      sorry
    have h₂ : ⊢ₐ[T] Pr[T](K) ⇒ₐ (Pr[T](Pr[T](K)) ⇒ₐ Pr[T](σ)) := impₐ_trans h₁ Derivability2.D2;
    have h₃ : ⊢ₐ[T] Pr[T](K) ⇒ₐ Pr[T](σ) := by
      have h₃₁ := @Derivability3.D3 _ T _ K;
      have h₃₂ := (mpₐ _).mp h₂;
      -- have h₃₂ := impₐ_trans h₃₁ h₂;
      sorry
    have h₄ : ⊢ₐ[T] Pr[T](K) ⇒ₐ σ := impₐ_trans h₃ H;
    have h₅ : ⊢ₐ[T] K := (iffₐ_eq_iff.mp hK).mpr h₄;
    have h₆ : ⊢ₐ[T] Pr[T](K) := Derivability1.D1 h₅;
    have h₇ : ⊢ₐ[T] σ := (mpₐ _).mp h₄ h₆;
    exact h₇;

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