import Aesop
import Mathlib.Data.Finset.Basic
import ModalLogic.PropositionalLogic.Notation
import ModalLogic.PropositionalLogic.Axioms

open Finset 
attribute [simp] union_comm insert_eq

open ModalLogic.PropositionalLogic

namespace ModalLogic.PropositionalLogic

abbrev Context (α) := Finset α

structure DeductionSystem (α) extends ProveSystem α where
  Deducts: Context α → α → Prop
  NoContext : (Deducts ∅ φ) ↔ (Proves φ)
  inContext : ∀ {Γ φ}, (φ ∈ Γ) → (Deducts Γ φ)

namespace DeductionSystem

notation Γ " ⊢ᵈ[" D "] " φ => DeductionSystem.Deducts D Γ φ 
notation Γ " ⊬ᵈ[" D "] " φ => ¬(Γ ⊢ᵈ[D] φ)
notation "⊢ᵈ[" D "] " φ => ⊢[toProveSystem D] φ
notation "⊬ᵈ[" D "] " φ => ¬(⊢ᵈ[D] φ)

variable {α : Type u} [DecidableEq α] 
variable (D : DeductionSystem α)

@[simp] 
lemma toProves_def : (∅ ⊢ᵈ[D] φ) → (⊢ᵈ[D] φ) := by apply (NoContext D).mp

@[simp] lemma inContext_def : (φ ∈ Γ) → (Γ ⊢ᵈ[D] φ) := by apply inContext

@[simp]
axiom fromProves {Γ D} {φ : α}: (⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] φ)

instance Coe : Coe (⊢ᵈ[D] φ) (Γ ⊢ᵈ[D] φ) := ⟨fromProves⟩

variable [HasImply α] in
class HasDT where
  DT {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) ↔ ((Γ ∪ {φ}) ⊢ᵈ[D] ψ)
attribute [simp] HasDT.DT

variable [HasImply α] in
class HasMP where
  MP {φ ψ : α} : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) → (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] ψ)
attribute [simp] HasMP.MP

variable [HasImply α] [HasBot α] in
class HasExplode where
  Explode (φ : α) : (Γ ⊢ᵈ[D] ⊥) → (Γ ⊢ᵈ[D] φ)
attribute [simp] HasExplode.Explode

variable [HasImply α] [HasNeg α] in
class HasDNElim where
  DNElim {φ : α} : (Γ ⊢ᵈ[D] ~~φ) → (Γ ⊢ᵈ[D] φ)
attribute [simp] HasDNElim.DNElim

@[simp] lemma trivial_context (φ : α) : {φ} ⊢ᵈ[D] φ := by aesop;

open HasDT HasMP HasExplode HasDNElim

variable [HasImply α] [HasBot α] [HasNeg α] [HasNegDef α]
variable {D}
variable [HasDT D] [HasMP D] 

@[simp]
lemma deducible_equality : ⊢ᵈ[D] φ ⇒ φ := by aesop;

@[simp]
lemma deducible_MP : (⊢ᵈ[D] (φ ⇒ ψ)) → (⊢ᵈ[D] φ) → (⊢ᵈ[D] ψ) := by
  intro H₁ H₂;
  have H₂ : ∅ ⊢ᵈ[D] φ := H₂;
  apply toProves_def;
  exact MP H₁ H₂;

lemma deducible_K : ⊢ᵈ[D] (Axioms.K φ ψ) := by
  repeat apply DT.mpr;
  simp;

lemma deducible_S : ⊢ᵈ[D] (Axioms.S φ ψ ξ) := by
  repeat apply DT.mpr;
  have h₁ : ({φ ⇒ ψ ⇒ ξ} ∪ ({φ ⇒ ψ, φ})) ⊢ᵈ[D] φ := by simp;
  have h₂ : ({φ ⇒ ψ ⇒ ξ} ∪ ({φ ⇒ ψ, φ})) ⊢ᵈ[D] φ ⇒ ψ := by simp;
  have h₃ : ({φ ⇒ ψ ⇒ ξ} ∪ ({φ ⇒ ψ, φ})) ⊢ᵈ[D] φ ⇒ ψ ⇒ ξ := by simp;
  have h₄ := MP h₂ h₁;
  have h₅ := MP h₃ h₁;
  have h₆ := MP h₅ h₄;
  aesop;

/-
lemma deducible_Con₄ : ⊢ᵈ[D] (Axioms.Con₄ φ ψ) := by
  repeat apply DT.mpr;
  have h₁ : ({φ ⇒ ψ, ψ ⇒ ⊥, φ}) ⊢[D] φ := by simp;
  have h₂ : ({φ ⇒ ψ, ψ ⇒ ⊥, φ}) ⊢[D] φ ⇒ ψ := by simp;
  have h₃ : ({φ ⇒ ψ, ψ ⇒ ⊥, φ}) ⊢[D] ψ ⇒ ⊥ := by simp;
  have h₄ := MP h₂ h₁;
  have h₅ := MP h₃ h₄;
  aesop;
-/

@[simp]
lemma deducible_DNI : ⊢ᵈ[D] (Axioms.DNI φ) := by
  simp;
  apply toProves_def;
  repeat apply DT.mpr;
  have h₁ : ({φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : ({φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ ⇒ ⊥ := by simp;
  have h₃ := MP h₂ h₁;
  aesop;


lemma deducible_imply_trans : ((⊢ᵈ[D] (φ ⇒ ψ)) ∧ (⊢ᵈ[D] (ψ ⇒ ξ))) → (⊢ᵈ[D] (φ ⇒ ξ)) := by
  intro H₁;
  have H₁l : ∅ ⊢ᵈ[D] φ ⇒ ψ := (H₁.left);
  have H₁r : ∅ ⊢ᵈ[D] ψ ⇒ ξ := (H₁.right);

  have H₁l := MP H₁l;
  have H₁r := MP H₁r;

  have H₂l := λ h => H₁r (H₁l h);

  sorry;

lemma deducible_contrapose₁ : (⊢ᵈ[D] (φ ⇒ ψ)) → (⊢ᵈ[D] (~ψ ⇒ ~φ)) := by
  intro H₁;
  simp [HasNegDef.NegDef];
  
  apply toProves_def;
  repeat apply DT.mpr;

  have H₁ : ({ψ ⇒ ⊥, φ}) ⊢ᵈ[D] φ ⇒ ψ := H₁;
  have h₁ : ({ψ ⇒ ⊥, φ}) ⊢ᵈ[D] ψ ⇒ ⊥ := by simp;
  have h₂ : ({ψ ⇒ ⊥, φ}) ⊢ᵈ[D] φ := by simp;
  have h₃ := MP H₁ h₂;
  have h₄ := MP h₁ h₃;
  aesop;

lemma deducible_contrapose₂ : (⊢ᵈ[D] (φ ⇒ ~ψ)) → (⊢ᵈ[D] (ψ ⇒ ~φ)) := by
  intro H₁;
  simp [HasNegDef.NegDef];
  
  apply toProves_def;
  repeat apply DT.mpr;

  have H₁ : ({φ, ψ}) ⊢ᵈ[D] φ ⇒ ~ψ := H₁;
  have h₁ : ({φ, ψ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : ({φ, ψ}) ⊢ᵈ[D] ψ := by simp;
  have h₃ := MP H₁ h₁;
  simp only [HasNegDef.NegDef] at h₃;
  have h₄ := MP h₃ h₂;
  aesop;

lemma deducible_negneg_intro : (⊢ᵈ[D] (φ)) → (⊢ᵈ[D] (~~φ)) := by
  intro H;
  exact deducible_MP deducible_DNI H;

variable [HasExplode D] 

lemma deducible_EFQ (φ) : ⊢ᵈ[D] (Axioms.EFQ φ) := sorry

lemma deducible_explode (φ) : (⊢ᵈ[D] ⊥) → (⊢ᵈ[D] φ) := by
  intro H;
  apply toProves_def;
  exact Explode φ H;

variable [HasDNElim D]

@[simp]
lemma deducible_negneg_elim : (⊢ᵈ[D] (~~φ)) → (⊢ᵈ[D] (φ)) := by
  intro H;
  apply toProves_def;
  exact DNElim H;

variable [HasDisj α] [HasDisjDef α]

lemma deducible_LEM : ⊢ᵈ[D] (Axioms.LEM φ) := by
  simp only [Axioms.LEM, HasDisjDef.DisjDef];
  aesop;

lemma deducible_contrapose₃ : (⊢ᵈ[D] (~φ ⇒ ψ)) → (⊢ᵈ[D] (~ψ ⇒ φ)) := by
  intro H₁;
  sorry

lemma deducible_contrapose₄ : (⊢ᵈ[D] (~φ ⇒ ~ψ)) → (⊢ᵈ[D] (ψ ⇒ φ)) := by
  intro H₁;
  sorry

lemma deducible_imply_elim_ant_dne : (⊢ᵈ[D] (~~φ ⇒ ψ)) → (⊢ᵈ[D] (φ ⇒ ψ)) := sorry

lemma deducible_imply_elim_con_dne : (⊢ᵈ[D] (φ ⇒ ~~ψ)) → (⊢ᵈ[D] (φ ⇒ ψ)) := sorry

lemma deducible_disj_distribute : (⊢ᵈ[D] (φ ⋎ ψ)) → ((⊢ᵈ[D] φ) ∨ (⊢ᵈ[D] ψ)) := by
  simp [HasDisjDef.DisjDef];
  intro h;
  have h₁ := @MP _ D _ _ ∅ (φ ⇒ ⊥) ψ
  have h₂ := h₁;
  sorry

variable [HasConj α] [HasConjDef α]

@[simp]
lemma deducible_conj_intro : ((⊢ᵈ[D] φ) ∧ (⊢ᵈ[D] ψ)) → (⊢ᵈ[D] (φ ⋏ ψ)):= by
  intro H;
  
  have ⟨hl, hr⟩ := H;
  simp [HasConjDef.ConjDef];
  apply toProves_def;
  repeat apply DT.mpr;

  have h₁ : ({φ ⇒ ψ ⇒ ⊥}) ⊢ᵈ[D] φ ⇒ ψ ⇒ ⊥ := by simp;
  have h₂ := MP h₁ hl;
  have h₃ := MP h₂ hr;
  aesop;


@[simp]
lemma deducible_conj_left : (⊢ᵈ[D] (φ ⋏ ψ)) → (⊢ᵈ[D] φ) := by 
  simp [HasConjDef.ConjDef];
  intro H;
  
  apply toProves_def;
  repeat apply DT.mpr;

  /-
  have h₁ : {φ ⇒ ψ ⇒ ⊥} ⊢[D] ⊥ := by
    have h : (∅ ∪ {φ ⇒ ψ ⇒ ⊥}) ⊢[D] ⊥ := DT.mp H;
    simp at h;
    exact h;
  have h₂ : {φ ⇒ ψ ⇒ ⊥} ⊢[D] φ ⇒ ψ ⇒ ⊥ := by simp;
  -/
  -- have h₃ := MP h₂;

  /-
  have h₁ : ({φ ⇒ ψ ⇒ ⊥, φ}) ⊢[D] (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ := fromProves H;
  have h₂ : {φ ⇒ ψ ⇒ ⊥, φ} ⊢[D] φ ⇒ ψ ⇒ ⊥ := by simp;
  have h₃ := MP h₂ h₁;
  -/

  sorry

@[simp]
lemma deducible_conj_comm : (⊢ᵈ[D] (φ ⋏ ψ)) → (⊢ᵈ[D] (ψ ⋏ φ)) := by
  intro H;
  
  simp [HasConjDef.ConjDef];
  
  apply toProves_def;
  repeat apply DT.mpr;

  have h₁ : ({ψ ⇒ φ ⇒ ⊥}) ⊢ᵈ[D] ψ ⇒ φ ⇒ ⊥ := by simp;
  have h₂ := MP h₁;

  sorry
  -- have h₂ := MP h₁;
  -- have h₂ : ({ψ ⇒ φ ⇒ ⊥, ψ}) ⊢[D] φ ⇒ ⊥ := by simp;
  
  
@[simp]
lemma deducible_conj_right : (⊢ᵈ[D] (φ ⋏ ψ)) → (⊢ᵈ[D] ψ) := by
  intro H;
  exact deducible_conj_left (deducible_conj_comm H);

@[simp]
lemma deducible_conj_contract : (⊢ᵈ[D] φ ⋏ φ) ↔ (⊢ᵈ[D] φ) := by
  apply Iff.intro;
  . intro H;
    exact deducible_conj_left H;
  . intro H;
    exact deducible_conj_intro ⟨H, H⟩;

variable [HasEquiv α] [HasEquivDef α]

attribute [simp] HasEquivDef.EquivDef


@[simp]
lemma deducible_equiv_comm : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] (ψ ⇔ φ)) := by aesop;

@[simp]
lemma deducible_equiv_mp : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] φ ⇒ ψ) := by
  simp; 
  exact deducible_conj_left;

@[simp]
lemma deducible_equiv_mpr : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] ψ ⇒ φ) := by
  intro H;
  exact deducible_equiv_mp (deducible_equiv_comm H);

@[simp]
lemma deducible_equiv_neg : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] ((~φ : α) ⇔ ~ψ)) := by sorry

lemma deducible_equiv_eq : (⊢ᵈ[D] (φ ⇔ ψ)) ↔ ((⊢ᵈ[D] φ) ↔ (⊢ᵈ[D] ψ)) := by
  apply Iff.intro;
  . intro H;
    apply Iff.intro;
    . intro h;
      have hmp := deducible_equiv_mp H;
      exact deducible_MP hmp h;
    . intro h;
      have hmpr := deducible_equiv_mpr H;
      exact deducible_MP hmpr h;
  . intro H;
    simp;
    apply deducible_conj_intro;
    apply And.intro;
    . sorry;
    . sorry;

lemma deducible_equiv_left : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] φ) → (⊢ᵈ[D] ψ) := by
  intro H₁ H₂;
  have h₁ := deducible_equiv_mp H₁;
  exact deducible_MP h₁ H₂;

lemma deducible_equiv_right : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] ψ) → (⊢ᵈ[D] φ) := by
  intro H₁ H₂;
  exact deducible_equiv_left (deducible_equiv_comm H₁) H₂;

lemma deducible_equiv_neg_left : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] (~φ)) → (⊢ᵈ[D] (~ψ)) := by
  intro H₁ H₂;
  sorry
  
lemma deducible_equiv_neg_right : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] (~ψ)) → (⊢ᵈ[D] (~φ)) := by
  intro H₁ H₂
  exact deducible_equiv_neg_left (deducible_equiv_comm H₁) H₂;

lemma deducible_equiv_trans : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊢ᵈ[D] (ψ ⇔ ξ)) → (⊢ᵈ[D] (φ ⇔ ξ)) := by
  intro H₁ H₂;
  simp [HasEquivDef.EquivDef];
  apply deducible_conj_intro;
  apply And.intro;
  . have H₁ := deducible_equiv_mp H₁;
    have H₂ := deducible_equiv_mp H₂;
    exact deducible_imply_trans ⟨H₁, H₂⟩;    
  . have H₁ := deducible_equiv_mpr H₁;
    have H₂ := deducible_equiv_mpr H₂;
    exact deducible_imply_trans ⟨H₂, H₁⟩;

lemma undeducible_equiv_left : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊬ᵈ[D] φ) → (⊬ᵈ[D] ψ) := by
  intro H₁ H₂;
  exact (deducible_equiv_eq.mp H₁).not.mp H₂;

lemma undeducible_equiv_right : (⊢ᵈ[D] (φ ⇔ ψ)) → (⊬ᵈ[D] ψ) → (⊬ᵈ[D] φ) := by
  intro H₁ H₂;
  exact undeducible_equiv_left (deducible_equiv_comm H₁) H₂;

end DeductionSystem

end ModalLogic.PropositionalLogic