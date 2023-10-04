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
variable {D : DeductionSystem α}

@[simp] 
lemma toProves_def : (∅ ⊢ᵈ[D] φ) → (⊢ᵈ[D] φ) := by apply (NoContext D).mp

@[simp] lemma inContext_def : (φ ∈ Γ) → (Γ ⊢ᵈ[D] φ) := by apply inContext

@[simp]
axiom contextWeakening {Γ Δ φ} : (Γ ⊢ᵈ[D] φ) → ((Γ ∪ Δ) ⊢ᵈ[D] φ)

instance : Coe (Γ ⊢ᵈ[D] φ) ((Γ ∪ Δ) ⊢ᵈ[D] φ) := ⟨contextWeakening⟩ 

@[simp]
axiom fromProves {Γ D} {φ : α}: (⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] φ)

instance Coe : Coe (⊢ᵈ[D] φ) (Γ ⊢ᵈ[D] φ) := ⟨fromProves⟩

@[simp] lemma trivial_context (φ : α) : {φ} ⊢ᵈ[D] φ := by aesop;

section

variable (D : DeductionSystem α)

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

end

open HasDT HasMP HasExplode HasDNElim

variable [HasImply α] [HasBot α] [HasNeg α] [HasNegDef α]
variable {D : DeductionSystem α}

variable [HasDT D] [HasMP D] 

@[simp]
lemma deducible_equality : ⊢ᵈ[D] φ ⇒ φ := by simp;

lemma deducible_K : Γ ⊢ᵈ[D] (Axioms.K φ ψ) := by simp;

lemma deducible_S : Γ ⊢ᵈ[D] (Axioms.S φ ψ ξ) := by 
  repeat apply DT.mpr;
  have h₁ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ ({φ ⇒ ψ, φ})) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ ({φ ⇒ ψ, φ})) ⊢ᵈ[D] φ ⇒ ψ := by simp;
  have h₃ : (Γ ∪ {φ ⇒ ψ ⇒ ξ} ∪ ({φ ⇒ ψ, φ})) ⊢ᵈ[D] φ ⇒ ψ ⇒ ξ := by simp;
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
lemma deducible_DNI : Γ ⊢ᵈ[D] (Axioms.DNI φ) := by
  simp;
  repeat apply DT.mpr;
  have h₁ : (Γ ∪ {φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ ⇒ ⊥, φ}) ⊢ᵈ[D] φ ⇒ ⊥ := by simp;
  have h₃ := MP h₂ h₁;
  aesop;


lemma deducible_imply_trans : ((Γ ⊢ᵈ[D] (φ ⇒ ψ)) ∧ (Γ ⊢ᵈ[D] (ψ ⇒ ξ))) → (Γ ⊢ᵈ[D] (φ ⇒ ξ)) := by
  intro H₁;
  have ⟨H₁l, H₁r⟩ := H₁; 
  have H₂ := λ h => MP H₁.right (MP H₁.left h);
  sorry

lemma deducible_contrapose₁ : (Γ ⊢ᵈ[D] (φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (~ψ ⇒ ~φ)) := by
  intro H₁;
  simp [HasNegDef.NegDef];
  
  repeat apply DT.mpr;

  have H₁ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] φ ⇒ ψ := H₁;
  have h₁ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] ψ ⇒ ⊥ := by simp;
  have h₂ : (Γ ∪ {ψ ⇒ ⊥} ∪ {φ}) ⊢ᵈ[D] φ := by simp;
  have h₃ := MP H₁ h₂;
  have h₄ := MP h₁ h₃;
  aesop;

lemma deducible_contrapose₂ : (Γ ⊢ᵈ[D] (φ ⇒ ~ψ)) → (Γ ⊢ᵈ[D] (ψ ⇒ ~φ)) := by
  intro H₁;
  simp [HasNegDef.NegDef];
  
  repeat apply DT.mpr;

  have H₁ : (Γ ∪ {φ, ψ}) ⊢ᵈ[D] φ ⇒ ~ψ := H₁;
  have h₁ : (Γ ∪ {φ, ψ}) ⊢ᵈ[D] φ := by simp;
  have h₂ : (Γ ∪ {φ, ψ}) ⊢ᵈ[D] ψ := by simp;
  have h₃ := MP H₁ h₁;
  simp only [HasNegDef.NegDef] at h₃;
  have h₄ := MP h₃ h₂;
  sorry;
  -- aesop;

lemma deducible_negneg_intro : (Γ ⊢ᵈ[D] (φ)) → (Γ ⊢ᵈ[D] (~~φ)) := λ H => MP deducible_DNI H

variable [HasExplode D] 

lemma deducible_EFQ (φ) : Γ ⊢ᵈ[D] (Axioms.EFQ φ) := by simp;

variable [HasDNElim D]

variable [HasDisj α] [HasDisjDef α]

lemma deducible_LEM : Γ ⊢ᵈ[D] (Axioms.LEM φ) := by
  simp only [Axioms.LEM, HasDisjDef.DisjDef];
  aesop;

lemma deducible_contrapose₃ : (Γ ⊢ᵈ[D] (~φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (~ψ ⇒ φ)) := by
  intro H₁;
  repeat apply DT.mpr;
  have h₁ : {~ψ} ⊢ᵈ[D] ~ψ := by simp;
  sorry

lemma deducible_contrapose₄ : (Γ ⊢ᵈ[D] (~φ ⇒ ~ψ)) → (Γ ⊢ᵈ[D] (ψ ⇒ φ)) := by
  intro H₁;
  sorry

lemma deducible_imply_elim_ant_dne : (Γ ⊢ᵈ[D] (~~φ ⇒ ψ)) → (Γ ⊢ᵈ[D] (φ ⇒ ψ)) := sorry

lemma deducible_imply_elim_con_dne : (Γ ⊢ᵈ[D] (φ ⇒ ~~ψ)) → (Γ ⊢ᵈ[D] (φ ⇒ ψ)) := sorry

lemma deducible_disj_distribute : (⊢ᵈ[D] (φ ⋎ ψ)) → ((⊢ᵈ[D] φ) ∨ (⊢ᵈ[D] ψ)) := by
  simp [HasDisjDef.DisjDef];
  intro h;
  have h₁ := @MP _ D _ _ ∅ (φ ⇒ ⊥) ψ
  have h₂ := h₁;
  sorry

variable [HasConj α] [HasConjDef α]

@[simp]
lemma deducible_conj_intro : ((Γ ⊢ᵈ[D] φ) ∧ (Γ ⊢ᵈ[D] ψ)) → (Γ ⊢ᵈ[D] (φ ⋏ ψ)):= by
  intro H;
  
  have ⟨hl, hr⟩ := H;
  simp [HasConjDef.ConjDef];
  
  repeat apply DT.mpr;

  have h₁ : (Γ ∪ {φ ⇒ ψ ⇒ ⊥}) ⊢ᵈ[D] φ ⇒ ψ ⇒ ⊥ := by simp;
  have h₂ := MP h₁ hl;
  have h₃ := MP h₂ hr;
  exact h₃;


@[simp]
lemma deducible_conj_left : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] φ) := by 
  simp [HasConjDef.ConjDef];
  intro H;
  
  -- apply toProves_def;
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
lemma deducible_conj_comm : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] (ψ ⋏ φ)) := by
  intro H;
  
  simp [HasConjDef.ConjDef];
  
  repeat apply DT.mpr;

  have h₁ : ({ψ ⇒ φ ⇒ ⊥}) ⊢ᵈ[D] ψ ⇒ φ ⇒ ⊥ := by simp;
  have h₂ := MP h₁;

  sorry
  -- have h₂ := MP h₁;
  -- have h₂ : ({ψ ⇒ φ ⇒ ⊥, ψ}) ⊢[D] φ ⇒ ⊥ := by simp;
  
  
@[simp]
lemma deducible_conj_right : (Γ ⊢ᵈ[D] (φ ⋏ ψ)) → (Γ ⊢ᵈ[D] ψ) := by
  intro H;
  exact deducible_conj_left (deducible_conj_comm H);

@[simp]
lemma deducible_conj_contract : (Γ ⊢ᵈ[D] φ ⋏ φ) ↔ (Γ ⊢ᵈ[D] φ) := by
  apply Iff.intro;
  . intro H;
    exact deducible_conj_left H;
  . intro H;
    exact deducible_conj_intro ⟨H, H⟩;

variable [HasEquiv α] [HasEquivDef α]

attribute [simp] HasEquivDef.EquivDef

@[simp]
lemma deducible_equiv_intro : ((Γ ⊢ᵈ[D] (φ ⇒ ψ)) ∧ (Γ ⊢ᵈ[D] (ψ ⇒ φ))) → (Γ ⊢ᵈ[D] (φ ⇔ ψ)) := by aesop;

@[simp]
lemma deducible_equiv_comm : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (ψ ⇔ φ)) := by aesop;

@[simp]
lemma deducible_equiv_mp : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] φ ⇒ ψ) := by
  intro H;
  simp [HasEquivDef.EquivDef] at H
  exact deducible_conj_left H;

@[simp]
lemma deducible_equiv_mpr : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ψ ⇒ φ) := by
  intro H;
  exact deducible_equiv_mp (deducible_equiv_comm H);

@[simp]
lemma deducible_equiv_neg : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ((~φ : α) ⇔ ~ψ)) := by sorry

lemma deducible_equiv_eq : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) ↔ ((Γ ⊢ᵈ[D] φ) ↔ (Γ ⊢ᵈ[D] ψ)) := by
  apply Iff.intro;
  . intro H;
    apply Iff.intro;
    . intro h;
      have hmp := deducible_equiv_mp H;
      exact MP hmp h;
    . intro h;
      have hmpr := deducible_equiv_mpr H;
      exact MP hmpr h;
  . intro H;
    simp;
    apply deducible_conj_intro;
    apply And.intro;
    . sorry;
    . sorry;

lemma deducible_equiv_left : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] φ) → (Γ ⊢ᵈ[D] ψ) := by
  intro H₁ H₂;
  have h₁ := deducible_equiv_mp H₁;
  exact MP h₁ H₂;

lemma deducible_equiv_right : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] ψ) → (Γ ⊢ᵈ[D] φ) := by
  intro H₁ H₂;
  exact deducible_equiv_left (deducible_equiv_comm H₁) H₂;

lemma deducible_equiv_neg_left : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (~φ)) → (Γ ⊢ᵈ[D] (~ψ)) := by
  intro H₁ H₂;
  sorry
  
lemma deducible_equiv_neg_right : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (~ψ)) → (Γ ⊢ᵈ[D] (~φ)) := by
  intro H₁ H₂
  exact deducible_equiv_neg_left (deducible_equiv_comm H₁) H₂;

lemma deducible_equiv_trans : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊢ᵈ[D] (ψ ⇔ ξ)) → (Γ ⊢ᵈ[D] (φ ⇔ ξ)) := by
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

lemma undeducible_equiv_left : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊬ᵈ[D] φ) → (Γ ⊬ᵈ[D] ψ) := by
  intro H₁ H₂;
  exact (deducible_equiv_eq.mp H₁).not.mp H₂;

lemma undeducible_equiv_right : (Γ ⊢ᵈ[D] (φ ⇔ ψ)) → (Γ ⊬ᵈ[D] ψ) → (Γ ⊬ᵈ[D] φ) := by
  intro H₁ H₂;
  exact undeducible_equiv_left (deducible_equiv_comm H₁) H₂;

end DeductionSystem

end ModalLogic.PropositionalLogic