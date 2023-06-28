import Modallogic.Propositional.Formula
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

namespace Modallogic

namespace Propositional

variable {α β : Type}

namespace HilbertProof

inductive HTheorem : Formula α → Prop
| ax1 : HTheorem (Axiom1 φ ψ)
| ax2 : HTheorem (Axiom2 φ ψ χ)
| ax3 : HTheorem (Axiom3 φ ψ)
| mp : HTheorem (φ →ₚ ψ) → HTheorem φ → HTheorem ψ

namespace HTheorem

variable (φ ψ χ : Formula α)

@[simp] lemma ax1_def : HTheorem ((φ →ₚ (ψ →ₚ φ))) := ax1
@[simp] lemma ax2_def : HTheorem ((φ →ₚ (ψ →ₚ χ)) →ₚ ((φ →ₚ ψ) →ₚ (φ →ₚ χ))) := ax2
@[simp] lemma ax3_def : HTheorem (((¬ₚφ →ₚ ¬ₚψ) →ₚ (ψ →ₚ φ))) := ax3

@[simp] lemma mp_def (hφψ : HTheorem (φ →ₚ ψ)) (hφ : HTheorem φ): HTheorem ψ := mp hφψ hφ

@[simp]
theorem id : HTheorem (φ →ₚ φ) := by
  have s1 := ax1_def φ (φ →ₚ φ)
  have s2 := ax2_def φ (φ →ₚ φ) φ
  have s3 := mp s2 s1
  have s4 := ax1_def φ φ
  have s5 := mp s3 s4
  exact s5

@[simp]
theorem iff_to_and (h : HTheorem (φ ↔ₚ ψ)) : HTheorem ((φ →ₚ ψ) ∧ₚ (ψ →ₚ φ)) := by simp [Formula.iff] at h; exact h;

@[simp]
theorem cut (h1 : HTheorem (φ →ₚ ψ)) (h2 : HTheorem (ψ →ₚ χ)) : HTheorem (φ →ₚ χ) := by
  have s1 := ax1_def (ψ →ₚ χ) φ;
  have s2 := mp s1 h2;
  have s3 := ax2_def φ ψ χ;
  have s4 := mp s3 s2;
  have s5 := mp s4 h1;
  exact s5;

@[simp]
theorem intro_imp_antecedent (h : HTheorem ψ) : HTheorem (φ →ₚ ψ) := by
  have s1 := ax1_def ψ φ;
  have s2 := mp s1 h;
  exact s2;

lemma not_not_elim.lem1 : HTheorem (¬ₚφ →ₚ (φ →ₚ ψ)) := by
  have s1 := intro_imp_antecedent (¬ₚφ) (Axiom3 ψ φ) (ax3_def ψ φ);
  have s2 := ax2_def (¬ₚφ) (¬ₚψ →ₚ ¬ₚφ) (φ →ₚ ψ);
  have s3 := mp s2 s1;
  have s4 := ax1_def (¬ₚφ) (¬ₚψ)
  have s5 := mp s3 s4;
  exact s5;

def bot := ¬ₚ(#0 →ₚ #0)

theorem not_not_elim (φ : Formula α) : HTheorem (¬ₚ¬ₚφ →ₚ φ) := by
  have s1 := not_not_elim.lem1 (¬ₚφ) (¬ₚ¬ₚ¬ₚφ);
  have s2 := ax3_def (φ) (¬ₚ¬ₚφ) ;
  have s3 : HTheorem (¬ₚ¬ₚφ→ₚ¬ₚ¬ₚφ→ₚφ) := cut _ _ _ s1 s2
  have s4 := ax2_def (¬ₚ¬ₚφ) (¬ₚ¬ₚφ) (φ);
  have s5 := mp s4 s3;
  have s6 := id (¬ₚ¬ₚφ);
  have s7 := mp s5 s6;
  exact s7;

end HTheorem

inductive HProvable (Γ : Formulae α) (φ : Formula α) : Prop
| thm : HTheorem φ → HProvable Γ φ
| ctx : φ ∈ Γ → HProvable Γ φ

notation Γ " ⊢ₚ " φ => HProvable Γ φ
notation Γ " ⊬ₚ " φ => ¬(Γ ⊢ₚ φ)

notation "⊢ₚ " φ => ∅ ⊢ₚ φ
notation "⊬ₚ " φ => ∅ ⊬ₚ φ

namespace HProvable

variable (Γ Δ : Formulae α) (φ ψ χ : Formula α)

theorem to_theorem : (⊢ₚ φ) → (HTheorem φ) := by
  intro h;
  cases h with
  | thm h => exact h
  | ctx h => contradiction;

@[simp] theorem ax1 : Γ ⊢ₚ (φ →ₚ (ψ →ₚ φ)) := thm (HTheorem.ax1_def φ ψ)
@[simp] theorem ax2 : Γ ⊢ₚ ((φ →ₚ (ψ →ₚ χ)) →ₚ ((φ →ₚ ψ) →ₚ (φ →ₚ χ))) := thm (HTheorem.ax2_def φ ψ χ)
@[simp] theorem ax3 : Γ ⊢ₚ (((¬ₚφ →ₚ ¬ₚψ) →ₚ (ψ →ₚ φ))) := thm (HTheorem.ax3_def φ ψ)

@[simp]
theorem ctx_def (Γ : Formulae α) (φ : Formula α) : (Γ ∪ {φ}) ⊢ₚ φ := by exact ctx (by simp)

@[simp]
def mp (Γ : Formulae α) (φ ψ : Formula α) (h1 : Γ ⊢ₚ (φ →ₚ ψ)) (h2 : Γ ⊢ₚ φ) : Γ ⊢ₚ ψ :=
  match h1, h2 with
  | thm h1, thm h2 => thm (HTheorem.mp h1 h2)
  | ctx h1, thm h2 => sorry
  | thm h1, ctx h2 => sorry
  | ctx h1, ctx h2 => sorry

theorem intro_contra (Γ : Formulae α) (φ ψ : Formula α) : (Γ ⊢ₚ (¬ₚφ →ₚ ¬ₚψ)) → (Γ ⊢ₚ (ψ →ₚ φ)) := by
  intro h;
  sorry

theorem elim_contra (Γ : Formulae α) (φ ψ : Formula α) : (Γ ⊢ₚ (ψ →ₚ φ)) → (Γ ⊢ₚ (¬ₚφ →ₚ ¬ₚψ)) := by
  intro h;
  sorry

@[simp]
theorem id : Γ ⊢ₚ (φ →ₚ φ) := by exact thm (HTheorem.id φ)

@[simp]
theorem intro_imp_antecedent :  (Γ ⊢ₚ ψ) → (Γ ⊢ₚ (φ →ₚ ψ)) := by
  intro h;
  have h1 := ax1 Γ ψ φ;
  have h2 := mp _ _ _ h1 h;
  exact h2;

theorem deduction_right (Γ : Formulae α) : ((Γ ∪ {φ}) ⊢ₚ ψ) → (Γ ⊢ₚ (φ →ₚ ψ)) := by
  intro h;
  induction h with
  | thm h => exact HProvable.thm (HTheorem.intro_imp_antecedent φ ψ h)
  | ctx h =>
    cases h with
    | inl h => exact HProvable.intro_imp_antecedent Γ φ ψ (HProvable.ctx h);
    | inr h => have h2 := Set.eq_of_mem_singleton h; rw [h2]; simp;

theorem deduction_left (Γ : Formulae α) : (Γ ⊢ₚ (φ →ₚ ψ)) → ((Γ ∪ {φ}) ⊢ₚ ψ) := by
  intro h;
  induction h with
  | thm h =>
    cases h with
    | ax1 => sorry
    | ax2 => sorry
    | ax3 => sorry
    | mp h1 h2 => sorry
  | ctx h => sorry

theorem weakening_subset (hΔ : Γ ⊆ Δ) : (Γ ⊢ₚ φ) → (Δ ⊢ₚ φ) := by
  intro h;
  induction h with
  | thm h => exact HProvable.thm h
  | ctx h => have h2 : φ ∈ Δ := Set.mem_of_subset_of_mem hΔ h; exact HProvable.ctx h2

theorem weakening_right : (Γ ⊢ₚ ψ) → ((Γ ∪ {φ}) ⊢ₚ ψ) := by
  intro h; exact weakening_subset _ _ _ (by simp) h

@[simp]
theorem contraction : ((Γ ∪ {φ} ∪ {φ}) ⊢ₚ ψ) → ((Γ ∪ {φ}) ⊢ₚ ψ) := by
  intro h;
  induction h with
  | thm h => exact HProvable.thm h
  | ctx h =>
    cases h with
    | inl h => exact HProvable.ctx h
    | inr h => have h2 := Set.eq_of_mem_singleton h; rw [h2]; exact ctx_def Γ φ;

@[simp]
theorem exchange : ((Γ ∪ {φ} ∪ {ψ}) ⊢ₚ χ) → ((Γ ∪ {ψ} ∪ {φ}) ⊢ₚ χ) := by
  intro h;
  induction h with
  | thm h => exact HProvable.thm h
  | ctx h =>
      rw [Set.union_assoc] at h;
      rw [Set.union_comm {φ} {ψ}] at h;
      rw [←Set.union_assoc] at h;
      exact HProvable.ctx h

theorem cut (h1 : Γ ⊢ₚ (φ →ₚ ψ)) (h2 : Γ ⊢ₚ (ψ →ₚ χ)) : (Γ ⊢ₚ φ →ₚ χ) := by
  match h1, h2 with
  | thm h1, thm h2 => exact HProvable.thm (HTheorem.cut _ _ _ h1 h2)
  | thm h1, ctx h2 => sorry
  | ctx h1, thm h2 => sorry
  | ctx h1, ctx h2 => sorry

theorem explosion' : ⊢ₚ (¬ₚφ →ₚ (φ →ₚ ψ)) := by
  apply deduction_right;
  apply deduction_right;
  have s1 : ({φ, ¬ₚφ} ⊢ₚ φ) := @HProvable.ctx α {φ, ¬ₚφ} (φ) (by simp);
  have s2 : ({φ, ¬ₚφ} ⊢ₚ ¬ₚφ) := @HProvable.ctx α {φ, ¬ₚφ} (¬ₚφ) (by simp);
  have s3 := HProvable.ax1 {φ, ¬ₚφ} (¬ₚφ) (¬ₚψ);
  have s4 : {φ, ¬ₚφ} ⊢ₚ ¬ₚψ→ₚ¬ₚφ := HProvable.mp _ _ _ s3 s2;
  have s5 : {φ, ¬ₚφ} ⊢ₚ (φ →ₚ ψ) := HProvable.intro_contra _ _ _ s4;
  have s6 : {φ, ¬ₚφ} ⊢ₚ ψ := HProvable.mp _ _ _ s5 s1;
  simp
  exact s6;

theorem explosion : ({φ, ¬ₚφ}) ⊢ₚ ψ := by
  have s1 := explosion' φ ψ;
  have s2 := deduction_left _ _ _ s1;
  have s3 := deduction_left _ _ _ s2;
  simp at s3;
  exact s3

def inconsistent (Γ : Formulae α) :=  ∃ φ, (φ ∈ Γ ∧ ¬ₚφ ∈ Γ)
def consistent (Γ : Formulae α) := ¬(inconsistent Γ)

example (h₁ : a ∈ Γ) (h₂ : b ∈ Γ) : {a, b} ⊆ Γ := by
  intro x h₃;
  cases h₃ with
  | inl h₃ => rw [h₃]; exact h₁
  | inr h₃ => rw [h₃]; exact h₂

theorem incosistent_explosion (h : inconsistent Γ) : (Γ ⊢ₚ ψ) := by
  apply Exists.elim h;
  intro φ h;
  have h1 : {φ, ¬ₚφ} ⊆ Γ := by
    intro x h₃;
    cases h₃ with
    | inl h₃ => rw [h₃]; exact h.left
    | inr h₃ => rw [h₃]; exact h.right
  exact weakening_subset ({φ, ¬ₚφ}) Γ ψ h1 (explosion φ ψ);

theorem inconsistent_def : (∃ φ, ((Γ ⊢ₚ φ) ∧ (Γ ⊢ₚ ¬ₚφ))) → (inconsistent Γ) := by sorry

theorem consistent_def : (consistent Γ) → (∀ φ, (Γ ⊬ₚ φ) ∨ (Γ ⊬ₚ ¬ₚφ)) := by sorry

theorem iff_inconsistent_provable : (inconsistent (Γ ∪ {φ})) ↔ (Γ ⊢ₚ φ) := by
  apply Iff.intro;
  . intro h; sorry;
  . intro h;
    apply inconsistent_def;
    apply Exists.intro φ;
    sorry

theorem cons : (Γ ⊬ₚ φ) → (consistent (Γ ∪ {φ})) := by
  have h1 := (iff_inconsistent_provable Γ φ).mp;
  contrapose!;
  rw [consistent];
  push_neg;
  exact h1

theorem consistent_lemma : (consistent Γ) → (consistent (Γ ∪ {φ}) ∨ consistent (Γ ∪ {¬ₚφ})) := by
  intro h;
  have h1 := consistent_def _ h φ;
  apply Or.elim h1;
  . intro h2;
    apply Or.inl;
    exact (cons _ _ h2);
  . intro h2;
    apply Or.inr;
    exact (cons _ _ h2)

end HProvable

/-
def contradiction (φ : Formula α) := ¬ₚ(φ →ₚ φ)
prefix:25 "¿" => contradiction

def inconsistent (Γ : Formulae α) : Prop :=  ∃ φ, Γ ⊢ₚ ¿φ

def consistent (Γ : Formulae α) : Prop := ¬(inconsistent Γ)
-/

end HilbertProof

end Propositional

end Modallogic
