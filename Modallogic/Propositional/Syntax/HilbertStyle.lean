import Modallogic.Propositional.Formula
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.LibrarySearch

namespace Modallogic.Propositional

namespace Syntax.HilbertStyle

def Axiom1 (φ ψ : Formula α) := (φ →ₚ (ψ →ₚ φ))
def Axiom2 (φ ψ χ : Formula α) := ((φ →ₚ (ψ →ₚ χ)) →ₚ ((φ →ₚ ψ) →ₚ (φ →ₚ χ)))
def Axiom3 (φ ψ : Formula α) := ((¬ₚφ →ₚ ¬ₚψ) →ₚ (ψ →ₚ φ))

inductive Theorem : Formula α → Prop
| ax1 : Theorem (Axiom1 φ ψ)
| ax2 : Theorem (Axiom2 φ ψ χ)
| ax3 : Theorem (Axiom3 φ ψ)
| mp : Theorem (φ →ₚ ψ) → Theorem φ → Theorem ψ

namespace Theorem

variable (φ ψ χ : Formula α)

@[simp] lemma ax1_def : Theorem ((φ →ₚ (ψ →ₚ φ))) := ax1
@[simp] lemma ax2_def : Theorem ((φ →ₚ (ψ →ₚ χ)) →ₚ ((φ →ₚ ψ) →ₚ (φ →ₚ χ))) := ax2
@[simp] lemma ax3_def : Theorem (((¬ₚφ →ₚ ¬ₚψ) →ₚ (ψ →ₚ φ))) := ax3

@[simp] lemma mp_def (hφψ : Theorem (φ →ₚ ψ)) (hφ : Theorem φ): Theorem ψ := mp hφψ hφ

@[simp]
theorem id : Theorem (φ →ₚ φ) := by
  have s1 := ax1_def φ (φ →ₚ φ)
  have s2 := ax2_def φ (φ →ₚ φ) φ
  have s3 := mp s2 s1
  have s4 := ax1_def φ φ
  have s5 := mp s3 s4
  exact s5

@[simp]
theorem cut (h1 : Theorem (φ →ₚ ψ)) (h2 : Theorem (ψ →ₚ χ)) : Theorem (φ →ₚ χ) := by
  have s1 := ax1_def (ψ →ₚ χ) φ;
  have s2 := mp s1 h2;
  have s3 := ax2_def φ ψ χ;
  have s4 := mp s3 s2;
  have s5 := mp s4 h1;
  exact s5;

@[simp]
theorem weakening (h : Theorem ψ) : Theorem (φ →ₚ ψ) := by
  have s1 := ax1_def ψ φ;
  have s2 := mp s1 h;
  exact s2;

@[simp]
theorem iff_to_and (h : Theorem (φ ↔ₚ ψ)) : Theorem ((φ →ₚ ψ) ∧ₚ (ψ →ₚ φ)) := by simp [Formula.iff] at h; exact h;

theorem explosion' : Theorem (¬ₚφ →ₚ (φ →ₚ ψ)) := by
  have s1 := weakening (¬ₚφ) (Axiom3 ψ φ) (ax3_def ψ φ);
  have s2 := ax2_def (¬ₚφ) (¬ₚψ →ₚ ¬ₚφ) (φ →ₚ ψ);
  have s3 := mp s2 s1;
  have s4 := ax1_def (¬ₚφ) (¬ₚψ)
  have s5 := mp s3 s4;
  exact s5;

theorem not_not_elim' : Theorem (¬ₚ¬ₚφ →ₚ φ) := by
  have s1 := explosion' (¬ₚφ) (¬ₚ¬ₚ¬ₚφ);
  have s2 := ax3_def (φ) (¬ₚ¬ₚφ) ;
  have s3 : Theorem (¬ₚ¬ₚφ→ₚ¬ₚ¬ₚφ→ₚφ) := cut _ _ _ s1 s2
  have s4 := ax2_def (¬ₚ¬ₚφ) (¬ₚ¬ₚφ) (φ);
  have s5 := mp s4 s3;
  have s6 := id (¬ₚ¬ₚφ);
  have s7 := mp s5 s6;
  exact s7;

theorem not_not_elim (h : Theorem (¬ₚ¬ₚφ)) : Theorem φ := by exact mp (not_not_elim' φ) h;

end Theorem

inductive Provable (Γ : Formulae α) : Formula α → Prop
| thm (φ : Formula α) : Theorem φ → Provable Γ φ
| ctx (φ : Formula α) : φ ∈ Γ → Provable Γ φ
| mp (φ ψ : Formula α): (Provable Γ (φ →ₚ ψ)) → (Provable Γ φ) → (Provable Γ ψ)

notation Γ " ⊢ₚ " φ => Provable Γ φ
notation Γ " ⊬ₚ " φ => ¬(Γ ⊢ₚ φ)

notation "⊢ₚ " φ => ∅ ⊢ₚ φ
notation "⊬ₚ " φ => ∅ ⊬ₚ φ

namespace Provable

variable (Γ Δ : Formulae α) (φ ψ χ : Formula α)

theorem to_theorem (φ : Formula α) : (⊢ₚ φ) → (Theorem φ) := by
  intro h;
  induction h with
  | thm _ h => exact h
  | ctx _ h => contradiction;
  | mp _ _ _ _ ih1 ih2 => exact Theorem.mp ih1 ih2;

theorem ax1 : Γ ⊢ₚ (φ →ₚ (ψ →ₚ φ)) := thm _ (Theorem.ax1_def φ ψ)
theorem ax2 : Γ ⊢ₚ ((φ →ₚ (ψ →ₚ χ)) →ₚ ((φ →ₚ ψ) →ₚ (φ →ₚ χ))) := thm _ (Theorem.ax2_def φ ψ χ)
theorem ax3 : Γ ⊢ₚ (((¬ₚφ →ₚ ¬ₚψ) →ₚ (ψ →ₚ φ))) := thm _ (Theorem.ax3_def φ ψ)

theorem ctx_def (Γ : Formulae α) (φ : Formula α) : (Γ ∪ {φ}) ⊢ₚ φ := by exact ctx _ (by simp)

@[simp]
theorem intro_contra : (Γ ⊢ₚ (¬ₚφ →ₚ ¬ₚψ)) → (Γ ⊢ₚ (ψ →ₚ φ)) := by
  intro h;
  exact mp _ _ (ax3 _ _ _) h;

@[simp]
theorem id : Γ ⊢ₚ (φ →ₚ φ) := by exact thm _ (Theorem.id φ)

@[simp]
theorem intro_imp_antecedent :  (Γ ⊢ₚ ψ) → (Γ ⊢ₚ (φ →ₚ ψ)) := by
  intro h;
  have h1 := ax1 Γ ψ φ;
  have h2 := mp _ _ h1 h;
  exact h2;

theorem deduction_right (Γ : Formulae α) : ((Γ ∪ {φ}) ⊢ₚ ψ) → (Γ ⊢ₚ (φ →ₚ ψ)) := by
  intro h;
  induction h with
  | thm _ h => exact thm _ (Theorem.weakening _ _ h)
  | ctx _ h =>
    cases h with
    | inl h => simp; exact intro_imp_antecedent _ _ _ (ctx _ h);
    | inr h => rw [(Set.eq_of_mem_singleton h)]; simp;
  | mp ψ χ _ _ ih1 ih2 => exact mp _ _ (mp _ _ (ax2 Γ φ ψ χ) ih1) ih2;

theorem weakening_subset (hΔ : Γ ⊆ Δ) : (Γ ⊢ₚ φ) → (Δ ⊢ₚ φ) := by
  intro h;
  induction h with
  | thm _ h => exact Provable.thm _ h
  | ctx _ h => exact Provable.ctx _ (Set.mem_of_subset_of_mem hΔ h)
  | mp _ _ _ _ ih1 ih2 => exact Provable.mp _ _ ih1 ih2

theorem weakening : (Γ ⊢ₚ ψ) → ((Γ ∪ {φ}) ⊢ₚ ψ) := by
  intro h; exact weakening_subset _ _ _ (by simp) h

theorem deduction_left (Γ : Formulae α) : (Γ ⊢ₚ (φ →ₚ ψ)) → ((Γ ∪ {φ}) ⊢ₚ ψ) := by
  intro h;
  have h1 := weakening Γ φ _ h;
  have h2 := @ctx α (Γ ∪ {φ}) φ (by simp);
  exact @mp α _ _ _ h1 h2;

/-
@[simp]
theorem contraction : ((Γ ∪ {φ} ∪ {φ}) ⊢ₚ ψ) → ((Γ ∪ {φ}) ⊢ₚ ψ) := by
  intro h;
  induction h with
  | thm h => exact Provable.thm h
  | ctx h =>
    cases h with
    | inl h => exact Provable.ctx h
    | inr h => have h2 := Set.eq_of_mem_singleton h; rw [h2]; exact ctx_def Γ φ;

@[simp]
theorem exchange : ((Γ ∪ {φ} ∪ {ψ}) ⊢ₚ χ) → ((Γ ∪ {ψ} ∪ {φ}) ⊢ₚ χ) := by
  intro h;
  induction h with
  | thm h => exact Provable.thm h
  | ctx h =>
      rw [Set.union_assoc] at h;
      rw [Set.union_comm {φ} {ψ}] at h;
      rw [←Set.union_assoc] at h;
      exact Provable.ctx h

theorem cut (h1 : Γ ⊢ₚ (φ →ₚ ψ)) (h2 : Γ ⊢ₚ (ψ →ₚ χ)) : (Γ ⊢ₚ φ →ₚ χ) := by
  match h1, h2 with
  | thm h1, thm h2 => exact Provable.thm (Theorem.cut _ _ _ h1 h2)
  | thm h1, ctx h2 => sorry
  | ctx h1, thm h2 => sorry
  | ctx h1, ctx h2 => sorry
-/

theorem explosion' : ⊢ₚ (¬ₚφ →ₚ (φ →ₚ ψ)) := by
  apply deduction_right;
  apply deduction_right;
  have s1 : ({φ, ¬ₚφ} ⊢ₚ φ) := @ctx _ {φ, ¬ₚφ} (φ) (by simp);
  have s2 : ({φ, ¬ₚφ} ⊢ₚ ¬ₚφ) := @ctx _ {φ, ¬ₚφ} (¬ₚφ) (by simp);
  have s3 := Provable.ax1 {φ, ¬ₚφ} (¬ₚφ) (¬ₚψ);
  have s4 : {φ, ¬ₚφ} ⊢ₚ ¬ₚψ→ₚ¬ₚφ := mp _ _ s3 s2;
  have s5 : {φ, ¬ₚφ} ⊢ₚ (φ →ₚ ψ) := intro_contra _ _ _ s4;
  have s6 : {φ, ¬ₚφ} ⊢ₚ ψ := mp _ _ s5 s1;
  simp
  exact s6;

theorem explosion : ({φ, ¬ₚφ}) ⊢ₚ ψ := by
  have s1 := explosion' φ ψ;
  have s2 := deduction_left _ _ _ s1;
  have s3 := deduction_left _ _ _ s2;
  simp at s3;
  exact s3

end Provable

end Syntax.HilbertStyle

end Modallogic.Propositional
