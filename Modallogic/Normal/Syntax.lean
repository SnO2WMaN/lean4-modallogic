import Mathlib.Tactic.LibrarySearch

import Modallogic.Normal.Formula
import Modallogic.Normal.Axioms
import Modallogic.Normal.Context

namespace Modallogic.Normal

inductive HasProof : Formula α → Prop
| pl1 : HasProof (Axioms.Pl1 φ ψ)
| pl2 : HasProof (Axioms.Pl2 φ ψ χ)
| pl3 : HasProof (Axioms.Pl3 φ ψ)
| k : HasProof (Axioms.K φ ψ)
| mp : HasProof (φ →ₘ ψ) → HasProof φ → HasProof ψ
| nec : HasProof φ → HasProof (□φ)

namespace HasProof

theorem id_intro (φ : Formula α) : HasProof (φ →ₘ φ) := by
  have s1 := @HasProof.pl1 α φ (φ →ₘ φ);
  have s2 := @HasProof.pl2 α φ (φ →ₘ φ) φ;
  have s3 := HasProof.mp s2 s1;
  have s4 := @HasProof.pl1 α φ φ;
  have s5 := HasProof.mp s3 s4;
  exact s5;

theorem imp_bot (φ : Formula α) : HasProof (⊥ₘ →ₘ ¬ₘφ) := by exact @HasProof.pl1 α ⊥ₘ φ;

theorem imp_intro (φ ψ : Formula α) (hψ : HasProof ψ) : HasProof (φ →ₘ ψ) := by
  have s1 := @HasProof.pl1 α ψ φ;
  have s2 := HasProof.mp s1 hψ;
  exact s2;

theorem cut (φ ψ χ : Formula α) (h1 : HasProof (φ →ₘ ψ)) (h2 : HasProof (ψ →ₘ χ)) : HasProof (φ →ₘ χ) := by
  have s1 := @HasProof.pl1 α (ψ →ₘ χ) φ;
  have s2 := HasProof.mp s1 h2;
  have s3 := @HasProof.pl2 α φ ψ χ;
  have s4 := HasProof.mp s3 s2;
  have s5 := HasProof.mp s4 h1;
  exact s5;

lemma imp_arbitary (φ ψ : Formula α) : HasProof (¬ₘφ →ₘ (φ →ₘ ψ)) := by
  have s1 := imp_intro (¬ₘφ) (Axioms.Pl3 ψ φ) (@HasProof.pl3 α ψ φ);
  have s2 := @HasProof.pl2 α (¬ₘφ) (¬ₘψ →ₘ ¬ₘφ) (φ →ₘ ψ);
  have s3 := HasProof.mp s2 s1;
  have s4 := @HasProof.pl1 α (¬ₘφ) (¬ₘψ)
  have s5 := HasProof.mp s3 s4;
  exact s5;

theorem imp_not_not_elim (φ : Formula α) : HasProof (¬ₘ¬ₘφ →ₘ φ) := by
  have s1 := imp_arbitary (¬ₘφ) (¬ₘ¬ₘ¬ₘφ);
  have s2 := @HasProof.pl3 α (φ) (¬ₘ¬ₘφ) ;
  have s3 := cut _ _ _ s1 s2;
  have s4 := @HasProof.pl2 α (¬ₘ¬ₘφ) (¬ₘ¬ₘφ) (φ);
  have s5 := HasProof.mp s4 s3;
  have s6 := id_intro (¬ₘ¬ₘφ);
  have s7 := HasProof.mp s5 s6;
  exact s7;

theorem imp_not_not_intro (φ : Formula α) : HasProof (φ →ₘ ¬ₘ¬ₘφ) := by
  have s1 := @HasProof.pl3 α (¬ₘ¬ₘφ) φ;
  have s2 := imp_not_not_elim (¬ₘφ);
  have s3 := HasProof.mp s1 s2;
  exact s3;

theorem or_intro (φ ψ χ : Formula α) (hφ : HasProof (φ →ₘ χ)) (hψ : HasProof (ψ →ₘ χ)) : HasProof ((φ ∨ₘ ψ) →ₘ χ) := by sorry
theorem and_intro (φ ψ χ : Formula α) (hψ : HasProof (φ →ₘ ψ)) (hχ : HasProof (φ →ₘ χ)) : HasProof (φ →ₘ ψ ∧ₘ χ) := by sorry

theorem and_comm (φ ψ : Formula α) (h : HasProof (φ ∨ₘ ψ)) : HasProof (ψ ∨ₘ φ) := by
  simp [Formula.or] at h;
  have s1 := @HasProof.pl3 α φ (¬ₘψ);
  sorry

theorem imp_and_comm (φ ψ : Formula α) : HasProof ((φ ∧ₘ ψ) →ₘ (ψ ∧ₘ φ)) := by sorry

theorem imp_iff_intro (φ ψ : Formula α) : HasProof (((φ →ₘ ψ) ∧ₘ (φ →ₘ ψ)) →ₘ (φ ↔ₘ ψ)) := by sorry

theorem not_imply (φ : Formula α) : HasProof (¬ₘφ →ₘ (φ →ₘ ψ)) := by
  have s1 := @HasProof.pl1 α φ ψ
  have s2 := @HasProof.pl1 α ψ φ
  sorry

theorem imp_and_left (φ ψ : Formula α) : HasProof ((φ ∧ₘ ψ) →ₘ φ) := by
  have s1 := @HasProof.pl1 α φ ψ;
  have s2 := @HasProof.pl2 α φ ψ φ;
  have s3 := HasProof.mp s2 s1;
  sorry;

theorem imp_and_right (φ ψ : Formula α) : HasProof ((φ ∧ₘ ψ) →ₘ ψ) := by
  have s1 := @HasProof.pl1 α φ ψ;
  have s2 := @HasProof.pl2 α φ ψ φ;
  have s3 := HasProof.mp s2 s1;
  sorry;

theorem l2  (φ ψ: Formula α) : HasProof (φ →ₘ ψ →ₘ φ ∧ₘ ψ) := by
  have s1 := @HasProof.pl1 α φ ψ;
  have s2 := @HasProof.pl2 α φ ψ (φ ∧ₘ ψ);
  sorry

theorem lll (φ ψ χ : Formula α) : HasProof ((φ →ₘ ψ) →ₘ ((φ →ₘ χ) →ₘ (φ →ₘ ψ ∧ₘ χ))) := by sorry;

theorem imp_box_and_left (φ ψ : Formula α) : HasProof (□(φ ∧ₘ ψ) →ₘ □φ) := by
  have s1 := imp_and_left φ ψ;
  have s2 := HasProof.nec s1;
  have s3 : HasProof (□((φ ∧ₘ ψ) →ₘ φ) →ₘ (□(φ ∧ₘ ψ) →ₘ □φ)) := @HasProof.k α (φ ∧ₘ ψ) φ;
  have s4 := HasProof.mp s3 s2;
  exact s4;

theorem imp_box_and_right (φ ψ : Formula α) : HasProof (□(φ ∧ₘ ψ) →ₘ □ψ) := by sorry;

theorem box_and_distribution (φ ψ : Formula α) : HasProof (□(φ ∧ₘ ψ) →ₘ (□φ ∧ₘ □ψ)) := by
  have s1 := imp_box_and_left φ ψ;
  have s2 := imp_box_and_right φ ψ;
  have s3 := lll (□(φ∧ₘψ)) (□φ) (□ψ);
  have s4 := HasProof.mp s3 s1;
  have s5 := HasProof.mp s4 s2;
  exact s5;

end HasProof


def Derivation (Γ: Context α) (φ : Formula α): Prop := ∃Δ, (Δ ⊆ Γ) ∧ (HasProof (⋀ₘΔ →ₘ φ))

notation Γ "⊢ₘ" φ => Derivation Γ φ
notation Γ "⊬ₘ" φ => ¬(Γ ⊢ₘ φ)

notation "⊢ₘ" φ => ∅ ⊢ₘ φ
notation "⊬ₘ" φ => ¬(⊢ₘ φ)

theorem deduction (Γ: Context α) (φ ψ : Formula α): (Γ ⊢ₘ (φ →ₘ ψ)) ↔ ((φ::Γ) ⊢ₘ ψ) := by
  apply Iff.intro;
  . intro h;
    rw [Derivation];
    sorry
  . intro h;
    rw [Derivation];
    sorry

def Context.inconsistent (Γ : Context α) := Γ ⊢ₘ ⊥ₘ
def Context.consistent (Γ : Context α) := ¬(inconsistent Γ)
