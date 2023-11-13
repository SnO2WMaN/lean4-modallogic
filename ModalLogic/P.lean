import ModalLogic.Notations
import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic

namespace Finset

lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} : (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp[and_or_left]

end Finset

open Nat Finset

attribute [simp] union_self erase_subset

namespace ModalLogic.P

inductive Prime (α : Type u) : Type u where
  | atom : α → Prime α
  | ctom : α → Prime α
deriving DecidableEq

def Prime.neg {α : Type u} : Prime α → Prime α
  | atom p => ctom p
  | ctom p => atom p

notation "+" p => Prime.atom p
notation "-" p => Prime.ctom p

inductive Formula (α : Type u) : Type u where
  | prime : Prime α → Formula α
  | top : Formula α
  | bot : Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
deriving DecidableEq

namespace Formula

variable {α : Type u} [DecidableEq α]

instance : Coe (Prime α) (Formula α) := ⟨prime⟩
instance : HasTop (Formula α) := ⟨top⟩
instance : HasBot (Formula α) := ⟨bot⟩
instance : HasDisj (Formula α) := ⟨disj⟩
instance : HasConj (Formula α) := ⟨conj⟩

@[simp] lemma conj_neq {φ ψ ξ ζ : Formula α} : (φ ≠ ξ ∨ ψ ≠ ζ) → (φ ⋏ ψ) ≠ (ξ ⋏ ζ) := by
  intro h;
  cases h with
  | inl h => intro h; injection h; contradiction;
  | inr h => intro h; injection h; contradiction;

@[simp] lemma disj_neq {φ ψ ξ ζ : Formula α} : (φ ≠ ξ ∨ ψ ≠ ζ) → ((φ ⋎ ψ) ≠ (ξ ⋎ ζ)) := by
  intro h;
  cases h with
  | inl h => intro h; injection h; contradiction;
  | inr h => intro h; injection h; contradiction;

/-
def isPrime : Formula α → Bool
  | prime _ => true
  | _ => false
-/

def neg : Formula α → Formula α
  | prime p => prime p.neg
  | top => bot
  | bot => top
  | conj φ ψ => disj (neg φ) (neg ψ)
  | disj φ ψ => conj (neg φ) (neg ψ)
instance : HasNeg (Formula α) := ⟨neg⟩

lemma neg_conj_disj (φ ψ : Formula α) : ~(φ ⋏ ψ) = (~φ) ⋎ (~ψ) := by rfl
lemma neg_disj_conj (φ ψ : Formula α) : ~(φ ⋎ ψ) = (~φ) ⋏ (~ψ) := by rfl

@[simp]
def complexity : Formula α → ℕ
  | prime _ => 0
  | top => 0
  | bot => 0
  | conj φ ψ => (max φ.complexity ψ.complexity) + 1
  | disj φ ψ => (max φ.complexity ψ.complexity) + 1

attribute [simp] succ_le

@[simp] lemma complexity_prime : ((prime p).complexity < c + 1) := by aesop
@[simp] lemma complexity_top : ((top : Formula α).complexity < c + 1) := by aesop
@[simp] lemma complexity_bot : ((bot : Formula α).complexity < c + 1) := by aesop
@[simp] lemma complexity_conj_le_lt_right {φ ψ : Formula α} : ((φ ⋏ ψ).complexity ≤ c) → (φ.complexity < c) := by aesop
@[simp] lemma complexity_conj_le_lt_left {φ ψ : Formula α} : ((φ ⋏ ψ).complexity ≤ c) → (ψ.complexity < c) := by aesop
@[simp] lemma complexity_disj_le_lt_right {φ ψ : Formula α} : ((φ ⋎ ψ).complexity ≤ c) → (φ.complexity < c) := by aesop;
@[simp] lemma complexity_disj_le_lt_left {φ ψ : Formula α} : ((φ ⋎ ψ).complexity ≤ c) → (ψ.complexity < c) := by aesop

end Formula

abbrev Sequent (α : Type u) := Finset (Formula α)

open Formula

section Derivation

variable {α : Type u} [DecidableEq α]

inductive Derivation : ℕ → ℕ → Sequent α → Type u where
  | Init : ∀ (Γ) (p : α), ↑(+p) ∈ Γ → ↑(-p) ∈ Γ → (∀ k c, Derivation k c Γ)
  | Top : ∀ (Γ), Formula.top ∈ Γ → (∀ k c, Derivation k c Γ)
  | Conj : ∀ {k c} {Γ φ ψ}, Derivation k c (insert φ $ Γ) → Derivation k c (insert ψ $ Γ) → (∀ {l d}, k < l → c ≤ d → Derivation l d (insert (φ ⋏ ψ) Γ))
  | Disj : ∀ {k c} {Γ φ ψ}, Derivation k c (insert ψ $ insert φ $ Γ) → (∀ {l d}, k < l → c ≤ d → Derivation l d (insert (φ ⋎ ψ) Γ))
  | Cut : ∀ {k c Γ Δ} (φ), (φ.complexity < c) → Derivation k c (insert φ $ Γ) → Derivation k c (insert (~φ) $ Δ) → (∀ {l d}, k < l → c ≤ d → Derivation l d (Γ ∪ Δ))

notation "⊢^{" k "}_{" c "} " Γ => Derivation k c Γ

namespace Derivation

variable {α : Type u} [DecidableEq α]
variable {Γ Δ : Sequent α}

@[simp] def cast {Γ : Sequent α} (he : Γ = Δ) : (⊢^{k}_{c} Γ) → (⊢^{k}_{c} Δ) := by subst he; exact λ d => d;

lemma liftHeight {Γ : Sequent α} (hh : k ≤ l) : (⊢^{k}_{c} Γ) → (⊢^{l}_{c} Γ)
  | Init Γ p hatom hctom _ _ => Init Γ p hatom hctom l c
  | Top Γ htop _ _ => Top Γ htop l c
  | Conj Dφ Dψ hl hd => Conj Dφ Dψ (LT.lt.trans_le hl hh) hd
  | Disj D hl hd => Disj D (LT.lt.trans_le hl hh) hd
  | Cut _ hc Dl Dr hl hd => Cut _ hc Dl Dr (LT.lt.trans_le hl hh) hd

lemma weakening {Γ : Sequent α} (hk : k ≤ k') (hc : c ≤ c') (hΓ : Γ ⊆ Γ') : (⊢^{k}_{c} Γ) → (⊢^{k'}_{c'} Γ')
  | Init Γ p hatom hctom _ _ => Init Γ' p (hΓ hatom) (hΓ hctom) k' c'
  | Top Γ htop _ _ => Top Γ' (hΓ htop) k' c'
  | @Conj _ _ l d Γ φ ψ Dφ Dψ _ _ hl hd => by
      have wD₁ : ⊢^{l}_{d} insert φ Γ' := Dφ.weakening (by simp) (by simp) (insert_subset_insert φ (insert_subset_iff.mp hΓ).2);
      have wD₂ : ⊢^{l}_{d} insert ψ Γ' := Dψ.weakening (by simp) (by simp) (insert_subset_insert ψ (insert_subset_iff.mp hΓ).2);
      exact (Conj wD₁ wD₂ (LT.lt.trans_le hl hk) (LE.le.trans hd hc)).cast (by simp [insert_eq_self]; apply hΓ; simp;);
  | @Disj _ _ l d Γ φ ψ D _ _ hl hd => by
      have wD : ⊢^{l}_{d} insert ψ $ insert φ Γ' := D.weakening (by simp) (by simp) (insert_subset_insert ψ $ insert_subset_insert φ $ (insert_subset_iff.mp hΓ).2);
      exact (Disj wD (LT.lt.trans_le hl hk) (LE.le.trans hd hc)).cast (by simp [insert_eq_self]; apply hΓ; simp;);
  | @Cut _ _ l d Γ Δ φ hcomplex Dl Dr _ _ hl hd => by
      have wDl : ⊢^{l}_{d} insert φ Γ' := Dl.weakening (by simp) (by simp) (insert_subset_insert _ (union_subset_left hΓ));
      have wDr : ⊢^{l}_{d} (insert (~φ) Γ') := Dr.weakening (by simp) (by simp) (insert_subset_insert _ (union_subset_right hΓ));
      exact (Cut _ hcomplex wDl wDr (LT.lt.trans_le hl hk) (LE.le.trans hd hc)).cast (by simp);

lemma inversionDisjAux {Γ : Sequent α} : (⊢^{k}_{c} Γ) → (∀ φ ψ, ⊢^{k}_{c} insert ψ $ insert φ $ Γ.erase (φ ⋎ ψ))
  | Init Γ p hatom hctom _ _, φ, ψ => Init _ p (by simp [hatom]) (by simp [hctom]) k c
  | Top Γ htop _ _, φ, ψ => Top _ (by simp [htop]) k c
  | @Conj _ _ l d Γ ξ ζ Dξ Dζ _ _ hl hd, φ, ψ => by
      have hD₁ : ⊢^{l}_{d} insert ξ $ insert ψ $ insert φ $ erase Γ (φ ⋎ ψ) := (Dξ.inversionDisjAux φ ψ).weakening (by simp) (by simp)
          (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      have hD₂ : ⊢^{l}_{d} insert ζ $ insert ψ $ insert φ $ erase Γ (φ ⋎ ψ) := (Dζ.inversionDisjAux φ ψ).weakening (by simp) (by simp)
          (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      exact (Conj hD₁ hD₂ hl hd).cast (by simp [erase_insert_of_ne, Finset.Insert.comm]);
  | @Disj _ _ l d Γ φ ψ D _ _ hl hd, ξ, ζ => by
      by_cases e : (φ = ξ) ∧ (ψ = ζ);
      . exact @weakening _ _ (l + 1) k d c _ _ (by aesop) hd (by simp [subset_iff, e]; rintro χ hχ (rfl | hhx) <;> simp [*]) ((D.inversionDisjAux φ ψ).liftHeight (by simp));
      . have ne : (φ ⋎ ψ) ≠ (ξ ⋎ ζ) := disj_neq (not_and_or.mp e);
        have hD : ⊢^{l}_{d} insert ψ $ insert φ $ insert ζ $ insert ξ $ erase Γ (ξ ⋎ ζ) := (D.inversionDisjAux ξ ζ).weakening (by simp) (by simp)
          (by simp [subset_iff]; rintro x hx (rfl | rfl | hhx) <;> simp [*]);
        exact (Disj hD hl hd).cast (by simp [erase_insert_of_ne ne, Finset.Insert.comm]);
  | @Cut _ _ l d Γ Δ φ hcomplex Dl Dr _ _ hl hd, ξ, ζ => by
      have hDl : ⊢^{l}_{d} insert φ $ insert ζ $ insert ξ (erase Γ (ξ ⋎ ζ)) := (Dl.inversionDisjAux ξ ζ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      have hDr : ⊢^{l}_{d} insert (~φ) $ insert ζ $ insert ξ (erase Δ (ξ ⋎ ζ)) := (Dr.inversionDisjAux ξ ζ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      exact (Cut _ hcomplex hDl hDr hl hd).cast (by simp [erase_union];);

lemma inversionDisj {Γ : Sequent α} (D : (⊢^{k}_{c} insert (φ ⋎ ψ) Γ)) : (⊢^{k}_{c} insert ψ $ insert φ Γ) := by
  apply (D.inversionDisjAux φ ψ).weakening <;> simp [insert_subset_insert, erase_subset];

lemma inversionConjLAux {Γ : Sequent α} : (⊢^{k}_{c} Γ) → (∀ φ ψ, ⊢^{k}_{c} insert φ $ Γ.erase (φ ⋏ ψ))
  | Init Γ p hatom hctom _ _, φ, ψ => Init _ p (by simp [hatom]) (by simp [hctom]) k c
  | Top Γ htop _ _, φ, ψ => Top _ (by simp [htop]) k c
  | @Conj _ _ l d Γ ξ ζ Dξ Dζ _ _ hl hd, φ, ψ => by
      by_cases e : (ξ = φ) ∧ (ζ = ψ);
      . exact @weakening _ _ (l + 1) k d c _ _ (by aesop) hd (by simp [subset_iff]; rintro χ hχ (rfl | hhx) <;> simp [*]) ((Dξ.inversionConjLAux φ ψ).liftHeight (by simp));
      . have ne : (ξ ⋏ ζ) ≠ (φ ⋏ ψ) := conj_neq (not_and_or.mp e);
        have hD₁ : ⊢^{l}_{d} insert ξ $ insert φ $ erase Γ (φ ⋏ ψ) := (Dξ.inversionConjLAux φ ψ).weakening (by simp) (by simp)
          (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
        have hD₂ : ⊢^{l}_{d} insert ζ $ insert φ $ erase Γ (φ ⋏ ψ) := (Dζ.inversionConjLAux φ ψ).weakening (by simp) (by simp)
          (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
        exact (Conj hD₁ hD₂ hl hd).cast (by simp [erase_insert_of_ne ne, Insert.comm φ]);
  | @Disj _ _ l d Γ ξ ζ D _ _ hl hd, φ, ψ => by
      have hD : ⊢^{l}_{d} insert ζ $ insert ξ $ insert φ $ (erase Γ (φ ⋏ ψ)) := (D.inversionConjLAux φ ψ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro χ hχ (rfl | rfl | hhx) <;> simp [*]);
      exact (Disj hD hl hd).cast (by simp [erase_insert_of_ne, Insert.comm φ])
  | @Cut _ _ l d Γ Δ ξ hcomplex Dl Dr _ _ hl hd, φ, ψ => by
      have hDl : ⊢^{l}_{d} insert ξ $ insert φ (erase Γ (φ ⋏ ψ)) := (Dl.inversionConjLAux φ ψ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      have hDr : ⊢^{l}_{d} insert (~ξ) $ insert φ (erase Δ (φ ⋏ ψ)) := (Dr.inversionConjLAux φ ψ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      exact (Cut _ hcomplex hDl hDr hl hd).cast (by simp [erase_union];);

lemma inversionConjL {Γ : Sequent α} (D : (⊢^{k}_{c} insert (φ ⋏ ψ) Γ)) : (⊢^{k}_{c} insert φ Γ) := by
  apply (D.inversionConjLAux φ ψ).weakening <;> simp [insert_subset_insert, erase_subset];

lemma inversionConjRAux {Γ : Sequent α} : (⊢^{k}_{c} Γ) → (∀ φ ψ, ⊢^{k}_{c} insert ψ $ Γ.erase (φ ⋏ ψ))
  | Init Γ p hatom hctom _ _, φ, ψ => Init _ p (by simp [hatom]) (by simp [hctom]) k c
  | Top Γ htop _ _, φ, ψ => Top _ (by simp [htop]) k c
  | @Conj _ _ l d Γ ξ ζ Dξ Dζ _ _ hl hd, φ, ψ => by
      by_cases e : (ξ = φ) ∧ (ζ = ψ);
      . exact @weakening _ _ (l + 1) k d c _ _ (by aesop) hd (by simp [subset_iff]; rintro χ hχ (rfl | hhx) <;> simp [*]) ((Dζ.inversionConjRAux φ ψ).liftHeight (by simp));
      . have ne : (ξ ⋏ ζ) ≠ (φ ⋏ ψ) := conj_neq (not_and_or.mp e);
        have hD₁ : ⊢^{l}_{d} insert ξ $ insert ψ $ erase Γ (φ ⋏ ψ) := (Dξ.inversionConjRAux φ ψ).weakening (by simp) (by simp)
          (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
        have hD₂ : ⊢^{l}_{d} insert ζ $ insert ψ $ erase Γ (φ ⋏ ψ) := (Dζ.inversionConjRAux φ ψ).weakening (by simp) (by simp)
          (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
        exact (Conj hD₁ hD₂ hl hd).cast (by simp [erase_insert_of_ne ne, Insert.comm ψ]);
  | @Disj _ _ l d Γ ξ ζ D _ _ hl hd, φ, ψ => by
      have hD : ⊢^{l}_{d} insert ζ $ insert ξ $ insert ψ $ (erase Γ (φ ⋏ ψ)) := (D.inversionConjRAux φ ψ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro χ hχ (rfl | rfl | hhx) <;> simp [*]);
      exact (Disj hD hl hd).cast (by simp[Finset.erase_insert_of_ne, Finset.Insert.comm ψ])
  | @Cut _ _ l d Γ Δ ξ hcomplex Dl Dr _ _ hl hd, φ, ψ => by
      have hDl : ⊢^{l}_{d} insert ξ $ insert ψ (erase Γ (φ ⋏ ψ)) := (Dl.inversionConjRAux φ ψ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      have hDr : ⊢^{l}_{d} insert (~ξ) $ insert ψ (erase Δ (φ ⋏ ψ)) := (Dr.inversionConjRAux φ ψ).weakening (by simp) (by simp)
        (by simp [subset_iff]; rintro x hx (rfl | hhx) <;> simp [*]);
      exact (Cut _ hcomplex hDl hDr hl hd).cast (by simp [erase_union];);

lemma inversionConjR {Γ : Sequent α} (D : (⊢^{k}_{c} insert (φ ⋏ ψ) Γ)) : (⊢^{k}_{c} insert ψ Γ) := by
  apply (D.inversionConjRAux φ ψ).weakening <;> simp [insert_subset_insert, erase_subset];

lemma reduction {Γ Δ : Sequent α} {φ : Formula α} (hc : φ.complexity ≤ c + 1) : (⊢^{k}_{c + 1} (insert φ Γ)) → (⊢^{k}_{c + 1} (insert (~φ) Δ)) → (⊢^{k + 2}_{c + 1} (Γ ∪ Δ)) := by
  intro Dl Dr;
  cases φ with
  | conj φ ψ =>
      have C₁ : ⊢^{k + 1}_{c + 1} (insert (neg φ) (Γ ∪ Δ)) := (Cut _ (complexity_conj_le_lt_left hc) Dl.inversionConjR Dr.inversionDisj (by simp) (by simp)).cast (by simp);
      have C₂ : ⊢^{k + 2}_{c + 1} (Γ ∪ Δ) := (Cut _ (complexity_conj_le_lt_right hc) (Dl.inversionConjL.liftHeight (by simp)) C₁ (by simp) (by simp)).cast (by simp);
      exact C₂;
  | disj φ ψ =>
      have C₁ : ⊢^{k + 1}_{c + 1} (insert φ (Γ ∪ Δ)) := (Cut _ (complexity_disj_le_lt_left hc) Dl.inversionDisj Dr.inversionConjR (by simp) (by simp)).cast (by simp);
      have C₂ : ⊢^{k + 2}_{c + 1} (Γ ∪ Δ) := (Cut _ (complexity_disj_le_lt_right hc) C₁ (Dr.inversionConjL.liftHeight (by simp)) (by simp) (by simp)).cast (by simp);
      exact C₂;
  | _ => exact Cut _ (by simp) Dl Dr (by simp) (by simp);

lemma reductionPrime {Γ Δ : Sequent α} {p : α} : (⊢^{k}_{0} (insert ↑(+p) Γ)) → (⊢^{l}_{0} (insert ↑(-p) Δ)) → (⊢^{k + l}_{0} (Γ ∪ Δ)) := by
  intro D₁ D₂;
  induction k with
  | zero =>
    cases D₁ with
    | Init Γ q hatom hctom =>
        by_cases hpq : p = q
        . simp_all [hpq];
        . apply Init _ q (by aesop) (by aesop);
    | Top Γ htop => apply Top (Γ ∪ Δ) (by aesop);
      -- have C₂ : ⊢^{l}_{0} (insert (↑p) (Γ ∪ Δ)) := (Cut _ (by simp) D₁ C₁ (by simp) (by simp)).cast (by simp);
  | succ k ih =>
      sorry;

lemma reduceCut1 {Γ : Sequent α} : (⊢^{k}_{1} Γ) → (⊢^{k}_{0} Γ)
  | Init Γ p hatom hctom _ _ => Init Γ p hatom hctom k 0
  | Top Γ htop _ _ => Top Γ htop k 0
  | Conj Γ φ ψ Dφ Dψ => Conj _ _ _ (Dφ.reduceCut1) (Dψ.reduceCut1)
  | Disj Γ φ ψ D => Disj Γ φ ψ (D.reduceCut1)
  | Cut Γ₁ Γ₂ φ hCut D₁ D₂ =>
    match φ with
    | .prime p => by sorry; -- reductionPrime (red D₁) (red D₂)
    | .top => by sorry;
    | .bot => by sorry;

lemma reduceCutLt2 {Γ : Sequent α} : (⊢^{k}_{c + 1} Γ) → (⊢^{2 ^ k}_{c} Γ)
  | Init Γ p hatom hctom _ _ => by apply Init _ _ hatom hctom;
  | Top Γ htop _ _ => by apply Top _ htop;
  | Conj Dφ Dψ _ _ => reduceCutLt2 $ Conj Dφ Dψ (by assumption) (by assumption)
  | Disj D _ _ => reduceCutLt2 $ Disj D (by assumption) (by assumption)
  | @Cut _ _ l d Γl Γr  φ hcomplex Dl Dr _ _ hl hd =>
      -- have RR := Dr.reduceCutLt2;
      -- have := reduction (by sorry) (Dl.reduceCutLt2) (Dr.reduceCutLt2);
      -- match φ with
      -- | .prime p => sorry -- reductionPrime (Dl.reduceCutLt2) (Dr.reduceCutLt2)
      -- | .top => sorry
      -- | .bot => sorry
      -- | .conj φ ψ => sorry -- reduction (Nat.lt_add_one_iff.mp hcomplex) (Dl.reduceCutLt2) (Dr.reduceCutLt2)
      -- | .disj φ ψ => sorry
-- termination_by reduceCutLt2 D => by sorry
      -- have hDl := reduceCutLt2;
      -- have hDr := @reduceCutLt2 k c (insert φ Γr);
      -- sorry;

      -- induction c with
      -- | zero =>
      --     have hDl : ⊢^{k}_{0} (insert φ Δl) := Dl.reduceCut1;
      --     have hDr : ⊢^{k}_{0} (insert (~φ) Δr) := Dr.reduceCut1;
      --     exact (Cut hcomplex hDl hDr hk hc).cast (by simp);
      -- | succ c ih =>
      --     have hDl := Dl.reduceCutLt2;
      --     have hDr := Dr.reduceCutLt2;

          -- exact (Cut hcomplex hDl hDr hk hc).cast (by simp);

  -- | @Cut _ _ l d Δl Δr φ hcomplex Dl Dr _ _ hl hd => by
    /-
      match φ with
      | .prime p => by sorry; -- reductionPrime (red Dl) (red Dr)
      | .top => by sorry;
      | .bot => by sorry;
      | .conj φ ψ => by sorry;
      | .disj φ ψ => have a := (D₁.reduceCutLt2); have b := (D₂.reduceCutLt2);
-/
/-
noncomputable def reduceCutLt2 {Γ : Sequent α} : (⊢ᶜ[< c + 2] Γ) → (⊢ᶜ[< c + 1] Γ)
  | Init Γ p ha hc => Init Γ p ha hc
  | top Γ ht => top Γ ht
  | conj Γ φ ψ Dφ Dψ => conj Γ φ ψ (Dφ.reduceCutLt2) (Dψ.reduceCutLt2)
  | disj Γ φ ψ D => disj Γ φ ψ (D.reduceCutLt2)
  | Cut _ _ φ hCut D₁ D₂ =>
    match φ with
    | .prime _ => reductionPrime (D₁.reduceCutLt2) (D₂.reduceCutLt2)
    | _ => reduction (Nat.lt_add_one_iff.mp hCut) (D₁.reduceCutLt2) (D₂.reduceCutLt2)
-/

lemma CutElimination {Γ : Sequent α} : {c : ℕ} → (⊢^{k}_{c} Γ) → (⊢^{2 ^ (2 ^ k * m)}_{0} Γ)
  | 0, D => sorry -- D.replaceCondition (by simp)
  | c + 1, D => sorry

/-
noncomputable def CutMax {Γ : Sequent α} : (⊢^{k}_{c} Γ) → ((c : ℕ) × (⊢ᶜ[< c] Γ))
  | Init Γ p ha hc => ⟨0, Init Γ p ha hc⟩
  | top Γ ht => ⟨0, top Γ ht⟩
  | conj Γ φ ψ Dφ Dψ =>
      let ⟨c₁, D₁⟩ := Dφ.CutMax;
      let ⟨c₂, D₂⟩ := Dψ.CutMax;
      ⟨max c₁ c₂, conj Γ φ ψ (D₁.liftCutComplexity (by simp)) (D₂.liftCutComplexity (by simp))⟩
  | disj Γ φ ψ D =>
      let ⟨c, D⟩ := D.CutMax;
      ⟨c, disj Γ φ ψ (D.liftCutComplexity (by simp))⟩
  | Cut Γ₁ Γ₂ φ _ D₁ D₂ =>
      let ⟨c₁, D₁⟩ := D₁.CutMax;
      let ⟨c₂, D₂⟩ := D₂.CutMax;
      ⟨max (max c₁ c₂) (φ.complexity + 1), Cut Γ₁ Γ₂ φ (by simp) (D₁.liftCutComplexity (by simp)) (D₂.liftCutComplexity (by simp))⟩

noncomputable def CutElimination : (⊢ᶜ Γ) → (⊢ Γ) := λ D => (D.CutMax.2).CutElimination'
-/

end Derivation

end Derivation

end ModalLogic.P
