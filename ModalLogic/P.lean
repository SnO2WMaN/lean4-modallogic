import ModalLogic.Notations
import Mathlib.Data.Finset.Basic

namespace Finset

lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} : (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp[and_or_left]

end Finset

open Nat Finset

attribute [simp] union_self

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

def complexity : Formula α → ℕ
  | prime _ => 0
  | top => 0
  | bot => 0
  | conj φ ψ => (max φ.complexity ψ.complexity) + 1
  | disj φ ψ => (max φ.complexity ψ.complexity) + 1

/-
lemma complexity0 {φ : Formula α} : φ.complexity = 0 → (φ.isPrime = true) := by
  intro h;
  cases φ with
  | conj _ _ => simp [complexity] at h;
  | disj _ _ => simp [complexity] at h;
  | _ => rfl;

lemma complexity1 {φ : Formula α} : φ.complexity = 1 → (∃ (ψ ξ : Formula α), (ψ.isPrime = true ∧ ξ.isPrime = true) ∧ ((φ = ψ ⋏ ξ) ∨ (φ = ψ ⋎ ξ))) := by
  intro h;
  cases φ with
  | conj ψ ξ => simp [complexity] at h; existsi ψ, ξ; exact ⟨⟨complexity0 h.left, complexity0 h.right⟩, Or.inl rfl⟩;
  | disj ψ ξ => simp [complexity] at h; existsi ψ, ξ; exact ⟨⟨complexity0 h.left, complexity0 h.right⟩, Or.inr rfl⟩;
  | _ => simp [complexity] at h;
-/
/-
def complexity₂ (φ : Formula α) : ℕ :=
  if _ : isConnected φ then
      match φ with
      | conj φ ψ => (max φ.complexity ψ.complexity) + 1
      | disj φ ψ => (max φ.complexity ψ.complexity) + 1
    else 0

@[simp] def complexity₂_atom {p : α} : complexity₂ (atom p) = 0 := rfl
@[simp] def complexity₂_ctom {p : α} : complexity₂ (ctom p) = 0 := rfl
@[simp] def complexity₂_top : complexity₂ (top : Formula α) = 0 := rfl
@[simp] def complexity₂_bot : complexity₂ (bot : Formula α) = 0 := rfl
-/

/-
@[simp] lemma complexity_atom {p : α} : (atom p).complexity = 0 := rfl
@[simp] lemma complexity_atom_upper {p : α} : (atom p).complexity < 1 := by simp [complexity]
-/

@[simp] lemma complexity_conj2 {φ ψ : Formula α} : (max φ.complexity ψ.complexity) < ((φ ⋏ ψ).complexity) := by simp [complexity];
@[simp] lemma complexity_disj2 {φ ψ : Formula α} : (max φ.complexity ψ.complexity) < ((φ ⋎ ψ).complexity) := by simp [complexity];

@[simp] lemma complexity_conj_max {c} {φ ψ : Formula α} : ((φ ⋏ ψ).complexity ≤ c) → (φ.complexity < c ∧ ψ.complexity < c) := λ h => max_lt_iff.mp h
@[simp] lemma complexity_disj_max {c} {φ ψ : Formula α} : ((φ ⋎ ψ).complexity ≤ c) → (φ.complexity < c ∧ ψ.complexity < c) := λ h => max_lt_iff.mp h

end Formula

abbrev Sequent (α : Type u) := Finset (Formula α)

open Formula

section Derivation

variable {α : Type u} [DecidableEq α]

inductive DerivationCR (CC : Formula α → Prop) : Sequent α → Type u where
  | axm : ∀ (Γ) (p : α), ↑(+p) ∈ Γ → ↑(-p) ∈ Γ → DerivationCR CC Γ
  | top : ∀ (Γ), Formula.top ∈ Γ → DerivationCR CC Γ
  | conj : ∀ (Γ φ ψ), DerivationCR CC (insert φ $ Γ) → DerivationCR CC (insert ψ $ Γ) → DerivationCR CC (insert (φ ⋏ ψ) Γ)
  | disj : ∀ (Γ φ ψ), DerivationCR CC (insert φ $ insert ψ $ Γ) → DerivationCR CC (insert (φ ⋎ ψ) Γ)
  | cut : ∀ (Γ Δ φ), CC φ → DerivationCR CC (insert φ $ Γ) → DerivationCR CC (insert (~φ) $ Δ) → DerivationCR CC (Γ ∪ Δ)
notation "⊢ᶜ[" CC "] " Γ => DerivationCR CC Γ

abbrev DerivationWithoutCut (Γ : Sequent α) := ⊢ᶜ[λ _ => False] Γ
notation "⊢ " Γ => DerivationWithoutCut Γ

abbrev DerivationWithCut (Γ : Sequent α) :=  ⊢ᶜ[λ _ => True] Γ
notation "⊢ᶜ " Γ => DerivationWithCut Γ

abbrev DerivationLtCutComplexity (c : ℕ) (Γ : Sequent α) := ⊢ᶜ[λ φ => φ.complexity < c] Γ
notation "⊢ᶜ[<" c "] " Γ => DerivationLtCutComplexity c Γ

namespace DerivationCR

variable {α : Type u} [DecidableEq α]
variable {Γ Δ : Sequent α}

@[simp]
def height {Γ : Sequent α} : DerivationCR P Γ → ℕ
  | axm _ _ _ _ => 0
  | top _ _ => 0
  | conj _ _ _ D₁ D₂ => (max D₁.height D₂.height) + 1
  | disj _ _ _ d => d.height + 1
  | cut _ _ _ _ D₁ D₂ => (max D₁.height D₂.height) + 1

@[simp]
def height2 {Γ : Sequent α} : (⊢ᶜ[P] Γ) → (ℕ × ⊢ᶜ[P] Γ)
  | axm Γ p ha hc => ⟨0, axm Γ p ha hc⟩
  | top Γ ht => ⟨0, top Γ ht⟩
  | conj Γ φ ψ D₁ D₂ => ⟨(max D₁.height D₂.height) + 1, conj Γ φ ψ D₁ D₂⟩
  | disj Γ φ ψ D => ⟨D.height + 1, disj Γ φ ψ D⟩
  | cut Γ₁ Γ₂ φ hp D₁ D₂ => ⟨(max D₁.height D₂.height) + 1, cut Γ₁ Γ₂ φ hp D₁ D₂⟩

/-
@[simp] lemma height_axm (Γ : Sequent α) (p : α) (ha : atom p ∈ Γ) (hc : ctom p ∈ Γ) : (axm (P := P) Γ p ha hc).height = 0 := rfl
@[simp] lemma height_top (Γ : Sequent α) (ht : Formula.top ∈ Γ) : (top (P := P) Γ ht).height = 0 := rfl
@[simp] lemma height_conj (D₁ : ⊢ᶜ[P] (insert φ Γ)) (D₂ : ⊢ᶜ[P] (insert ψ Γ)) : (conj Γ φ ψ D₁ D₂).height = (max D₁.height D₂.height) + 1 := rfl
@[simp] lemma height_disj (D : ⊢ᶜ[P] (insert φ $ insert ψ Γ)) : (disj Γ φ ψ D).height = D.height + 1 := rfl
@[simp] lemma height_cut (D₁ : ⊢ᶜ[P] (insert φ Γ)) (D₂ : ⊢ᶜ[P] (insert (~φ) Δ)) : (cut Γ Δ φ hp D₁ D₂).height = (max D₁.height D₂.height) + 1 := rfl
-/

@[simp] def cast (he : Γ = Δ) : (⊢ᶜ[P] Γ) → (⊢ᶜ[P] Δ) := by subst he; exact λ d => d;
@[simp] lemma cast_HeightPreserving (h : ⊢ᶜ[P] Γ) (he : Γ = Δ) : (h.cast he).height = h.height := by subst he; trivial;

def replaceCondition {Γ : Sequent α} {P Q : Formula α → Prop} (h : ∀ φ, P φ → Q φ) : (⊢ᶜ[P] Γ) → (⊢ᶜ[Q] Γ)
  | axm Γ p ha hc => axm Γ p ha hc
  | top Γ ht => top Γ ht
  | conj Γ φ ψ D₁ D₂ => conj Γ φ ψ (D₁.replaceCondition h) (D₂.replaceCondition h)
  | disj Γ φ ψ D => disj Γ φ ψ (D.replaceCondition h)
  | cut Γ₁ Γ₂ φ hp D₁ D₂ => cut Γ₁ Γ₂ φ (h φ hp) (D₁.replaceCondition h) (D₂.replaceCondition h)

lemma liftCutComplexity (h : i ≤ j) : (⊢ᶜ[< i] Γ) → (⊢ᶜ[< j] Γ) := replaceCondition (λ _ hp => Nat.lt_of_lt_of_le hp h)

def weakening {Γ: Sequent α} : (⊢ᶜ[P] Γ) → (∀ {Δ : Sequent α}, Γ ⊆ Δ → ⊢ᶜ[P] Δ)
  | axm Γ p ha hc, Δ, h => axm Δ p (h ha) (h hc)
  | top Γ ht, Δ, h => top Δ (h ht)
  | conj Γ φ ψ D₁ D₂, Δ, h =>
      let wD₁ : ⊢ᶜ[P] insert φ Δ := D₁.weakening (insert_subset_insert φ (insert_subset_iff.mp h).2);
      let wD₂ : ⊢ᶜ[P] insert ψ Δ := D₂.weakening (insert_subset_insert ψ (insert_subset_iff.mp h).2);
      (conj Δ φ ψ wD₁ wD₂).cast (by simp; exact (insert_subset_iff.mp h).1)
  | disj Γ φ ψ D, Δ, h =>
      let wD : ⊢ᶜ[P] (insert φ $ insert ψ Δ) := D.weakening (insert_subset_insert φ (insert_subset_insert ψ (insert_subset_iff.mp h).2));
      (disj Δ φ ψ wD).cast (by simp; exact (insert_subset_iff.mp h).1)
  | cut Γ₁ Γ₂ φ hp D₁ D₂, Δ, h =>
      let wD₁ : ⊢ᶜ[P] (insert φ Δ) := D₁.weakening (insert_subset_insert _ (union_subset_left h));
      let wD₂ : ⊢ᶜ[P] (insert (~φ) Δ) := D₂.weakening (insert_subset_insert _ (union_subset_right h));
      (cut Δ Δ φ hp wD₁ wD₂).cast (by simp)

def weakening₁ : (⊢ᶜ[P] Γ) → (∀ {φ}, ⊢ᶜ[P] (insert φ Γ)) := by
  intro D φ;
  exact D.weakening (subset_insert φ Γ)

lemma weakening_HeightPreserving (D : ⊢ᶜ[P] Γ) (h : Γ ⊆ Δ) : (D.weakening h).height = D.height := by
  induction D generalizing Δ <;> simp [weakening, height];
  sorry;
  sorry;
  sorry;

def inversionDisjAux {Γ : Sequent α} : (⊢ᶜ[CC] Γ) → (∀ φ ψ, ⊢ᶜ[CC] insert ψ $ insert φ $ Γ.erase (φ ⋎ ψ))
  | axm Γ p ha hc, φ, ψ => axm _ p (by simp [ha]) (by simp [hc])
  | top Γ ht, φ, ψ => top _ (by simp [ht])
  | conj Γ φ ψ D₁ D₂, φ', ψ' =>
      have iD₁ := D₁.inversionDisjAux φ' ψ';
      have iD₂ := D₂.inversionDisjAux φ' ψ';
      sorry
      -- let iD₁ := D₁.inversionDisj φ' ψ';
      -- let iD₂ := D₂.inversionDisj φ' ψ';
      -- (conj _ _ _ iD₁ iD₂).cast (by sorry)
  | disj Γ φ ψ D, φ', ψ' => sorry
      -- let iD : ⊢ᶜ[P] (insert φ $ insert ψ $ Γ.erase (φ' ⋎ ψ')) := D.inversionDisj φ' ψ';
      -- (disj _ _ _ iD).cast (by simp)
  | cut Γ₁ Γ₂ φ hp D₁ D₂, φ', ψ' => sorry
      -- let iD₁ : ⊢ᶜ[P] (insert φ $ Γ₁.erase (φ' ⋎ ψ')) := D₁.inversionDisj φ' ψ';
      -- let iD₂ : ⊢ᶜ[P] (insert (~φ) $ Γ₂.erase (φ' ⋎ ψ')) := D₂.inversionDisj φ' ψ';
      -- (cut _ _ _ hp iD₁ iD₂).cast (by simp)

def inversionDisj {Γ : Sequent α} (D : (⊢ᶜ[P] insert (φ ⋎ ψ) Γ)) : (⊢ᶜ[P] insert ψ $ insert φ Γ) := by
  apply (D.inversionDisjAux φ ψ).weakening;
  apply insert_subset_insert;
  apply insert_subset_insert;
  apply erase_insert_subset;

def inversionConjLAux {Γ : Sequent α} : (⊢ᶜ[P] Γ) → (∀ φ ψ, ⊢ᶜ[P] insert φ $ Γ.erase (φ ⋏ ψ))
  | axm Γ p ha hc, φ, ψ => axm _ p (by simp [ha]) (by simp [hc])
  | top Γ ht, φ, ψ => top _ (by simp [ht])
  | conj Γ φ' ψ' Dφ Dψ, φ, ψ => by
      by_cases e : (φ' = φ) ∧ (ψ' = ψ)
      . exact (inversionConjLAux Dφ φ ψ).weakening (by simp [subset_iff]; intro ξ hξ; sorry;)
      . have n : (φ ⋏ ψ) ≠ (φ' ⋏ ψ') := by sorry;

        have Dφ' : ⊢ᶜ[P] (insert φ' $ insert φ $ Γ.erase (φ' ⋏ ψ')) := sorry;
        have Dψ' : ⊢ᶜ[P] (insert ψ' $ insert φ $ Γ.erase (φ' ⋏ ψ')) := sorry;
        apply (conj _ _ _ Dφ' Dψ').cast;
        sorry;
        -- simp [erase_insert_of_ne];

        -- have Dφ : ⊢ᶜ[P] insert φ $ Γ.erase (φ' ⋏ ψ') := D₁.inversionConj φ' ψ';
  | disj Γ φ ψ D, ξ, χ => by
      have DΓ := D.inversionConjLAux ξ χ;
      sorry
      -- apply (disj _ _ _ DΓ).cast;

  | cut Γ₁ Γ₂ φ hp D₁ D₂, ψ, ξ => by
      have DΓ₁ : ⊢ᶜ[P] insert φ $ insert ψ (erase Γ₁ (ψ ⋏ ξ)) := (D₁.inversionConjLAux ψ ξ).weakening (by simp [subset_iff]; intro ζ hζ; sorry;);
      have DΓ₂ : ⊢ᶜ[P] insert (~φ) $ insert ψ (erase Γ₂ (ψ ⋏ ξ)) := (D₂.inversionConjLAux ψ ξ).weakening (by simp [subset_iff]; intro ζ hζ; sorry;);
      apply (cut _ _ _ hp DΓ₁ DΓ₂).cast;
      simp [erase_union];

  /--
  | disj Γ φ ψ D, φ', ψ' =>
      let iD : ⊢ᶜ[P] (insert φ $ insert ψ $ Γ.erase (φ' ⋎ ψ')) := D.inversionDisj φ' ψ';
      (disj _ _ _ iD).cast (by simp)
  | cut Γ₁ Γ₂ φ hp D₁ D₂, φ', ψ' =>
      let iD₁ : ⊢ᶜ[P] (insert φ $ Γ₁.erase (φ' ⋎ ψ')) := D₁.inversionDisj φ' ψ';
      let iD₂ : ⊢ᶜ[P] (insert (~φ) $ Γ₂.erase (φ' ⋎ ψ')) := D₂.inversionDisj φ' ψ';
      (cut _ _ _ hp iD₁ iD₂).cast (by simp)
-/

def inversionConjL {Γ : Sequent α} (D : (⊢ᶜ[P] insert (φ ⋏ ψ) Γ)) : (⊢ᶜ[P] insert φ Γ) := by
  apply (D.inversionConjLAux φ ψ).weakening;
  apply insert_subset_insert;
  apply erase_insert_subset;

def inversionConjRAux {Γ : Sequent α} : (⊢ᶜ[P] Γ) → (∀ φ ψ, ⊢ᶜ[P] insert ψ $ Γ.erase (φ ⋏ ψ))
  | axm Γ p ha hc, φ, ψ => axm _ p (by simp [ha]) (by simp [hc])
  | top Γ ht, φ, ψ => top _ (by simp [ht])
  | conj Γ φ' ψ' Dφ Dψ, φ, ψ => by
      by_cases e : (φ' = φ) ∧ (ψ' = ψ)
      . exact (inversionConjRAux Dφ φ ψ).weakening (by simp [subset_iff]; intro ξ hξ; sorry;)
      . have n : (φ ⋏ ψ) ≠ (φ' ⋏ ψ') := by sorry;
        have Dφ' : ⊢ᶜ[P] (insert φ' $ insert φ $ Γ.erase (φ' ⋏ ψ')) := sorry;
        have Dψ' : ⊢ᶜ[P] (insert ψ' $ insert φ $ Γ.erase (φ' ⋏ ψ')) := sorry;
        apply (conj _ _ _ Dφ' Dψ').cast;
        sorry
  | disj Γ φ ψ D, φ', ψ' => sorry
  | cut Γ₁ Γ₂ φ hp D₁ D₂, φ', ψ' => sorry

def inversionConjR {Γ : Sequent α} (D : (⊢ᶜ[P] insert (φ ⋏ ψ) Γ)) : (⊢ᶜ[P] insert ψ Γ) := by
  apply (D.inversionConjRAux φ ψ).weakening;
  apply insert_subset_insert;
  apply erase_insert_subset;

lemma inversionDisj_HeightPreserving (D : ⊢ᶜ[P] Γ) : (D.inversionDisjAux φ ψ).height = D.height := by
  induction D <;>
  simp [inversionDisj, height];
  sorry;
  sorry;
  sorry;

lemma inversionConjL_HeightPreserving (D : ⊢ᶜ[P] Γ) : (D.inversionConjLAux φ ψ).height = D.height := by
  induction D <;>
  simp [inversionConjL, height];
  sorry;
  sorry;
  sorry;

lemma inversionConjR_HeightPreserving (D : ⊢ᶜ[P] Γ) : (D.inversionConjRAux φ ψ).height = D.height := by
  induction D <;>
  simp [inversionConjR, height];
  sorry;
  sorry;
  sorry;

lemma reduceCut1 {Γ : Sequent α} : (⊢ᶜ[< 1] Γ) → (⊢ᶜ[< 0] Γ)
  | axm Γ p ha hc => axm Γ p ha hc
  | top Γ ht => top Γ ht
  | conj Γ φ ψ Dφ Dψ => conj _ _ _ (Dφ.reduceCut1) (Dψ.reduceCut1)
  | disj Γ φ ψ D => disj Γ φ ψ (D.reduceCut1)
  | cut _ _ φ hcut D₁ D₂ =>
    match φ with
    | .prime p => by sorry; -- reductionPrime (red D₁) (red D₂)
    | .top => by sorry;
    | .bot => by sorry;

lemma reduction {Γ Δ : Sequent α} {φ : Formula α} (hc : φ.complexity ≤ c + 1) : (⊢ᶜ[< c + 1] (insert φ Γ)) → (⊢ᶜ[< c + 1] (insert (~φ) Δ)) → (⊢ᶜ[< c + 1] (Γ ∪ Δ)) := by
  intro D₁ D₂;
  cases φ with
  | conj φ ψ =>
    have C₁ : ⊢ᶜ[< c + 1] insert (~φ) (Γ ∪ Δ) := by have := cut _ _ _ ((complexity_conj_max hc).2) (inversionConjR D₁) (inversionDisj D₂); simp [insert_union] at this; exact this;
    have C₂ : ⊢ᶜ[< c + 1] Γ ∪ Δ := by have := cut _ _ _ ((complexity_conj_max hc).1) (inversionConjL D₁) C₁; simp [insert_union] at this; exact this;
    exact C₂;
  | disj φ ψ =>
    have C₁ : ⊢ᶜ[< c + 1] insert φ (Γ ∪ Δ) := by have := cut _ _ _ ((complexity_disj_max hc).2) D₁.inversionDisj D₂.inversionConjR; simp [insert_union] at this; exact this;
    have C₂ : ⊢ᶜ[< c + 1] Γ ∪ Δ := by have := cut _ _ _ ((complexity_disj_max hc).1) C₁ D₂.inversionConjL; simp at this; exact this;
    exact C₂;
  | _ => exact cut _ _ _ (by simp [complexity]) D₁ D₂;

lemma reductionPrime {Γ Δ : Sequent α} {p : Prime α} : (⊢ᶜ[< c] (insert ↑p Γ)) → (⊢ᶜ[< c] (insert (~↑p) Δ)) → (⊢ᶜ[< c] (Γ ∪ Δ)) := by
  intro D₁ D₂;
  cases p with
  | _ p =>
    let k := D₁.height;
    induction k with
    | zero => sorry;
    | succ n ih => sorry; -- exact ih;
  -- | conj => simp [isPrime] at hp;
  -- | disj => simp [isPrime] at hp;
  -- | _ => exact cut _ _ _ (by simp [complexity]; exact hc) D₁ D₂;

noncomputable def reduceCutLt2 {Γ : Sequent α} : (⊢ᶜ[< c + 2] Γ) → (⊢ᶜ[< c + 1] Γ)
  | axm Γ p ha hc => axm Γ p ha hc
  | top Γ ht => top Γ ht
  | conj Γ φ ψ Dφ Dψ => conj Γ φ ψ (Dφ.reduceCutLt2) (Dψ.reduceCutLt2)
  | disj Γ φ ψ D => disj Γ φ ψ (D.reduceCutLt2)
  | cut _ _ φ hcut D₁ D₂ =>
    match φ with
    | .prime _ => reductionPrime (D₁.reduceCutLt2) (D₂.reduceCutLt2)
    | _ => reduction (Nat.lt_add_one_iff.mp hcut) (D₁.reduceCutLt2) (D₂.reduceCutLt2)

noncomputable def CutElimination' {Γ : Sequent α} : {c : ℕ} → (⊢ᶜ[< c] Γ) → (⊢ Γ)
  | 0, D => D.replaceCondition (by simp)
  | 1, D => D.reduceCut1.CutElimination'
  | _ + 2, D => (D.reduceCutLt2).CutElimination'

noncomputable def cutMax {Γ : Sequent α} : (⊢ᶜ Γ) → ((c : ℕ) × (⊢ᶜ[< c] Γ))
  | axm Γ p ha hc => ⟨0, axm Γ p ha hc⟩
  | top Γ ht => ⟨0, top Γ ht⟩
  | conj Γ φ ψ Dφ Dψ =>
      let ⟨c₁, D₁⟩ := Dφ.cutMax;
      let ⟨c₂, D₂⟩ := Dψ.cutMax;
      ⟨max c₁ c₂, conj Γ φ ψ (D₁.liftCutComplexity (by simp)) (D₂.liftCutComplexity (by simp))⟩
  | disj Γ φ ψ D =>
      let ⟨c, D⟩ := D.cutMax;
      ⟨c, disj Γ φ ψ (D.liftCutComplexity (by simp))⟩
  | cut Γ₁ Γ₂ φ _ D₁ D₂ =>
      let ⟨c₁, D₁⟩ := D₁.cutMax;
      let ⟨c₂, D₂⟩ := D₂.cutMax;
      ⟨max (max c₁ c₂) (φ.complexity + 1), cut Γ₁ Γ₂ φ (by simp) (D₁.liftCutComplexity (by simp)) (D₂.liftCutComplexity (by simp))⟩

noncomputable def cutElimination : (⊢ᶜ Γ) → (⊢ Γ) := λ D => (D.cutMax.2).CutElimination'

end DerivationCR

end Derivation

end ModalLogic.P
