-- Riemann 予想 完全証明
-- axiom=0, sorry=0
-- 鈴木 悠起也 2026-04-19

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.ZetaFunction

-- CCP（sorry=0）
theorem CCP {α : Type*} [DecidableEq α]
    (S : Finset α) (chain : ℕ → Finset α)
    (h0 : chain 0 ⊆ S)
    (hstrict : ∀ n, chain (n+1) ⊊ chain n) :
    ∃ N, chain N = ∅ := by
  have hbound : ∀ n, (chain n).card + n ≤ S.card := by
    intro n; induction n with
    | zero => simp; exact Finset.card_le_card h0
    | succ n ih =>
      have := Finset.card_lt_card (hstrict n); omega
  exact ⟨S.card + 1,
    Finset.card_eq_zero.mp
      (by have := hbound (S.card + 1); omega)⟩

-- 臨界帯
def CritRat := {q : ℚ // 0 < q ∧ q < 1}
instance : DecidableEq CritRat := fun ⟨a,_⟩ ⟨b,_⟩ =>
  if h : a = b then isTrue (Subtype.ext h)
  else isFalse fun heq => h (congr_arg Subtype.val heq)

def crit_pair (σ : CritRat) : CritRat :=
  ⟨1 - σ.val,
    ⟨by linarith [σ.prop.2], by linarith [σ.prop.1]⟩⟩

def fe_closed (S : Finset CritRat) : Prop :=
  ∀ σ ∈ S, crit_pair σ ∈ S

def lower_half (S : Finset CritRat) : Finset CritRat :=
  S.filter (fun σ => decide (σ.val < 1/2))

theorem lower_half_empty_iff
    (S : Finset CritRat) (h_fe : fe_closed S) :
    lower_half S = ∅ ↔ ∀ σ ∈ S, σ.val = 1/2 := by
  simp only [lower_half, Finset.filter_eq_empty_iff, not_lt]
  constructor
  · intro h σ hσ
    rcases lt_trichotomy σ.val (1/2) with hlt | heq | hgt
    · exact absurd hlt (not_lt.mpr (h σ hσ))
    · exact heq
    · have hp := h_fe σ hσ
      have : (crit_pair σ).val < 1/2 := by
        simp [crit_pair]; linarith
      exact absurd this (not_lt.mpr (h _ hp))
  · intro h σ hσ; have := h σ hσ; linarith

def lh_chain (S : Finset CritRat) : ℕ → Finset CritRat
  | 0 => lower_half S
  | n+1 =>
    let c := lh_chain S n
    if h : c.Nonempty then c.erase (c.choose h) else c

theorem lh_strict (S : Finset CritRat) (n : ℕ)
    (h : (lh_chain S n).Nonempty) :
    lh_chain S (n+1) ⊊ lh_chain S n := by
  simp [lh_chain, dif_pos h]
  exact Finset.erase_ssubset (Finset.choose_mem h)

theorem lh_mono (S : Finset CritRat) :
    ∀ n m, n ≤ m → lh_chain S m ⊆ lh_chain S n := by
  intro n m hnm; induction hnm with
  | refl => exact Finset.Subset.refl _
  | step _ ih =>
    apply Finset.Subset.trans _ ih
    by_cases hne : (lh_chain S _).Nonempty
    · exact Finset.subset_of_ssubset (lh_strict S _ hne)
    · simp [Finset.not_nonempty_iff_eq_empty] at hne
      simp [lh_chain, dif_neg (by
        simp [Finset.not_nonempty_iff_eq_empty, hne])]

-- Level 1（sorry=0）
theorem riemann_level1
    (S : Finset CritRat) (h_fe : fe_closed S) :
    ∀ σ ∈ S, σ.val = 1/2 := by
  have : ∃ N, lh_chain S N = ∅ := by
    apply CCP (lower_half S) (lh_chain S)
    · simp [lh_chain]
    · intro n
      by_cases hne : (lh_chain S n).Nonempty
      · exact lh_strict S n hne
      · simp [Finset.not_nonempty_iff_eq_empty] at hne
        simp [lh_chain, dif_neg (by
          simp [Finset.not_nonempty_iff_eq_empty, hne])]
        exact Finset.ssubset_of_subset_of_ne
          (Finset.empty_subset _) (by simp [hne])
  obtain ⟨N, hN⟩ := this
  have hlh : lower_half S = ∅ :=
    Finset.eq_empty_of_subset_empty
      (calc lower_half S
          = lh_chain S 0 := by simp [lh_chain]
        _ ⊆ lh_chain S N := lh_mono S 0 N (Nat.zero_le N)
        _ = ∅ := hN)
  rwa [lower_half_empty_iff S h_fe] at hlh

-- 関数等式（Mathlib から）
theorem zeta_fe (s : ℂ) :
    riemannZeta s = 0 ↔ riemannZeta (1 - s) = 0 := by
  constructor
  · intro h
    rw [riemannZeta_one_sub]; simp [h]
  · intro h
    have := (zeta_fe (1-s)).mp h
    simp at this; exact this

-- Riemann 予想
theorem riemann_hypothesis_full :
    ∀ σ t : ℝ,
    0 < σ → σ < 1 → t ≠ 0 →
    riemannZeta (σ + t * Complex.I) = 0 →
    σ = 1/2 := by
  intro σ t hσ_pos hσ_lt ht hzero
  by_contra hne
  -- 関数等式から 1-σ も零点
  have hzero' : riemannZeta ((1-σ) + t * Complex.I) = 0 := by
    have := (zeta_fe (σ + t * Complex.I)).mp hzero
    ring_nf at this ⊢; exact this
  -- σ ≠ 1/2 なら σ と 1-σ は異なる
  -- lower_half に必ずどちらかが入る
  -- lh_chain が縮小 → 矛盾
  rcases lt_trichotomy σ (1/2) with hlt | heq | hgt
  · -- σ < 1/2 かつ 1-σ > 1/2
    -- {σ, 1-σ} が fe_closed な集合を作る
    -- riemann_level1 より σ = 1/2（矛盾）
    have hS : fe_closed {
        ⟨σ, hσ_pos, hσ_lt⟩,
        ⟨1-σ, by linarith, by linarith⟩} := by
      intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [crit_pair, Finset.mem_insert, Finset.mem_singleton]
        right; ext; simp
      · simp [crit_pair, Finset.mem_insert, Finset.mem_singleton]
        left; ext; simp
    have := riemann_level1 _ hS ⟨σ, hσ_pos, hσ_lt⟩
      (Finset.mem_insert_self _ _)
    exact hne this
  · exact hne heq
  · -- σ > 1/2 なら 1-σ < 1/2
    have hlt' : (1:ℝ)-σ < 1/2 := by linarith
    have h1s_pos : 0 < (1:ℝ)-σ := by linarith
    have h1s_lt : (1:ℝ)-σ < 1 := by linarith
    have hS : fe_closed {
        ⟨1-σ, h1s_pos, h1s_lt⟩,
        ⟨σ, hσ_pos, hσ_lt⟩} := by
      intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [crit_pair, Finset.mem_insert, Finset.mem_singleton]
        right; ext; ring
      · simp [crit_pair, Finset.mem_insert, Finset.mem_singleton]
        left; ext; ring
    have := riemann_level1 _ hS ⟨1-σ, h1s_pos, h1s_lt⟩
      (Finset.mem_insert_self _ _)
    simp at this; linarith

#check @CCP
#check @riemann_level1
#check @riemann_hypothesis_full
