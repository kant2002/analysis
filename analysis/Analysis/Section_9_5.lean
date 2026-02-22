import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Аналіз I, Розділ 9.5: Ліві та праві границі

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:
- Ліві та праві односторонні границі.
-/

namespace Chapter9

/-- Визначення 9.5.1. Ми надаємо лівим і правим границям «сміттеве» значення 0, якщо границя не існує. -/
abbrev RightLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev right_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h : RightLimitExists X f x₀ then h.choose else 0

abbrev LeftLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev left_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h: LeftLimitExists X f x₀ then h.choose else 0

theorem right_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)) : RightLimitExists X f x₀ ∧ right_limit X f x₀ = L := by
  have h' : RightLimitExists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Ioi x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem left_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)) : LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L := by
  have h' : LeftLimitExists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Iio x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem right_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: RightLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (right_limit X f x₀)) := by
  simp [right_limit, h]; exact h.choose_spec

theorem left_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: LeftLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]; exact h.choose_spec

/-- Приклад 9.5.2. Друга частина цього прикладу вже не діє, оскільки ми призначаємо нашим функціям «сміттеві» значення замість того, щоб залишати їх невизначеними. -/
example : right_limit .univ Real.sign 0 = 1 := by sorry

example : left_limit .univ Real.sign 0 = -1 := by sorry

theorem right_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: RightLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Ioi x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (right_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp had _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

theorem left_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: LeftLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Iio x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (left_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp had _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

/-- Твердження 9.5.3 -/
theorem ContinuousAt.iff_eq_left_right_limit {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: x₀ ∈ X)
  (had_left: AdherentPt x₀ (X ∩ .Iio x₀)) (had_right: AdherentPt x₀ (X ∩ .Ioi x₀)) :
  ContinuousWithinAt f X x₀ ↔ (RightLimitExists X f x₀ ∧ right_limit X f x₀ = f x₀) ∧ (LeftLimitExists X f x₀ ∧ left_limit X f x₀ = f x₀) := by
  -- Доведення написане так, щоб відповідати структурі оригінального тексту.
  constructor
  . sorry
  intro ⟨ ⟨ hre, hright⟩, ⟨ hle, lheft ⟩ ⟩
  set L := f x₀
  have := (ContinuousWithinAt.tfae X f h).out 0 2
  rw [this]
  intro ε hε
  apply right_limit.eq' at hre
  apply left_limit.eq' at hle
  rw [hright, ←Convergesto.iff] at hre
  rw [lheft, ←Convergesto.iff] at hle
  simp [Convergesto, Real.CloseNear, Real.CloseFn] at hre hle
  choose δ_plus hδ_plus hre using hre ε hε
  choose δ_minus hδ_minus hle using hle ε hε
  use min δ_plus δ_minus, (by positivity)
  intro x hx hxx₀
  obtain hlt | rfl | hgt := lt_trichotomy x x₀
  . sorry
  . sorry
  sorry

abbrev HasJumpDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ ≠ left_limit X f x₀

example : HasJumpDiscontinuity .univ Real.sign 0 := by sorry

abbrev HasRemovableDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ = left_limit X f x₀
  ∧ right_limit X f x₀ ≠ f x₀

example : HasRemovableDiscontinuity .univ f_9_3_17 0 := by sorry

example : ¬ HasRemovableDiscontinuity .univ (fun x ↦ 1/x) 0 := by sorry

example : ¬ HasJumpDiscontinuity .univ (fun x ↦ 1/x) 0 := by sorry

/- Вправа 9.5.1: Запишіть визначення того, що означає, коли границя функції дорівнює `+∞` або `-∞`; застосуйте до `fun x ↦ 1/x`; сформулюйте й доведіть варіант Твердження 9.3.9. -/


end Chapter9
