import Mathlib.Tactic

/-!
# Аналіз I, Розділ 9.10: Limits at infinity

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:
- Базовий набір API для версій Mathlib щодо збіжності до нескінченності та границь на нескінченності.
-/

namespace Chapter9

/-- Визначення 9.10.1 (Нескінченна точка дотику). Ми використовуємо `¬ BddAbove X` як позначення того, що `+∞` є точкою дотику множини X. -/
theorem BddAbove.unbounded_iff (X:Set ℝ) : ¬ BddAbove X ↔ ∀ M, ∃ x ∈ X, x > M := by
  simp [bddAbove_def]

theorem BddAbove.unbounded_iff' (X:Set ℝ) : ¬ BddAbove X ↔ sSup ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊤ := by
  simp [sSup_eq_top, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, hx; revert M; simp [EReal.forall]
  intro h M; specialize h (M:EReal) ?_ <;> simp_all

theorem BddBelow.unbounded_iff (X:Set ℝ) : ¬ BddBelow X ↔ ∀ M, ∃ x ∈ X, x < M := by
  simp [bddBelow_def]

theorem BddBelow.unbounded_iff' (X:Set ℝ) : ¬ BddBelow X ↔ sInf ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊥ := by
  simp [sInf_eq_bot, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, hx; revert M; simp [EReal.forall]
  intro h M; specialize h (M:EReal) ?_ <;>simp_all

/-- Визначення 9.10.13 (Границя на нескінченності) -/
theorem Filter.Tendsto.AtTop.iff {X: Set ℝ} (f:ℝ → ℝ) (L:ℝ) : Filter.Tendsto f (.atTop ⊓ .principal X) (nhds L) ↔ ∀ ε > (0:ℝ), ∃ M, ∀ x ∈ X ∩ .Ici M, |f x - L| < ε := by
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  simp [Filter.eventually_inf_principal]
  aesop

/-- Вправа 9.10.4 -/
example : Filter.Tendsto (fun x:ℝ ↦ 1/x) (.atTop ⊓ .principal (.Ioi 0)) (nhds 0) := by
  sorry

open Classical in
/-- Вправа 9.10.1 -/
example (a:ℕ → ℝ) (L:ℝ) : Filter.Tendsto (fun x:ℝ ↦ (if h:(∃ n:ℕ, x = n) then a h.choose else 0)) (.atTop ⊓ .principal ((fun n:ℕ ↦ (n:ℝ)) '' .univ)) (nhds L) ↔ Filter.atTop.Tendsto a (nhds L) := by
  sorry

end Chapter9
