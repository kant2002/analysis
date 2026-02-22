import Mathlib.Tactic

/-!
# Аналіз I, Розділ 10.3: Монотонні функції та похідні

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:
- Взаємозв'язки між монотонністю та диференційністю.

-/

namespace Chapter10

/-- Твердження 10.3.1 / Вправа 10.3.1 -/
theorem derivative_of_monotone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Monotone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≥ 0 := by
  sorry

theorem derivative_of_antitone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Antitone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≤ 0 := by
  sorry

/-- Твердження 10.3.3 / Вправа 10.3.4 -/
theorem strictMono_of_positive_derivative {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hpos: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) :
    StrictMonoOn f (.Icc a b) := by
  sorry

theorem strictAnti_of_negative_derivative {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hneg: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) :
    StrictAntiOn f (.Icc a b) := by
  sorry

/-- Приклад 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by sorry

/-- Вправа 10.3.3 -/
example : ∃ f: ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by sorry

/-- Вправа 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X  := by
  sorry

end Chapter10
