import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Analysis I, Appendix A.6: Деякі приклади доказів та квантифікаторів

Деякі приклади доказів та квантифікаторів у Lean

-/

/-- Твердження A.6.1 -/
example : ∀ ε > (0:ℝ), ∃ δ > 0, 2 * δ < ε := by
  intro ε hε
  use ε / 3
  constructor
  . positivity
  . linarith

example : ¬ ∃ δ > 0, ∀ ε > (0:ℝ), 2 * δ < ε := by
  sorry

open Real in
/-- Твердження A.6.2.  Наведений нижче доказ є дещо не ідіоматичним для Lean, але ілюструє, як реалізувати доказ типу "нехай ε буде величиною, яку буде обрано пізніше". -/
example : ∃ ε > 0, ∀ x, 0 < x ∧ x < ε → sin x > x / 2 := by
  use ?eps  -- ми оберемо це пізніше
  constructor
  swap -- відкласти перевірку позитивності на потім
  intro x hx
  have hpos := hx.1
  have hderiv : deriv sin = cos := by
    ext x
    apply HasDerivAt.deriv
    apply hasDerivAt_sin
  have := exists_deriv_eq_slope sin hpos (by fun_prop) (by fun_prop)
  simp [hderiv] at this
  obtain ⟨ y, ⟨ hy1, hy2 ⟩, hy3 ⟩ := this
  suffices hcosy : cos y > 1/2
  . rw [hy3, gt_iff_lt, ←(mul_lt_mul_left hpos)] at hcosy
    rw [gt_iff_lt]
    convert hcosy using 1
    . ring
    field_simp
  suffices ybound : y < π/3
  . have := cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hy1) (by linarith) ybound
    simp only [cos_pi_div_three, ←gt_iff_lt] at this
    exact this
  have : y < ?eps := by
    exact hy2.trans hx.2
  pick_goal 3  -- Тепер час підібрати ε
  . exact π/3
  exact this
  positivity

open Real in
/-- Твердження A.6.2: більш ідіоматичний доказ -/
example : ∃ ε > 0, ∀ x, 0 < x ∧ x < ε → sin x > x / 2 := by
  use π/3, by positivity
  intro x ⟨ hpos, hx ⟩
  have hderiv : deriv sin = cos := by
    ext x
    apply HasDerivAt.deriv
    apply hasDerivAt_sin
  have := exists_deriv_eq_slope sin hpos (by fun_prop) (by fun_prop)
  simp [hderiv] at this
  obtain ⟨ y, ⟨ hy1, hy2 ⟩, hy3 ⟩ := this
  have ybound : y < π/3 := by linarith
  have hcosy := cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hy1) (by linarith) ybound
  simp only [cos_pi_div_three, ←gt_iff_lt] at hcosy
  rw [hy3, gt_iff_lt, ←(mul_lt_mul_left hpos)] at hcosy
  rw [gt_iff_lt]
  convert hcosy using 1
  . ring
  field_simp
