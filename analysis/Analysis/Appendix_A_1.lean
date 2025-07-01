import Mathlib.Tactic

/-!
# Аналіз I, Додаток A.1

Вступ до математичних тверджень. Демонструє деякі базові тактики та синтаксис Lean.

-/


-- Приклад A.1.1. Те, що в підручнику називається «твердженнями», є об'єктами типу `Prop` в Lean. Крім того, в Lean ми схильні присвоювати "мусорні" значення виразам, які зазвичай вважаються невизначеними, тому обговорення невизначених термінів у підручнику слід відповідно скоригувати.

#check 2+2=4
#check 2+2=5

/-- Кожне добре сформульоване твердження або істинне, або хибне... -/
example (P:Prop) : (P=true) ∨ (P=false) := by simp; tauto

/-- .. але не одночасно. -/
example (P:Prop) : ¬ ((P=true) ∧ (P=false)) := by simp

-- Примітка: `P=true` та `P=false` спрощуються до `P` та `¬P` відповідно.

/-- Щоб довести істинність твердження, достатньо показати, що воно не є хибним, -/
example {P:Prop} (h: P ≠ false) : P = true := by simp; tauto

/-- тоді як для того, щоб довести, що твердження хибне, достатньо довести, що воно не є істинним. -/
example {P:Prop} (h: P ≠ true) : P = false := by simp; tauto

/-- Це твердження істінне, але навряд чи буде дуже корисним. -/
example : 2 = 2 := rfl

/-- Це твердження також істінне, але не дуже ефективне. -/
example : 4 ≤ 4 := by norm_num

/- Це вираз, а не твердження. -/
#check 2 + 3*5

/- Це твердження, а не вираз. -/
#check 2 + 3*5 = 17

#check Prime (30+5)

#check 30+5 ≤ 42-7

/-- Кон'юнкція -/
example {X Y: Prop} (hX: X) (hY: Y) : X ∧ Y := by
  constructor
  . exact hX
  exact hY

example {X Y: Prop} (hXY: X ∧ Y) : X := by
  exact hXY.1

example {X Y: Prop} (hXY: X ∧ Y) : Y := by
  exact hXY.2

example {X Y: Prop} (hX: ¬ X) : ¬ (X ∧ Y) := by
  contrapose! hX
  exact hX.1

example {X Y: Prop} (hY: ¬ Y) : ¬ (X ∧ Y) := by
  contrapose! hY
  exact hY.2

example : (2+2=4) ∧ (3+3=6) := by
  constructor
  . norm_num
  norm_num

/-- Диз'юнкція -/
example {X Y: Prop} (hX: X) : X ∨ Y := by
  left
  exact hX

example {X Y: Prop} (hY: Y) : X ∨ Y := by
  right
  exact hY

example {X Y: Prop} (hX: ¬ X) (hY: ¬ Y) : ¬ (X ∨ Y) := by
  simp
  constructor
  . exact hX
  exact hY

example : (2+2=4) ∨ (3+3=5) := by
  left
  norm_num

example : ¬ ((2+2=5) ∨ (3+3=5)) := by
  simp

example : (2+2=4) ∨ (3+3=6) := by
  left
  norm_num

example : (2+2=4) ∧ (3+3=6) := by
  constructor
  . norm_num
  norm_num

example : (2+2=4) ∨ (2353 + 5931 = 7284) := by
  left
  norm_num

#check Xor'

/-- Заперечення -/
example {X:Prop} : (¬ X = true) ↔ (X = false) := by simp

example {X:Prop} : (¬ X = false) ↔ (X = true) := by simp

example : ¬ (2+2=5) := by simp

example : 2+2 ≠ 5 := by simp

example (Jane_black_hair Jane_blue_eyes:Prop) :
  (¬ (Jane_black_hair ∧ Jane_blue_eyes)) ↔ (¬ Jane_black_hair ∨  ¬ Jane_blue_eyes) := by
  simp; tauto

example (x:ℤ) : ¬ (Even x ∧ x ≥ 0) ↔ (Odd x ∨ x < 0) := by
  have : ¬ Odd x ↔ Even x := Int.not_odd_iff_even
  have : ¬ (x ≥ 0) ↔ x < 0 := Int.not_le
  tauto

example (x:ℤ) : ¬ (x ≥ 2 ∧ x ≤ 6) ↔ (x < 2 ∨ x > 6) := by
  have : ¬ (x ≥ 2) ↔ (x < 2) := Int.not_le
  have : ¬ (x ≤ 6) ↔ (x > 6) := Int.not_le
  tauto

example (John_brown_hair John_black_hair:Prop) :
  (¬ (John_brown_hair ∨ John_black_hair)) ↔ (¬ John_brown_hair ∧  ¬ John_black_hair) := by
  simp

example (x:ℝ) : ¬ (x ≥ 1 ∧ x ≤ -1) ↔ (x < 1 ∨ x > -1) := by
  have : ¬ (x ≥ 1) ↔ (x < 1) := not_le
  have : ¬ (x ≤ -1) ↔ (x > -1) := not_le
  tauto

example (x:ℤ) : ¬ (Even x ∨ Odd x) ↔ (¬ Even x ∧ ¬ Odd x) := by
  tauto

example (X:Prop) : ¬ (¬ X) ↔ X := by
  simp

/-- Тоді і тільки тоді (iff) -/
example {X Y: Prop} (hXY: X ↔ Y) (hX: X) : Y := by
  rw [hXY] at hX
  exact hX

example {X Y: Prop} (hXY: X ↔ Y) (hY: Y) : X := by
  rw [←hXY] at hY
  exact hY

example {X Y: Prop} (hXY: X ↔ Y) (hX: X) : Y := by
  exact hXY.mp hX

example {X Y: Prop} (hXY: X ↔ Y) (hY: Y) : X := by
  exact hXY.mpr hY

example {X Y: Prop} (hXY: X ↔ Y) : X=Y := by
  simp [hXY]

example (x:ℝ) : x = 3 ↔ 2 * x = 6 := by
  constructor
  . intro h
    linarith
  intro h
  linarith

example : ¬ (∀ x:ℝ, x = 3 ↔ x^2 = 9) := by
  simp
  use -3
  norm_cast

example {X Y: Prop} (hXY: X ↔ Y) (hX: ¬ X) : ¬ Y := by
  by_contra this
  rw [←hXY] at this
  contradiction

example : (2+2=5) ↔ (4+4=10) := by
  simp

example {X Y Z:Prop} (hXY: X ↔ Y) (hXZ: X ↔ Z) : [X,Y,Z].TFAE := by
  tfae_have 1 ↔ 2 := by exact hXY  -- Цей рядок необов'язковий
  tfae_have 1 ↔ 3 := by exact hXZ  -- Цей рядок необов'язковий
  tfae_finish

/-- Зверніть увагу, що для методу `.out` індексація починається з 0, на відміну від тактики `tfae_have`. -/
example {X Y Z:Prop} (h: [X,Y,Z].TFAE) : X ↔ Y := by
  exact h.out 0 1

/-- Вправа A.1.1.  Заповніть перше `sorry` чимось прийнятним -/
example {X Y:Prop} : ¬ ((X ∨ Y) ∧ ¬ (X ∧ Y)) ↔ sorry := by sorry

/-- Вправа A.1.2.  Заповніть перше `sorry` чимось прийнятним -/
example {X Y:Prop} : ¬ (X ↔ Y) ↔ sorry := by sorry

/-- Вправа A.1.3. -/
def Exercise_A_1_3 : Decidable (∀ (X Y: Prop), (X → Y) → (¬X → ¬ Y) → (X ↔ Y)) := by
  -- перший рядок цієї конструкції має бути або `apply isTrue`, або `apply isFalse`, залежно від того, чи вважаєте ви дане твердження істинним чи хибним.
  sorry

/-- Вправа A.1.4. -/
def Exercise_A_1_4 : Decidable (∀ (X Y: Prop), (X → Y) → (¬Y → ¬ X) → (X ↔ Y)) := by
  -- перший рядок цієї конструкції має бути або `apply isTrue`, або `apply isFalse`.
  sorry

/-- Вправа A.1.5. -/
def Exercise_A_1_5 : Decidable (∀ (X Y Z: Prop), (X ↔ Y) → (Y ↔ Z) → [X,Y,Z].TFAE) := by
  -- перший рядок цієї конструкції має бути або `apply isTrue`, або `apply isFalse`.
  sorry

/-- Вправа A.1.6. -/
def Exercise_A_1_6 : Decidable (∀ (X Y Z: Prop), (X → Y) → (Y → Z) → (Z → X) → [X,Y,Z].TFAE) := by
  -- перший рядок цієї конструкції має бути або `apply isTrue`, або `apply isFalse`.
  sorry
