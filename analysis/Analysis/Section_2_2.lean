import Mathlib.Tactic
import Analysis.Section_2_1

/-!
# Аналіз I, Глава 2.2

Цей файл є перекладом Глави 2.2 Аналізу I до Lean 4.
Вся нумерація посилається на оригінального тексту.

Я *(пр.перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним рішенням Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підбуцнути",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Визначення додавання та порядку для натуральних чисел "Розділу 2", `Chapter2.Nat`
- Встановлення основних властивостей додавання та порядку

Примітка: наприкінці цього розділу клас `Chapter2.Nat` буде замінено на користь стандартного
класу Mathlib `_root_.Nat`, або `ℕ`.  Однак, ми пропрацюємо властивості
`Chapter2.Nat` "вручну" в наступних кількох розділах для педагогічних цілей.
-/

namespace Chapter2

/-- Визначення 2.2.1. (Додавання натуральних чисел.
    Порівняйте із Mathlib-овським `Nat.add` -/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum ↦ sum++) m n

/-- Цей екземпляр дозволить нотації `+` використовуватися для додавання натуральних чисел. -/
instance Nat.instAdd : Add Nat where
  add := add

/-- Порівняйте із Mathlib-овським `Nat.zero_add`-/
@[simp]
theorem Nat.zero_add (m: Nat) : 0 + m = m := recurse_zero (fun _ sum ↦ sum++) _

/-- Порівняйте із Mathlib-овським `Nat.succ_add` -/
theorem Nat.succ_add (n m: Nat) : n++ + m = (n+m)++ := by rfl

/-- Порівняйте із Mathlib-овським `Nat.one_add` -/
theorem Nat.one_add (m:Nat) : 1 + m = m++ := by
  rw [show 1 = 0++ from rfl, succ_add, zero_add]

theorem Nat.two_add (m:Nat) : 2 + m = (m++)++ := by
  rw [show 2 = 1++ from rfl, succ_add, one_add]

example : (2:Nat) + 3 = 5 := by
  rw [Nat.two_add, show 3++=4 from rfl, show 4++=5 from rfl]

-- сума двух натуральних чисел це також натуральне число
#check (fun (n m:Nat) ↦ n + m)

/-- Лема 2.2.2 (n + 0 = n). Порівняйте із Mathlib-овським `Nat.add_zero` -/
@[simp]
lemma Nat.add_zero (n:Nat) : n + 0 = n := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert n; apply induction
  . exact zero_add 0
  intro n ih
  calc
    (n++) + 0 = (n + 0)++ := by rfl
    _ = n++ := by rw [ih]

/-- Лема 2.2.3 (n+(m++) = (n+m)++). Порівняйте із Mathlib-овським `Nat.add_succ` -/
lemma Nat.add_succ (n m:Nat) : n + (m++) = (n + m)++ := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert n; apply induction
  . rw [zero_add, zero_add]
  intro n ih
  rw [succ_add, ih]
  rw [succ_add]


/-- n++ = n + 1 (Чому?). Порівняйте із Mathlib-овським `Nat.succ_eq_add_one` -/
theorem Nat.succ_eq_add_one (n:Nat) : n++ = n + 1 := by
  sorry

/-- Твердження 2.2.4 (Додавання комутативне). Порівняйте із Mathlib-овським `Nat.add_comm` -/
theorem Nat.add_comm (n m:Nat) : n + m = m + n := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert n; apply induction
  . rw [zero_add, add_zero]
  intro n ih
  rw [succ_add]
  rw [add_succ, ih]

/-- Твердження 2.2.5 (Додавання асоціативне) / Вправа 2.2.1
    Порівняйте із Mathlib-овським `Nat.add_assoc` -/
theorem Nat.add_assoc (a b c:Nat) : (a + b) + c = a + (b + c) := by
  sorry

/-- Твердження 2.2.6 (Правило відміни)
    Порівняйте із Mathlib-овським `Nat.add_left_cancel` -/
theorem Nat.add_left_cancel (a b c:Nat) (habc: a + b = a + c) : b = c := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert a; apply induction
  . intro hbc
    rwa [zero_add, zero_add] at hbc
  intro a ih
  intro hbc
  rw [succ_add, succ_add] at hbc
  replace hbc := succ_cancel hbc
  exact ih hbc


/-- (Не із книги) Типу Nat можна дати структуру комутативного адітивного моноїда. -/
instance Nat.addCommMonoid : AddCommMonoid Nat where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec

/-- Визначення 2.2.7 (Додатні натуральні числе).-/
def Nat.isPos (n:Nat) : Prop := n ≠ 0

theorem Nat.isPos_iff (n:Nat) : n.isPos ↔ n ≠ 0 := by rfl

/-- Твердження 2.2.8 (Додатне плюс натуральне число буде додатним).
    Порівняйте із Mathlib-овським `Nat.add_pos_left` -/
theorem Nat.add_pos_left {a:Nat} (b:Nat) (ha: a.isPos) : (a + b).isPos := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert b; apply induction
  . rwa [add_zero]
  intro b hab
  rw [add_succ]
  have : (a+b)++ ≠ 0 := succ_ne _
  exact this

/-- Порівняйте із Mathlib-овським `Nat.add_pos_right` -/
theorem Nat.add_pos_right {a:Nat} (b:Nat) (ha: a.isPos) : (b + a).isPos := by
  rw [add_comm]
  exact add_pos_left _ ha

/-- Наслідок 2.2.9 (якщо сума дорівнює нулю, тоді доданки дорівнюють нулю).
    Порівняйте із Mathlib-овським `Nat.add_eq_zero` -/
theorem Nat.add_eq_zero (a b:Nat) (hab: a + b = 0) : a = 0 ∧ b = 0 := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  by_contra h
  simp only [not_and_or, ←ne_eq] at h
  rcases h with ha | hb
  . rw [← isPos_iff] at ha
    have : (a + b).isPos := add_pos_left _ ha
    contradiction
  rw [← isPos_iff] at hb
  have : (a + b).isPos := add_pos_right _ hb
  contradiction

/-
Наступне API для ∃! може бути корисним для наступної проблеми.  Також, тактика `obtain` корисна
для вилучення змінної предіката із кванторів існування; наприклад, `obtain ⟨ x, hx ⟩ := h`
вилучає змінну предіката `x` та доказ `hx : P x` властивості із гіпотези `h : ∃ x, P x`.
-/

#check existsUnique_of_exists_of_unique
#check ExistsUnique.exists
#check ExistsUnique.unique

/-- Лема 2.2.10 (унікальний попередник) / Вправа 2.2.2 -/
lemma Nat.uniq_succ_eq (a:Nat) (ha: a.isPos) : ∃! b, b++ = a := by
  sorry

/-- Визначення 2.2.11 (Порядок натуральних чисел)
    Це визначає операцію `≤` на натуральних числах. -/
instance Nat.instLE : LE Nat where
  le n m := ∃ a:Nat, m = n + a

/-- Визначення 2.2.11 (Порядок натуральних чисел)
    Це визначає операцію `<` на натуральних числах. -/
instance Nat.instLT : LT Nat where
  lt n m := n ≤ m ∧ n ≠ m

lemma Nat.le_iff (n m:Nat) : n ≤ m ↔ ∃ a:Nat, m = n + a := by rfl

lemma Nat.lt_iff (n m:Nat) : n < m ↔ (∃ a:Nat, m = n + a) ∧ n ≠ m := by rfl

/-- Порівняйте із Mathlib-овським `ge_iff_le` -/
lemma Nat.ge_iff_le (n m:Nat) : n ≥ m ↔ m ≤ n := by rfl

/-- Порівняйте із Mathlib-овським `gt_iff_lt` -/
lemma Nat.gt_iff_lt (n m:Nat) : n > m ↔ m < n := by rfl

/-- Порівняйте із Mathlib-овським `Nat.le_of_lt` -/
lemma Nat.le_of_lt {n m:Nat} (hnm: n < m) : n ≤ m := hnm.1

/-- Порівняйте із Mathlib-овським `Nat.le_iff_lt_or_eq` -/
lemma Nat.le_iff_lt_or_eq (n m:Nat) : n ≤ m ↔ n < m ∨ n = m := by
  rw [Nat.le_iff, Nat.lt_iff]
  by_cases h : n = m
  . simp [h]
    use 0
    rw [add_zero]
  simp [h]

example : (8:Nat) > 5 := by
  rw [Nat.gt_iff_lt, Nat.lt_iff]
  constructor
  . have : (8:Nat) = 5 + 3 := by rfl
    rw [this]
    use 3
  decide

/-- Порівняйте із Mathlib-овським `Nat.lt_succ_self`-/
theorem Nat.succ_gt_self (n:Nat) : n++ > n := by
  sorry

/-- Твердження 2.2.12 (Базові властивості порядку для натуральних чисел) / Вправа 2.2.3

(a) (Порядок рефлексівен). Порівняйте із Mathlib-овським `Nat.le_refl`-/
theorem Nat.ge_refl (a:Nat) : a ≥ a := by
  sorry

/-- (b) (Порядок транзітивен).  Тут буде корисною тактика `obtain`.
    Порівняйте із Mathlib-овським `Nat.le_trans` -/
theorem Nat.ge_trans {a b c:Nat} (hab: a ≥ b) (hbc: b ≥ c) : a ≥ c := by
  sorry

/-- (c) (Порядок антисіметричен). Порівняйте із Mathlib-овським `Nat.le_antisymm`  -/
theorem Nat.ge_antisymm {a b:Nat} (hab: a ≥ b) (hba: b ≥ a) : a = b := by
  sorry

/-- (d) (Додавання зберігає порядок).  Порівняйте із Mathlib-овським `Nat.add_le_add_right`  -/
theorem Nat.add_ge_add_right (a b c:Nat) : a ≥ b ↔ a + c ≥ b + c := by
  sorry

/-- (d) (Додавання зберігає порядок).  Порівняйте із Mathlib-овським `Nat.add_le_add_left`  -/
theorem Nat.add_ge_add_left (a b c:Nat) : a ≥ b ↔ c + a ≥ c + b := by
  simp only [add_comm]
  exact add_ge_add_right _ _ _

/-- (d) (Додавання зберігає порядок).  Порівняйте із Mathlib-овським `Nat.add_le_add_right`  -/
theorem Nat.add_le_add_right (a b c:Nat) : a ≤ b ↔ a + c ≤ b + c := add_ge_add_right _ _ _

/-- (d) (Додавання зберігає порядок).  Порівняйте із Mathlib-овським `Nat.add_le_add_left`  -/
theorem Nat.add_le_add_left (a b c:Nat) : a ≤ b ↔ c + a ≤ c + b := add_ge_add_left _ _ _

/-- (e) a < b iff a++ ≤ b.  Порівняйте із Mathlib-овським `Nat.succ_le_iff` -/
theorem Nat.lt_iff_succ_le (a b:Nat) : a < b ↔ a++ ≤ b := by
  sorry

/-- (f) a < b if and only if b = a + d for positive d. -/
theorem Nat.lt_iff_add_pos (a b:Nat) : a < b ↔ ∃ d:Nat, d.isPos ∧ b = a + d := by
  sorry

/-- Якщо a < b тоді a ̸= b,-/
theorem Nat.ne_of_lt (a b:Nat) : a < b → a ≠ b := by
  intro h; exact h.2

/-- Якщо a > b тоді a ̸= b. -/
theorem Nat.ne_of_gt (a b:Nat) : a > b → a ≠ b := by
  intro h; exact h.2.symm

/-- Якщо a > b та a < b тоді протиріччя -/
theorem Nat.not_lt_of_gt (a b:Nat) : a < b ∧ a > b → False := by
  intro h
  have := (ge_antisymm (Nat.le_of_lt h.1) (Nat.le_of_lt h.2)).symm
  have := ne_of_lt _ _ h.1
  contradiction


/-- Твердження 2.2.13 (Тріхотомія порядку для натуральних чисел) / Вправа 2.2.4
    Порівняйте із Mathlib-овським `trichotomous` -/
theorem Nat.trichotomous (a b:Nat) : a < b ∨ a = b ∨ a > b := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert a; apply induction
  . have why : 0 ≤ b := by
      sorry
    replace why := (Nat.le_iff_lt_or_eq _ _).mp why
    tauto
  intro a ih
  rcases ih with case1 | case2 | case3
  . rw [lt_iff_succ_le] at case1
    rw [Nat.le_iff_lt_or_eq] at case1
    tauto
  . have why : a++ > b := by sorry
    tauto
  have why : a++ > b := by sorry
  tauto

/--
  (Не із книги) Встановіть алгоритмічну розв'язність для цього порядку обчислювальним шляхом.
  Частина доказу, що стосується розв'язності, наведена; решта `sorry` стосуються тверджень
  про натуральні числа. Цей результат також можна було б встановити за допомогою тактики `classical`
  з подальшим використанням `exact Classical.decRel _`, але це зробило б це визначення
  (а також деякі приклади нижче) необчислювальним.

  Порівняйте із Mathlib-овським `Nat.decLe`
-/
def Nat.decLe : (a b : Nat) → Decidable (a ≤ b)
  | 0, b => by
    apply isTrue
    sorry
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue h =>
        apply isFalse
        sorry
      | isFalse h =>
        apply isTrue
        sorry
    | isFalse h =>
      apply isFalse
      sorry

instance Nat.decidableRel : DecidableRel (· ≤ · : Nat → Nat → Prop) := Nat.decLe


/-- (Не із книги) Nat має структуру лінійне впорядкування. -/
instance Nat.linearOrder : LinearOrder Nat where
  le_refl := ge_refl
  le_trans a b c hab hbc := ge_trans hbc hab
  lt_iff_le_not_le := sorry
  le_antisymm a b hab hba := ge_antisymm hba hab
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Не із книги) Nat має структуру впорядкованого моноїда. -/
instance Nat.isOrderedAddMonoid : IsOrderedAddMonoid Nat where
  add_le_add_left := by
    intro a b hab c
    exact (add_le_add_left a b c).mp hab

/-- Твердження 2.2.14 (Сильний принцип індукції) / Вправа 2.2.5
    Порівняйте із Mathlib-овським `Nat.strong_induction_on`
-/
theorem Nat.strong_induction {m₀:Nat} {P: Nat → Prop}
  (hind: ∀ m, m ≥ m₀ → (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m) :
    ∀ m, m ≥ m₀ → P m := by
  sorry

/-- Вправа 2.2.6 (індукція у зворотньому напрямку)
    Порівняйте із Mathlib-овським `Nat.decreasingInduction` -/
theorem Nat.backwards_induction {n:Nat} {P: Nat → Prop}
  (hind: ∀ m, P (m++) → P m) (hn: P n) :
    ∀ m, m ≤ n → P m := by
  sorry

/-- Вправа 2.2.7 (індукція із початкової точки)
    Порівняйте із Mathlib-овським `Nat.le_induction` -/
theorem Nat.induction_from {n:Nat} {P: Nat → Prop} (hind: ∀ m, P m → P (m++)) :
    P n → ∀ m, m ≥ n → P m := by
  sorry



end Chapter2
