import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Аналіз I, Глава 2.3: Множення

Цей файл є перекладом Глави 2.3 Аналізу I до Lean 4.
Вся нумерація посилається на оригінальний текст.

Я *(пр.перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним рішенням Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підбуцнути",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Визначення множення та піднесення до степеня для натуральних чисел з "Розділу 2".
  `Chapter2.Nat`.

Примітка: наприкінці цього розділу клас `Chapter2.Nat` буде замінено на користь стандартного
класу Mathlib `_root_.Nat`, або `ℕ`.  Однак, ми пропрацюємо властивості
`Chapter2.Nat` "вручну" в наступних кількох розділах для педагогічних цілей.

## Підказки від попередніх користувачів

Користувачі супровідного матеріалу, які виконали вправи в цьому розділі, можуть надсилати свої поради майбутнім користувачам цього розділу як PRи.

- (Додайте підказку тут)

-/

namespace Chapter2

/-- Визначення 2.3.1 (Множення натуральних чисел) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the `*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Визначення 2.3.1 (Множення натуральних чисел)
Порівняйте із Mathlib-івської `Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Визначення 2.3.1 (Множення натуральних чисел)
Порівняйте із Mathlib-івської `Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's `Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- Ця лема буде корисною для доведення Леми 2.3.2.
Порівняйте із Mathlib-івської `Nat.mul_zero` -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  sorry

/-- Ця лема буде корисною для доведення Леми 2.3.2.
Порівняйте із Mathlib-івської `Nat.mul_succ` -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  sorry

/-- Лема 2.3.2 (Множення комутативне) / Вправа 2.3.1
Порівняйте із Mathlib-івської `Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  sorry

/-- Compare with Mathlib's `Nat.mul_one` -/
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's `Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  sorry

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's `Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  sorry

/-- Твердження 2.3.4 (Дістрібутивність)
Порівняйте із Mathlib-івської `Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Твердження 2.3.4 (Дістрібутивність)
Порівняйте із Mathlib-івської `Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Твердження 2.3.5 (Множення асоціативне) / Вправа 2.3.3
Порівняйте із Mathlib-івської `Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  sorry

/-- (Не із книги)  Nat є комутативним півкільцем.
    This allows tactics such as `ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the `ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Твердження 2.3.6 (Множення зберігає порядок)
Порівняйте із Mathlib-івським `Nat.mul_lt_mul_of_pos_right` -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  rw [lt_iff_add_pos] at h
  choose d hdpos hd using h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Твердження 2.3.6 (Множення зберігає порядок) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Твердження 2.3.6 (Множення зберігає порядок)
Порівняйте із Mathlib-івським `Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Твердження 2.3.6 (Множення зберігає порядок) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Наслідок 2.3.7 (Властивість скорочення)
Compare with Mathlib's `Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  have := trichotomous a b
  obtain hlt | rfl | hgt := this
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  . rfl
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  apply ne_of_gt at hgt
  contradiction

/-- (Не із книги) Nat є впорядкованим півкільцем.
This allows tactics such as `gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by sorry
  mul_le_mul_of_nonneg_left := by sorry
  mul_le_mul_of_nonneg_right := by sorry

/-- This illustration of the `gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le

/-- Твердження 2.3.9 (Лема про ділення Евкліда) / Вправа 2.3.5
Порівняйте із Mathlib-івським `Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  sorry

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел)
Порівняйте із Mathlib-івським `Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел)
Порівняйте із Mathlib-івським `Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Порівняйте із Mathlib-івським `Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Вправа 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  sorry

end Chapter2
