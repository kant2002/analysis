import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Аналіз I, Глава 2.3

Цей файл є перекладом Глави 2.3 Аналізу I до Lean 4.
Вся нумерація посилається на оригінального тексту.

Я *(пр.перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним рішенням Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підбуцнути",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Визначення множення та піднесення до степеня для натуральних чисел з "Розділу 2".
  `Chapter2.Nat`

Примітка: наприкінці цього розділу клас `Chapter2.Nat` буде замінено на користь стандартного
класу Mathlib `_root_.Nat`, або `ℕ`.  Однак, ми пропрацюємо властивості
`Chapter2.Nat` "вручну" в наступних кількох розділах для педагогічних цілей.
-/

namespace Chapter2

/-- Визначення 2.3.1 (Множення натуральних чисел) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

instance Nat.instMul : Mul Nat where
  mul := mul

/-- Визначення 2.3.1 (Множення натуральних чисел) -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Визначення 2.3.1 (Множення натуральних чисел) -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- Ця лема буде корисною для доведення Леми 2.3.2. -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  sorry

/-- Ця лема буде корисною для доведення Леми 2.3.2. -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  sorry

/-- Лема 2.3.2 (Множення комутативне) / Вправа 2.3.1 -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  sorry

theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- Лема 2.3.3 (Додатні натуральні числа не мають дільників на нуль) / Вправа 2.3.2 -/
lemma Nat.mul_eq_zero_iff (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  sorry

lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.isPos) (h₂: m.isPos) : (n * m).isPos := by
  sorry

/-- Твердження 2.3.4 (Дістрібутивність)-/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Твердження 2.3.4 (Дістрібутивність)-/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Твердження 2.3.5 (Множення асоціативне) / Вправа 2.3.3 -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  sorry

/-- (Не із книги)  Nat є комутативним півкільцем. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- Твердження 2.3.6 (Множення зберігає порядок) -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.isPos) : a * c < b * c := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  rw [lt_iff_add_pos] at h
  obtain ⟨ d, hdpos, hd ⟩ := h
  apply_fun (· * c) at hd
  rw [add_mul] at hd
  have hdcpos : (d * c).isPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Твердження 2.3.6 (Множення зберігає порядок) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.isPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Твердження 2.3.6 (Множення зберігає порядок) -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.isPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Твердження 2.3.6 (Множення зберігає порядок) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.isPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc



/-- Наслідок 2.3.7 (Властивість скорочення) -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.isPos) : a = b := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  have := trichotomous a b
  rcases this with hlt | heq | hgt
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    replace hlt := ne_of_lt _ _ hlt
    contradiction
  . assumption
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  replace hgt := ne_of_gt _ _ hgt
  contradiction

/-- (Не із книги) Nat є впорядкованим півкільцем. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := by sorry
  mul_le_mul_of_nonneg_left := by sorry
  mul_le_mul_of_nonneg_right := by sorry


/-- Твердження 2.3.9 (Лема про ділення Евкліда) / Вправа 2.3.5 -/
theorem Nat.exists_div_mod (n :Nat) {q: Nat} (hq: q.isPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  sorry

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел) -/
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел) -/
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Визначення 2.3.11 (Піднесення до степеня для натуральних чисел) -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Вправа 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  sorry

end Chapter2
