import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Аналіз I, Розділ 2, Епілог

У цьому (технічному) епілозі ми показуємо, що натуральні числа `Chapter2.Nat` з "Розділу 2"
ізоморфні стандартним натуральним числам `ℕ` у різних типових сенсах.

З цього моменту `Chapter2.Nat` буде застарілим типом, і замість нього ми використовуватимемо
стандартні натуральні числа `ℕ`. Зокрема, для всіх наступних розділів слід використовувати
повний API Mathlib для `ℕ` замість API `Chapter2.Nat`.

Для заповнення цих вибачень потрібні як Chapter2.Nat API, так і Mathlib API для стандартних
натуральних чисел `ℕ`. Таким чином, вони є чудовими вправами для підготовки до вищезгаданого
переходу.

У другій половині цього розділу ми також наводимо повністю аксіоматичне трактування
натуральних чисел за допомогою аксіом Пеано. Розгляд у попередніх трьох розділах
був лише частково аксіоматичним, оскільки ми використовували специфічну конструкцію
`Chapter2.Nat` натуральних чисел, яка була індуктивного типу, і використовували цей
індуктивний тип для побудови рекурсора. Тут ми наводимо кілька вправ, щоб показати,
як можна виконати ті ж завдання безпосередньо з аксіом Пеано, не знаючи конкретної
реалізації натуральних чисел.
-/

abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn
    . rfl
    simp [succ_toNat, hn]
    symm
    exact succ_eq_add_one _
  right_inv n := by
    induction' n with n hn
    . rfl
    simp [←succ_eq_add_one]
    exact hn

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := by
    intro n m
    simp [equivNat]
    sorry
  map_mul' := by
    intro n m
    simp [equivNat]
    sorry
  map_le_map_iff' := by sorry

lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = n^m := by
  sorry


/-- Аксіоми Пеано для абстрактного типу `Nat` -/
@[ext]
class PeanoAxioms where
  Nat : Type
  zero : Nat -- Аксіома 2.1
  succ : Nat → Nat -- Аксіома 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Аксіома 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Аксіома 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Аксіома 2.5

namespace PeanoAxioms

/-- Натуральні числа розділу 2 дотримуються аксіом Пеано. -/
def Chapter2.Nat : PeanoAxioms where
  Nat := _root_.Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- Натуральні числа Mathlib дотримуються аксіом Пеано. -/
def Mathlib.Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- Ви можете співставити натуральні числа Mathlib у іншу струкруту яка дотримується аксіом Пеано. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast  := by
  sorry

theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  sorry

/-- Поняття еквівалентності між двома структурами, що дотримуються аксіом Пеано -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

abbrev Equiv.symm (equiv : Equiv P Q) : Equiv Q P where
  equiv := equiv.equiv.symm
  equiv_zero := by sorry
  equiv_succ n := by sorry

abbrev Equiv.trans (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by sorry
  equiv_succ n := by sorry

/-- Примітка: Я підозрюю, що ця конструкція не є обчислювальною та вимагає класичної логіки. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib.Nat P where
  equiv := {
    toFun := P.natCast
    invFun := by sorry
    left_inv := by sorry
    right_inv := by sorry
  }
  equiv_zero := by sorry
  equiv_succ n := by sorry

noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := by sorry

theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  sorry

/-- Приклад результату: рекурсія коректно визначена на будь-якій структурі, що підпорядковується аксіомам Пеано.-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  sorry

end PeanoAxioms
