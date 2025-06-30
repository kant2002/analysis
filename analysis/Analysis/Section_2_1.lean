import Mathlib.Tactic

/-!
# Аналіз I, Глава 2.1

Цей файл є перекладом Глави 2.1 Аналізу I до Lean 4. Вся нумерація посилається на оригінальний текст.

Я *(пр.перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним рішенням Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підбуцнути",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Визанчення натуральних чисел "Розділу 2", `Chapter2.Nat`, абревіюється як `Nat` в середині
  простору імен `Chapter2`. (У книзі натуральні числа трактуються суто аксіоматично, як тип,
  що підпорядковується аксіомам Пеано; але тут ми використовуємо переваги рідних для Lean
  індуктивних типів, щоб явно побудувати версію натуральних чисел, які підпорядковуються цим
  аксіомам. Можна також діяти більш аксіоматично, як це зроблено в розділі 3 для теорії множин,
  але ми залишаємо це як вправу для читача..)
- Встановлення аксіом Пеано для `Chapter2.Nat`
- Рекурсивні визначення для `Chapter2.Nat`

Примітка: наприкінці цього розділу клас `Chapter2.Nat` буде замінено на користь стандартного
класу Mathlib `_root_.Nat`, або `ℕ`.  Однак, ми пропрацюємо властивості
`Chapter2.Nat` "вручну" в наступних кількох розділах для педагогічних цілей.

-/

namespace Chapter2

/--
  Припущення 2.6 (Існування натуральних чисел).  Тут ми будемо використовувати явне побудування
  натуральних чисел (використовуючи індуктивний тип).  Для більш аксіоматичного підходу, дивіться епілог
  до цього розділу
-/
inductive Nat where
| zero : Nat
| succ : Nat → Nat
deriving Repr, DecidableEq  -- це дозволяє `decide` працювати із `Nat`

/-- Аксіома 2.1 (0 це натуральне число) -/
instance Nat.instZero : Zero Nat := ⟨ zero ⟩
#check (0:Nat)

/-- Аксіома 2.2 (Наступник натурального числа також є натуральним числом) -/
postfix:100 "++" => Nat.succ
#check (fun n ↦ n++)


/--
  Визначення 2.1.3 (Визначення чисел 0, 1, 2, etc.). Примітка: щоб уникнути неоднозначності, вам
  може знадобитися явна конвертація як наприклад (0:Nat), (1:Nat), і т.д. щоб посилатися на версію натуральних чисел із
  цього розділу.
-/
instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

instance Nat.instOne : One Nat := ⟨ 1 ⟩
lemma Nat.zero_succ : 0++ = 1 := by rfl
#check (1:Nat)

lemma Nat.one_succ : 1++ = 2 := by rfl
#check (2:Nat)

/-- Твердження 2.1.4 (3 є натуральним числом)-/
lemma Nat.two_succ : 2++ = 3 := by rfl
#check (3:Nat)

/--
  Аксіома 2.3 (0 не є наступником ніякого натурального числа).
  Порівняйте із Mathlib-овським `Nat.succ_ne_zero`.
-/
theorem Nat.succ_ne (n:Nat) : n++ ≠ 0 := by
  by_contra h
  simp only [reduceCtorEq] at h

/-- Твердження 2.1.6 (4 не дорівнює нулю) -/
theorem Nat.four_ne : (4:Nat) ≠ 0 := by
  -- За визначенням, 4 = 3++.
  change 3++ ≠ 0
  -- За аксіомою 2.3, 3++ не є нулем.
  exact succ_ne _

/--
  Аксіома 2.4 (Різні натуральні числа мають різних наступників).
  Порівняйте із Mathlib-овським `Nat.succ_inj`.
-/
theorem Nat.succ_cancel {n m:Nat} (hnm: n++ = m++) : n = m := by
  rwa [succ.injEq] at hnm

/--
  Аксіома 2.4 (Різні натуральні числа мають різних наступників).
  Порівняйте із Mathlib-овським `Nat.succ_ne_succ`.
-/
theorem Nat.succ_ne_succ (n m:Nat) : n ≠ m → n++ ≠ m++ := by
  intro h
  contrapose! h
  exact succ_cancel h

/-- Твердження 2.1.8 (6 не дорівнює 2) -/
theorem Nat.six_ne_two : (6:Nat) ≠ 2 := by
-- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  by_contra h
  change 5++ = 1++ at h
  replace h := succ_cancel h
  change 4++ = 0++ at h
  replace h := succ_cancel h
  have := four_ne
  contradiction

/-- Ви також можете довести такого типу результат використовуючи тактику `decide` -/
theorem Nat.six_ne_two' : (6:Nat) ≠ 2 := by
  decide

/--
  Аксіома 2.5 (принцип математичної індукції). Тактика `induction` (або `induction'`) в
  Mathlib служить заміною для цієї аксіоми.
-/
theorem Nat.induction (P : Nat → Prop) (hbase : P 0) (hind : ∀ n, P n → P (n++)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih => exact hind _ ih

/--
  Рекурсія. Аналогічно до вбудованого методу Mathlib `Nat.rec` ассоційованого із
  натуральними числами Mathlib
-/
abbrev Nat.recurse (f: Nat → Nat → Nat) (c: Nat) : Nat → Nat := fun n ↦ match n with
| 0 => c
| n++ => f n (recurse f c n)

/-- Твердження 2.1.16 (рекурсивне визначення). Порівняйте із Mathlib-овським `Nat.rec_zero`. -/
theorem Nat.recurse_zero (f: Nat → Nat → Nat) (c: Nat) : Nat.recurse f c 0 = c := by rfl

/-- Твердження 2.1.16 (рекурсивне визначення). Порівняйте із Mathlib-овським `Nat.rec_add_one`. -/
theorem Nat.recurse_succ (f: Nat → Nat → Nat) (c: Nat) (n: Nat) :
    recurse f c (n++) = f n (recurse f c n) := by rfl

/-- Твердження 2.1.16 (рекурсивне визначення). -/
theorem Nat.eq_recurse (f: Nat → Nat → Nat) (c: Nat) (a: Nat → Nat) :
    (a 0 = c ∧ ∀ n, a (n++) = f n (a n)) ↔ a = recurse f c := by
  constructor
  . intro ⟨ h0, hsucc ⟩
    -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
    apply funext; apply induction
    . exact h0
    intro n hn
    rw [hsucc n, recurse_succ, hn]
  intro h
  rw [h]
  constructor
  . exact recurse_zero _ _
  exact recurse_succ _ _


/-- Твердження 2.1.16 (рекурсивне визначення). -/
theorem Nat.recurse_uniq (f: Nat → Nat → Nat) (c: Nat) :
    ∃! (a: Nat → Nat), a 0 = c ∧ ∀ n, a (n++) = f n (a n) := by
  apply ExistsUnique.intro (recurse f c)
  . constructor
    . exact recurse_zero _ _
    . exact recurse_succ _ _
  intro a
  exact (eq_recurse _ _ a).mp

end Chapter2
