import Mathlib.Tactic

/-!
# Аналіз I, Розділ 4.3: Абсолютні значення та піднесення до степеня

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні побудови та результати цього розділу:

- Базові властивості абсолютного значення та піднесення до степеня для раціональних чисел
  (тут ми використовуємо раціональні числа Mathlib `ℚ`, а не раціональні числа розділу 4.2).

Примітка: щоб уникнути конфлікту позначень, ми використовуємо стандартні визначення Mathlib
для абсолютного значення та піднесення до степеня. Через це кілька вправ можна досить легко розв’язати
за допомогою API Mathlib для цих операцій. Однак дух вправ полягає в тому, щоб розв’язувати їх,
використовуючи API, наданий у цьому розділі, а також більш базовий API Mathlib для раціональних
чисел, який не посилається на абсолютне значення чи піднесення до степеня.

## Підказки від попередніх користувачів

Користувачі супровідного матеріалу, які виконали вправи в цьому розділі, можуть надсилати свої поради майбутнім користувачам цього розділу як PRи.

- (Додайте підказку тут)

-/


/--
  Це визначення потрібно зробити поза простором імен Розділу 4.3 з технічних причин.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Визначення 4.3.1 (Абсолютне значення) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Визначення 4.3.1 (Абсолютне значення) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Визначення 4.3.1 (Абсолютне значення) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Не в підручнику) Це визначення абсолютного значення збігається з визначенням у Mathlib.
  Надалі ми використовуємо абсолютне значення Mathlib.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  sorry

abbrev dist (x y : ℚ) := |x - y|

/--
  Визначення 4.2 (Відстань).
  Тут ми уникаємо поняття відстані з Mathlib, оскільки воно має дійсні значення.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Твердження 4.3.3(a) / Вправа 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by sorry

/-- Твердження 4.3.3(a) / Вправа 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by sorry

/-- Твердження 4.3.3(b) / Вправа 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by sorry

/-- Твердження 4.3.3(c) / Вправа 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by sorry

/-- Твердження 4.3.3(c) / Вправа 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by sorry

/-- Твердження 4.3.3(d) / Вправа 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by sorry

/-- Твердження 4.3.3(d) / Вправа 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by sorry

/-- Твердження 4.3.3(e) / Вправа 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by sorry

/-- Твердження 4.3.3(e) / Вправа 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  sorry

/-- Твердження 4.3.3(f) / Вправа 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by sorry

/-- Твердження 4.3.3(f) / Вправа 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by sorry

/--
  Визначення 4.3.4 (ε-близькість).  У тексті це поняття не визначене для ε, що дорівнює нулю або є від’ємним,
  але в Lean зручніше призначити в цьому випадку «сміттєве» визначення. Це також
  дозволяє деяке послаблення гіпотез у наступних лемах.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Приклади 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by sorry

/-- Приклади 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by sorry

/-- Приклади 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by sorry

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by sorry

/-- Твердження 4.3.7(a) / Вправа 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by sorry

/-- Твердження 4.3.7(b) / Вправа 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by sorry

/-- Твердження 4.3.7(c) / Вправа 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by sorry

/-- Твердження 4.3.7(d) / Вправа 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by sorry

/-- Твердження 4.3.7(d) / Вправа 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by sorry

/-- Твердження 4.3.7(e) / Вправа 4.3.2, трохи посилена -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by sorry

/-- Твердження 4.3.7(f) / Вправа 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by sorry

/-- Твердження 4.3.7(g) / Вправа 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by sorry

/-- Твердження 4.3.7(h) / Вправа 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- Доведення написане так, щоб відповідати структурі оригінального тексту, хоча
  -- невід’ємність ε та δ є очевидною і не потребує явного зазначення в гіпотезах.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- Ця варіація Твердження 4.3.7(h) не містилася в підручнику, але може бути корисною
у деяких наступних вправах. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
    sorry

/-- Визначення 4.3.9 (піднесення до степеня).  Тут ми використовуємо визначення з Mathlib.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Визначення 4.3.9 (піднесення до степеня).  Тут ми використовуємо визначення з Mathlib.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Твердження 4.3.10(a) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by sorry

/-- Твердження 4.3.10(a) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by sorry

/-- Твердження 4.3.10(a) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by sorry

/-- Твердження 4.3.10(b) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by sorry

/-- Твердження 4.3.10(c) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by sorry

/-- Твердження 4.3.10(c) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by sorry

/-- Твердження 4.3.10(c) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by sorry

/-- Твердження 4.3.10(c) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by sorry

/-- Твердження 4.3.10(d) (Властивості піднесення до степеня, I) / Вправа 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by sorry

/--
  Визначення 4.3.11 (Піднесення до степеня з від’ємним показником).
  Тут ми використовуємо поняття піднесення до степеня з цілим показником із Mathlib.
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Твердження 4.3.12(a) (Властивості піднесення до степеня, II) / Вправа 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by sorry

/-- Твердження 4.3.12(a) (Властивості піднесення до степеня, II) / Вправа 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by sorry

/-- Твердження 4.3.12(a) (Властивості піднесення до степеня, II) / Вправа 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by sorry

/-- Твердження 4.3.12(b) (Властивості піднесення до степеня, II) / Вправа 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by sorry

/-- Твердження 4.3.12(b) (Властивості піднесення до степеня, II) / Вправа 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by sorry

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  sorry

/-- Твердження 4.3.12(c) (Властивості піднесення до степеня, II) / Вправа 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  sorry

/-- Твердження 4.3.12(d) (Властивості піднесення до степеня, II) / Вправа 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by sorry

/-- Вправа 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by sorry
