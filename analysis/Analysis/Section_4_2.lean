import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Аналіз I, Розділ 4.2: Раціональні числа

Цей файл є перекладом розділу 4.2 книги *Analysis I* на Lean 4.
Уся нумерація відповідає оригінальному тексту.

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні побудови та результати цього розділу:

- Визначення раціональних чисел «Розділу 4.2» `Section_4_2.Rat` як формальних часток `a // b`
  цілих чисел `a b : ℤ`, з точністю до еквівалентності. (Це фактортип
  допоміжного типу `Section_4_2.PreRat`, який складається з формальних часток без накладеної еквівалентності.)

- Операції поля та порядок на цих раціональних числах, а також вкладення ℕ і ℤ.

- Еквівалентність із раціональними числами Mathlib `_root_.Rat` (або `ℚ`), які ми надалі використовуватимемо.

Примітка: тут (і надалі) ми використовуємо натуральні числа `ℕ` та цілі числа `ℤ` із Mathlib, а не натуральні числа розділу 2 та цілі числа розділу 4.1.

## Підказки від попередніх користувачів

Користувачі супровідного матеріалу, які виконали вправи в цьому розділі, можуть надсилати свої поради майбутнім користувачам цього розділу як PRи.

- (Додайте підказку тут)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Вправа 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by sorry
    symm := by sorry
    trans := by sorry
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- Ми надаємо діленню «сміттєве» значення 0//1, якщо знаменник дорівнює нулю -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Визначення 4.2.1 (Раціональні числа) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd, Setoid.r]

/-- Визначення 4.2.1 (Раціональні числа) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Розв’язність рівності. Підказка: змініть доведення `DecidableEq Int` із попереднього
  розділу. Однак, оскільки формальне ділення окремо обробляє випадок нульового знаменника,
  може бути зручніше уникати цієї операції та працювати безпосередньо з API `Quotient`.
-/
instance Rat.decidableEq : DecidableEq Rat := by
  sorry

/-- Лема 4.2.3 (Додавання коректно визначене) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    calc
      _ = (a*b')*d*d' + b*b'*(c*d') := by ring
      _ = (a'*b)*d*d' + b*b'*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Визначення 4.2.2 (Додавання раціональних чисел) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Лема 4.2.3 (Множення коректно визначене) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by sorry)

/-- Визначення 4.2.2 (Множення раціональних чисел) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Лема 4.2.3 (Протилежний елемент коректно визначени) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by sorry)

/-- Визначення 4.2.2 (Протилежний елемент раціональних чисел) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Вкладення цілих чисел у раціональні числа -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast розподіляється на наступника -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by sorry

/-- intCast розподіляється на додавання -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by sorry

/-- intCast розподіляється на множення -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by sorry

/-- intCast комутує з взяттям протилежного елемента -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by sorry

/--
  У той час як у книзі обернене число для 0 залишається невизначеним, у Lean зручніше призначити
  цьому оберненому числу «сміттєве» значення; ми довільно обираємо це сміттєве значення рівним 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    sorry -- підказка: розділіть на випадки `a = 0` та `a ≠ 0`
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Твердження 4.2.4 (закони алгебри) / Вправа 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- тут також можна використати `observe hbd : b*d ≠ 0`
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- тут також можна використати `observe hdf : d*f ≠ 0`
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- тут також можна використати `observe hbdf : b*d*f ≠ 0`
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
)
 (by sorry) (by sorry)

/-- Твердження 4.2.4 (закони алгебри) / Вправа 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by sorry

/-- Твердження 4.2.4 (закони алгебри) / Вправа 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by sorry
  mul_assoc := by sorry
  one_mul := by sorry
  mul_one := by sorry

/-- Твердження 4.2.4 (закони алгебри) / Вправа 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by sorry
  right_distrib := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry
  -- Зазвичай `CommRing` згенерує екземпляр `natCast` та доведення для цього.
  -- Однак ми використовуємо власний `natCast`, для якого `natCast_succ` не можна
  -- автоматично довести за допомогою `rfl`. На щастя, ми вже це довели.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by sorry

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

/-- Твердження 4.2.4 (закони алгебри) / Вправа 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by sorry
  mul_inv_cancel := by sorry
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by sorry

/-- Визначення віднімання -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by sorry
  map_mul' := by sorry

/-- Визначення 4.2.6 (позитивність) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Визначення 4.2.6 (негативність) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

/-- Лема 4.2.7 (трихотомія раціональних чисел) / Вправа 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by sorry

/-- Лема 4.2.7 (трихотомія раціональних чисел) / Вправа 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by sorry

/-- Лема 4.2.7 (трихотомія раціональних чисел) / Вправа 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by sorry

/-- Лема 4.2.7 (трихотомія раціональних чисел) / Вправа 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by sorry

/-- Визначення 4.2.8 (Порядок раціональних чисел) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Визначення 4.2.8 (Порядок раціональних чисел) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by sorry
theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by sorry

/-- Твердження 4.2.9(a) (трихотомія порядку) / Вправа 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by sorry

/-- Твердження 4.2.9(a) (трихотомія порядку) / Вправа 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by sorry

/-- Твердження 4.2.9(a) (трихотомія порядку) / Вправа 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by sorry

/-- Твердження 4.2.9(a) (трихотомія порядку) / Вправа 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by sorry

/-- Твердження 4.2.9(b) (порядок є антисиметричним) / Вправа 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by sorry

/-- Твердження 4.2.9(c) (порядок є транзитивним) / Вправа 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by sorry

/-- Твердження 4.2.9(d) (додавання зберігає порядок) / Вправа 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by sorry

/-- Твердження 4.2.9(e) (множення на додатне число зберігає порядок) / Вправа 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by sorry

/-- (Не в підручнику) Встановіть розв’язність цього порядку. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- на цьому етапі ціль фактично `Decidable(a//b ≤ c//d)`, але існують технічні
    -- проблеми через «сміттєве» значення формального ділення, коли знаменник дорівнює нулю.
    -- Може бути зручніше уникати формального ділення та працювати безпосередньо з `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Не в підручнику) Раціональні числа мають структуру лінійного порядку. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
  le_antisymm := sorry
  le_total := sorry
  toDecidableLE := decidableRel

/-- (Не в підручнику) Раціональні числа мають структуру строго впорядкованого кільця. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by sorry
  add_le_add_right := by sorry
  mul_lt_mul_of_pos_left := by sorry
  mul_lt_mul_of_pos_right := by sorry
  le_of_add_le_add_left := by sorry
  zero_le_one := by sorry

/-- Вправа 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  sorry


/--
  Не в підручнику: створіть еквівалентність між `Rat` та `ℚ`. Це вимагає певного знайомства з API
  для версії раціональних чисел у Mathlib.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    sorry)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := sorry
  right_inv n := sorry

/-- Не в підручнику: еквівалентність зберігає порядок -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by sorry

/-- Не в підручнику: еквівалентність зберігає операції кільця -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by sorry
  map_mul' := by sorry

/--
  (Не в підручнику) Раціональні числа з підручника ізоморфні (як поле) до раціональних чисел Mathlib.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
