import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Tools.ExistsUnique

/-!
# Аналіз I, Розділ 3.3: Функції

Я *(пр.перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним рішенням Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підбуцнути",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Поняття функції `Function X Y` між двома множинами `X`, `Y` в теорії множин із глави 3.1
- Різні співвідношення з поняттям функції `X → Y` у Mathlib між двома типами `X`, `Y`.
  (Примітка із глави 3.1, що кожна `Set` `X` також може бути розглянути
  як підтип `{x : Object // x ∈ X }` `Object`.)
- Основні властивості та операції над функціями, такі як композиція, ін'єктивні функції, сур'єктивні функції,
  та обернені функції.

У решті книги ми відмовимося від версії функції із Розділу 3 та працюватимемо з поняттям
функції із Mathlib. Навіть у цьому розділі ми перейдемо до формалізму Mathlib для деяких прикладів,
що стосуються систем числення, таких як `ℤ` або `ℝ`, які не були реалізовані у фреймворку Розділу 3.

Тут ми працюватимемо з версією `Nat` натуральних чисел, що є внутрішньою для теорії множин з
Розділу 3, хоча зазвичай ми використовуватимемо перетворення, щоб одразу ж перетворити їх на
натуральні числа `ℕ` з Mathlib.

## Підказки від попередніх користувачів

Користувачі супровідного матеріалу, які виконали вправи в цьому розділі, можуть надсилати свої поради майбутнім користувачам цього розділу як PRи.

- (Додайте підказку тут)

-/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/--
  Визначення 3.3.1. `Function X Y` — це структура функцій із `X` до `Y`.
  Аналогічно типу Mathlib `X → Y`.
-/
@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y

#check Function.mk

/--
  Перетворення функції `f: Function X Y` із Розділу 3 на функцію Mathlib `f: X → Y`.
  Визначення функції із Розділу 3 було неконструктивним, тому тут нам доведеться
  використати аксіому вибору.
-/
noncomputable def Function.to_fn {X Y: Set} (f: Function X Y) : X → Y :=
  fun x ↦ (f.unique x).choose

noncomputable instance Function.inst_coefn (X Y: Set) : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := Function.to_fn

theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl

/-- Перетворення функції Mathlib на `Function` з Розділу 3 -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by simp)

/-- Визначення 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  convert ((f.unique x).choose_iff y).symm

@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]


/-- Приклад 3.3.3.   -/
abbrev P_3_3_3a : Nat → Nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1

theorem SetTheory.Set.P_3_3_3a_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_3a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):Nat)
  . simp [P_3_3_3a]
  intro y h
  simpa [P_3_3_3a, Equiv.symm_apply_eq] using h

abbrev SetTheory.Set.f_3_3_3a : Function Nat Nat := Function.mk P_3_3_3a P_3_3_3a_existsUnique

theorem SetTheory.Set.f_3_3_3a_eval (x y: Nat) : y = f_3_3_3a x ↔ (y:ℕ) = (x+1:ℕ) :=
  Function.eval _ _ _


theorem SetTheory.Set.f_3_3_3a_eval' (n: ℕ) : f_3_3_3a (n:Nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_3a_eval, nat_equiv_coe_of_coe]

theorem SetTheory.Set.f_3_3_3a_eval'' : f_3_3_3a 4 = 5 :=  f_3_3_3a_eval' 4

theorem SetTheory.Set.f_3_3_3a_eval''' (n:ℕ) : f_3_3_3a (2*n+3: ℕ) = (2*n+4:ℕ) := by
  convert f_3_3_3a_eval' _

abbrev SetTheory.Set.P_3_3_3b : Nat → Nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)

theorem SetTheory.Set.not_P_3_3_3b_existsUnique : ¬ ∀ x, ∃! y: Nat, P_3_3_3b x y := by
  by_contra h
  choose n hn _ using h (0:Nat)
  have : ((0:Nat):ℕ) = 0 := by simp [OfNat.ofNat]
  simp [P_3_3_3b, this] at hn

abbrev SetTheory.Set.P_3_3_3c : (Nat \ {(0:Object)}: Set) → Nat → Prop :=
  fun x y ↦ ((y+1:ℕ):Object) = x

theorem SetTheory.Set.P_3_3_3c_existsUnique (x: (Nat \ {(0:Object)}: Set)) :
    ∃! y: Nat, P_3_3_3c x y := by
  -- Тут йде деяке технічне розпакування пов'язане з тонкими відмінностями між типом `Object`,
  -- множинами, перетвореними на підтипи `Object`, та підмножинами цих множин.
  obtain ⟨ x, hx ⟩ := x; simp at hx; obtain ⟨ hx1, hx2 ⟩ := hx
  set n := ((⟨ x, hx1 ⟩:Nat):ℕ)
  have : x = (n:Nat) := by simp [n]
  simp [P_3_3_3c, this, Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):Nat)
  . simp [←hx2]
  intro y hy; simp [←hy]

abbrev SetTheory.Set.f_3_3_3c : Function (Nat \ {(0:Object)}: Set) Nat :=
  Function.mk P_3_3_3c P_3_3_3c_existsUnique

theorem SetTheory.Set.f_3_3_3c_eval (x: (Nat \ {(0:Object)}: Set)) (y: Nat) :
    y = f_3_3_3c x ↔ ((y+1:ℕ):Object) = x := Function.eval _ _ _

/-- Створює версію ненульового `n` всередині `Nat \ {0}` для будь-якого натурального числа n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (Nat \ {(0:Object)}: Set) :=
  ⟨((n:ℕ):Object), by
    simp [Object.ofnat_eq',h]
    rw [←Object.ofnat_eq]
    exact Subtype.property _
  ⟩

theorem SetTheory.Set.f_3_3_3c_eval' (n: ℕ) : f_3_3_3c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; simp [f_3_3_3c_eval]

theorem SetTheory.Set.f_3_3_3c_eval'' : f_3_3_3c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_3c_eval' 3

theorem SetTheory.Set.f_3_3_3c_eval''' (n:ℕ) :
    f_3_3_3c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_3c_eval' (2*n+2)

/--
  Приклад 3.3.3 трішки складно відтворити за допомогою поточного формалізму, оскільки дійсні числа
  ще не побудовані. Натомість я пропоную деякі аналоги з Mathlib. Звичайно, для заповнення цих
  sorry знадобиться використання деякого API із Mathlib, наприклад, для невід'ємного
  дійсного класу `NNReal`, і того, як цей клас взаємодіє з `ℝ`.
-/
example : ¬ ∃ f: ℝ → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; set y := f (-1)
  have h1 := (hf _ y).mp (by rfl)
  have h2 := sq_nonneg y
  linarith

example : ¬ ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; specialize hf 4; set y := f 4
  have hy := (hf y).mp (by rfl)
  have h1 : 2 = y := (hf 2).mpr (by norm_num)
  have h2 : -2 = y := (hf (-2)).mpr (by norm_num)
  linarith

example : ∃ f: NNReal → NNReal, ∀ x y, y = f x ↔ y^2 = x := by
  use NNReal.sqrt; intro x y
  constructor <;> intro h
  · rw [h, NNReal.sq_sqrt]
  · rw [←h, NNReal.sqrt_sq]

/-- Приклад 3.3.5. Невикористана змінна `_x` підкреслена, щоб уникнути спрацьовування лінтера. -/
abbrev SetTheory.Set.P_3_3_5 : Nat → Nat → Prop := fun _x y ↦ y = 7

theorem SetTheory.Set.P_3_3_5_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_5 x y := by
  apply ExistsUnique.intro 7 <;> simp [P_3_3_5]

abbrev SetTheory.Set.f_3_3_5 : Function Nat Nat := Function.mk P_3_3_5 P_3_3_5_existsUnique

theorem SetTheory.Set.f_3_3_5_eval (x: Nat) : f_3_3_5 x = 7 := by
  symm; rw [Function.eval]

/-- Визначення 3.3.8 (Рівність функцій) -/
theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x := by
  constructor <;> intro h
  . simp [h]
  ext x y; constructor <;> intros
  . rwa [←Function.eval, ←h x, Function.eval]
  rwa [←Function.eval, h x, Function.eval]

/--
  Приклад 3.3.10 (спрощений).  Другу частину прикладу складно відтворити
  в цьому формалізмі, тому натомість цього пропонується замінник із Mathlib.
-/
abbrev SetTheory.Set.f_3_3_10a : Function Nat Nat := Function.mk_fn (fun x ↦ (x^2 + 2*x + 1:ℕ))

abbrev SetTheory.Set.f_3_3_10b : Function Nat Nat := Function.mk_fn (fun x ↦ ((x+1)^2:ℕ))

theorem SetTheory.Set.f_3_3_10_eq : f_3_3_10a = f_3_3_10b := by
  simp_rw [Function.eq_iff, Function.eval_of]
  intros; simp; ring

example : (fun x:NNReal ↦ (x:ℝ)) = (fun x:NNReal ↦ |(x:ℝ)|) := by
  simp_rw [NNReal.abs_eq]

example : (fun x:ℝ ↦ (x:ℝ)) ≠ (fun x:ℝ ↦ |(x:ℝ)|) := by
  intro h
  let a := (fun (x:ℝ) ↦ x) (-1)
  let b := (fun x:ℝ ↦ |(x:ℝ)|) (-1)
  have hab : a = b := by unfold a; rw [h]
  norm_num [a, b] at hab

/-- Приклад 3.3.11 -/
abbrev SetTheory.Set.f_3_3_11 (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (by intro ⟨ x,hx ⟩; simp at hx)

theorem SetTheory.Set.empty_function_unique {X: Set} (f g: Function (∅:Set) X) : f = g := by sorry

/-- Визначення 3.3.13 (Композиція) -/
noncomputable abbrev Function.comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    Function X Z :=
  Function.mk_fn (fun x ↦ g (f x))

-- `∘` вже використовується в Mathlib для композиції функцій Mathlib,
-- тому ми використовуємо тут `○` замість цього символа, щоб уникнути неоднозначності.
infix:90 "○" => Function.comp

theorem Function.comp_eval {X Y Z: Set} (g: Function Y Z) (f: Function X Y) (x: X) :
    (g ○ f) x = g (f x) := Function.eval_of _ _

/--
  Сумісність з операцією композиції Mathlib. Вам можуть бути корисними
  тактики `ext` та `simp`.
-/
theorem Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn := by
  ext; simp only [Function.comp_eval, Function.comp_apply]

/-- Приклад 3.3.14 -/
abbrev SetTheory.Set.f_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (2*x:ℕ))

abbrev SetTheory.Set.g_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (x+3:ℕ))

theorem SetTheory.Set.g_circ_f_3_3_14 :
    g_3_3_14 ○ f_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+3:ℕ):Nat)) := by
  simp [Function.eq_iff, Function.eval_of]

theorem SetTheory.Set.f_circ_g_3_3_14 :
    f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):Nat)) := by
  simp [Function.eq_iff, Function.eval_of]
  intros; ring

/-- Лема 3.3.15 (Композиція асоціативна) -/
theorem SetTheory.Set.comp_assoc {W X Y Z: Set} (h: Function Y Z) (g: Function X Y)
  (f: Function W X) :
    h ○ (g ○ f) = (h ○ g) ○ f := by
  simp [Function.eq_iff]

abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop := ∀ x x': X, x ≠ x' → f x ≠ f x'

theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
  peel with x hx; tauto

/--
  Сумісність із Mathlib-івським `Function.Injective`.  Можливо, ви захочете скористатися тактикою `unfold`,
  щоб зрозуміти такі концепції Mathlib, як `Function.Injective`.
-/
theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  rw [one_to_one_iff, Function.Injective]

/--
  Приклад 3.3.18.  Одна половина прикладу вимагає цілих чисел, тому виражається
  за допомогою функцій Mathlib замість функцій із Розділу 3.
-/
theorem SetTheory.Set.f_3_3_18_one_to_one :
    (Function.mk_fn (fun (n:Nat) ↦ ((n^2:ℕ):Nat))).one_to_one := by
  rw [Function.one_to_one_iff]
  intro _ _ h
  simpa [Function.eval, Function.eval_of] using h

example : ¬ Function.Injective (fun (n:ℤ) ↦ n^2) := by
  intro h
  have h1 : (fun n ↦ n ^ 2) 1 = (1:ℤ) := by norm_num
  have h2 : (fun n ↦ n ^ 2) (-1) = (1:ℤ) := by norm_num
  nth_rewrite 2 [←h1] at h2
  specialize h h2
  contradiction

example : Function.Injective (fun (n:ℕ) ↦ n^2) := by
  intro _ _ _; rwa [← pow_left_inj₀ (by norm_num) (by norm_num) (show 2 ≠ 0 by norm_num)]

/-- Ремарка 3.3.19 -/
theorem SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x' := by
  rw [Function.one_to_one] at h; aesop

/-- Визначення 3.3.20 (Сур'єктивні функції) -/
abbrev Function.onto {X Y: Set} (f: Function X Y) : Prop := ∀ y: Y, ∃ x: X, f x = y

/-- Сумісність із Mathlib-івським Function.Surjective-/
theorem Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by rfl

/-- Приклад 3.3.21 (використовуючи Mathlib) -/
example : ¬ Function.Surjective (fun (n:ℤ) ↦ n^2) := by
  unfold Function.Surjective; push_neg
  use (-1); intro a
  linarith [sq_nonneg a]

abbrev A_3_3_21 := { m:ℤ // ∃ n:ℤ, m = n^2 }

example : Function.Surjective (fun (n:ℤ) ↦ ⟨ n^2, by use n ⟩ : ℤ → A_3_3_21) := by
  rintro ⟨b, ⟨a, ha⟩⟩; use a
  simp only [ha]

/-- Визначення 3.3.23 (Бієктивні функції) -/
abbrev Function.bijective {X Y: Set} (f: Function X Y) : Prop := f.one_to_one ∧ f.onto

/-- Сумісність із Mathlib-івським Function.Bijective-/
theorem Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  rw [Function.bijective, Function.Bijective, one_to_one_iff', onto_iff]

/-- Приклад 3.3.24 (використовуючи Mathlib) -/
abbrev f_3_3_24 : Fin 3 → ({3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩
| 2 => ⟨ 4, by norm_num ⟩

example : ¬ Function.Injective f_3_3_24 := by decide
example : ¬ Function.Bijective f_3_3_24 := by decide

abbrev g_3_3_24 : Fin 2 → ({2,3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 2, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩

example : ¬ Function.Surjective g_3_3_24 := by decide
example : ¬ Function.Bijective g_3_3_24 := by decide

abbrev h_3_3_24 : Fin 3 → ({3,4,5}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 4, by norm_num ⟩
| 2 => ⟨ 5, by norm_num ⟩

example : Function.Bijective h_3_3_24 := by decide

/--
  Приклад 3.3.25 сформульовано з використанням Mathlib, а не теорії множин, щоб
  уникнути деяких нудних технічних проблем (див. Вправу 3.3.2)
-/
example : Function.Bijective (fun n ↦ ⟨ n+1, by omega⟩ : ℕ → { n:ℕ // n ≠ 0 }) := by
  constructor
  · intro _ _
    simp only [Subtype.mk.injEq]; omega
  intro ⟨x, hx⟩; use x-1
  simp only [Subtype.mk.injEq]; omega

example : ¬ Function.Bijective (fun n ↦ n+1) := by
  suffices h : ¬ Function.Surjective (fun n ↦ n+1) by unfold Function.Bijective; tauto
  unfold Function.Surjective; push_neg
  use 0; intros
  symm; apply Nat.zero_ne_add_one

/-- Ремарка 3.3.27 -/
theorem Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective := by
  use Nat, Nat
  set f := mk_fn fun x ↦ (0: Nat); use f
  constructor
  · intros
    apply existsUnique_of_exists_of_unique
    · use 0; rw [Function.eval]
    intros; rw [Function.eval] at *; aesop
  rw [Function.bijective]
  suffices h : ¬ f.one_to_one by tauto
  rw [Function.one_to_one_iff]
  push_neg; use 0, 1; simp [f]

/--
  Ми не можемо використовувати позначення `f⁻¹` для оберненої функції, оскільки в класі `Inv` Mathlib-у
  обернена функція `f` повинна бути точно такого ж типу, як `f`, а `Function Y X`
  має інший тип, ніж `Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intros
    apply existsUnique_of_exists_of_unique
    . aesop
    intro _ _ hx hx'; simp at hx hx'
    rw [←hx'] at hx
    apply f.one_to_one_iff.mp h.1
    simp [hx]
  )

theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _

/-- Сумісність із Mathlib-овським поняттям інверсивності -/
theorem Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  ext y; congr; symm
  rw [inverse_eval]
  apply Function.rightInverse_invFun (f.bijective_iff.mp h).2

/--
  Вправа 3.3.1.  Хоча доведення, що безпосередньо оперує функціями, було б коротшим,
  суть вправи полягає в тому, щоб показати це, використовуючи визначення `Function.eq_iff`.
-/
theorem Function.refl {X Y:Set} (f: Function X Y) : f = f := by sorry

theorem Function.symm {X Y:Set} (f g: Function X Y) : f = g ↔ g = f := by sorry

theorem Function.trans {X Y:Set} {f g h: Function X Y} (hfg: f = g) (hgh: g = h) : f = h := by sorry

theorem Function.comp_congr {X Y Z:Set} {f f': Function X Y} (hff': f = f') {g g': Function Y Z}
  (hgg': g = g') : g ○ f = g' ○ f' := by sorry

/-- Вправа 3.3.2 -/
theorem Function.comp_of_inj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.one_to_one)
  (hg: g.one_to_one) : (g ○ f).one_to_one := by sorry

theorem Function.comp_of_surj {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.onto)
  (hg: g.onto) : (g ○ f).onto := by sorry

/--
  Вправа 3.3.3 - заповніть sorry у твердженнях розумним чином.
-/
theorem empty_function_one_to_one_iff (X: Set) (f: Function ∅ X) : f.one_to_one ↔ sorry := by sorry

theorem empty_function_onto_iff (X: Set) (f: Function ∅ X) : f.onto ↔ sorry := by sorry

theorem empty_function_bijective_iff (X: Set) (f: Function ∅ X) : f.bijective ↔ sorry:= by sorry

/--
  Вправа 3.3.4.
-/
theorem Function.comp_cancel_left {X Y Z:Set} {f f': Function X Y} {g : Function Y Z}
  (heq : g ○ f = g ○ f') (hg: g.one_to_one) : f = f' := by sorry

theorem Function.comp_cancel_right {X Y Z:Set} {f: Function X Y} {g g': Function Y Z}
  (heq : g ○ f = g' ○ f) (hf: f.onto) : g = g' := by sorry

def Function.comp_cancel_left_without_hg : Decidable (∀ (X Y Z:Set) (f f': Function X Y) (g : Function Y Z) (heq : g ○ f = g ○ f'), f = f') := by
  -- перший рядок цієї побудови має бути або `apply isTrue`, або `apply isFalse`.
  sorry

def Function.comp_cancel_right_without_hg : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g g': Function Y Z) (heq : g ○ f = g' ○ f), g = g') := by
  -- перший рядок цієї побудови має бути або `apply isTrue`, або `apply isFalse`.
  sorry

/--
  Вправа 3.3.5.
-/
theorem Function.comp_injective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hinj :
    (g ○ f).one_to_one) : f.one_to_one := by sorry

theorem Function.comp_surjective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hsurj :
    (g ○ f).onto) : g.onto := by sorry

def Function.comp_injective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hinj :
    (g ○ f).one_to_one), g.one_to_one) := by
  -- перший рядок цієї побудови має бути або `apply isTrue`, або `apply isFalse`.
  sorry

def Function.comp_surjective' : Decidable (∀ (X Y Z:Set) (f: Function X Y) (g : Function Y Z) (hsurj :
    (g ○ f).onto), f.onto) := by
  -- перший рядок цієї побудови має бути або `apply isTrue`, або `apply isFalse`.
  sorry

/-- Вправа 3.3.6 -/
theorem Function.inverse_comp_self {X Y: Set} {f: Function X Y} (h: f.bijective) (x: X) :
    (f.inverse h) (f x) = x := by sorry

theorem Function.self_comp_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) :
    f ((f.inverse h) y) = y := by sorry

theorem Function.inverse_bijective {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).bijective := by sorry

theorem Function.inverse_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by sorry

/-- Вправа 3.3.7 -/
theorem Function.comp_bijective {X Y Z:Set} {f: Function X Y} {g : Function Y Z} (hf: f.bijective)
  (hg: g.bijective) : (g ○ f).bijective := by sorry

theorem Function.inv_of_comp {X Y Z:Set} {f: Function X Y} {g : Function Y Z}
  (hf: f.bijective) (hg: g.bijective) :
    (g ○ f).inverse (Function.comp_bijective hf hg) = (f.inverse hf) ○ (g.inverse hg) := by sorry

/-- Вправа 3.3.8 -/
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )

abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)

theorem Function.inclusion_id (X:Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by sorry

theorem Function.inclusion_comp (X Y Z:Set) (hXY: X ⊆ Y) (hYZ: Y ⊆ Z) :
    Function.inclusion hYZ ○ Function.inclusion hXY = Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) := by sorry

theorem Function.comp_id {A B:Set} (f: Function A B) : f ○ Function.id A = f := by sorry

theorem Function.id_comp {A B:Set} (f: Function A B) : Function.id B ○ f = f := by sorry

theorem Function.comp_inv {A B:Set} (f: Function A B) (hf: f.bijective) :
    f ○ f.inverse hf = Function.id B := by sorry

theorem Function.inv_comp {A B:Set} (f: Function A B) (hf: f.bijective) :
    f.inverse hf ○ f = Function.id A := by sorry

open Classical in
theorem Function.glue {X Y Z:Set} (hXY: Disjoint X Y) (f: Function X Z) (g: Function Y Z) :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by sorry

open Classical in
theorem Function.glue' {X Y Z:Set} (f: Function X Z) (g: Function Y Z)
    (hfg : ∀ x : ((X ∩ Y): Set), f ⟨x.val, by aesop⟩ = g ⟨x.val, by aesop⟩)  :
    ∃! h: Function (X ∪ Y) Z, (h ○ Function.inclusion (SetTheory.Set.subset_union_left X Y) = f)
    ∧ (h ○ Function.inclusion (SetTheory.Set.subset_union_right X Y) = g) := by sorry

end Chapter3
