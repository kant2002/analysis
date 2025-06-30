import Mathlib.Tactic

/-!
# Аналіз I, Глава 3.1

У цій главі ми пропонуємо версію теорії множин Цермело-Франкеля (з атомами), яка намагається
максимально точно наслідувати оригінальний тексту Аналізу I, Глава 3.1. Вся нумерація
посилається на оригінальний текст.

Я *(пр.перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним рішенням Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підбуцнути",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Тип множин `Chapter3.SetTheory.Set`
- Тип об'єктів `Chapter3.SetTheory.Object`
- Аксіома що кожна множина є (або може бути перетворена на) об'єкт
- Порожня множина `∅`, сінглетони `{y}`, та пари `{y,z}` (та більш узагальнені кінцеві кортежі), із
  їх супутнімі аксіомами
- Попарне об'єднання `X ∪ Y`, та його супутні аксіоми
- Приведення множини `A` до пов'язаного з нею типу `A.toSubtype`, який є підтипом `Object`, та
  базового API. (Це технічна конструкція, необхідна для того, щоб зробити теорію множин
  Цермело-Франкеля сумісною з теорією залежних типів Lean.)
- Специфікація `A.specify P` множини `A` та предикат `P: A.toSubtype → Prop` до
  підмножини елементів `A`, що підпорядковуються `P`, та аксіома специфікації.
  TODO: якось реалізувати конструктора множин для цього.

- Заміна `A.replace hP` множини `A` за допомогою предиката `P: A.toSubtype → Object → Prop`,
  що підпорядковується умові унікальності `∀ x y y', P x y ∧ P x y' → y = y'`,
  та аксіомі заміщення.
- Бієктивна відповідність між натуральними числами Mathlib `ℕ` та множиною
  `Chapter3.Nat : Chapter3.Set` (аксіомою нескінченності).
- Аксіоми регулярності, степеневої множини та об'єднання (використовуються
  в наступних розділах цього розділу, але не обов'язкові тут)
- Поєднання із Mathlib-овською нотацію множини

Інші аксіоми теорії множин Цермело-Френкеля обговорюються в наступних розділах.

Деякі технічні зауваження:
- Звичайно, Mathlib має власне поняття `Set`, яке несумісне з поняттям `Chapter3.Set`,
  визначеним тут, хоча ми спробуємо зробити позначення максимально збігаючимися.
  Це спричиняє певний конфлікт позначень: наприклад, може знадобитися явно вказати `(∅:Chapter3.Set)`
  замість просто `∅`, щоб вказати, що використовується версія порожньої множини `Chapter3.Set`,
  а не версія порожньої множини Mathlib, і аналогічно для інших позначень, визначених тут.
- В Аналізі I ми вирішили працювати з "нечистою" теорією множин, в якій може бути більше `Object`-ів,
  ніж просто `Set`-ів. У теорії типів Lean це вимагає розглядати `Chapter3.Set` та `Chapter3.Object`
  як окремі типи. Іноді це означає, що нам доводиться використовувати приведення `X.toObject` від `Chapter3.Set` `X`,
  щоб перетворити його на `Chapter3.Object`: це здебільшого потрібно під час маніпулювання множинами множин.
- Після завершення цього розділу поняття `Chapter3.SetTheory.Set` буде відхилено на користь
  стандартного позначення `Set` від Mathlib (або, точніше, типу `Set X` множини в заданому типі `X`).
  Однак, через різні технічні несумісності між теорією множин та теорією типів, ми не намагатимемося
  створити будь-яку еквівалентність між цими двома поняттями множин. (Таким чином, це робить весь
  цей розділ необов'язковим з точки зору решти книги, хоча ми зберігаємо його для педагогічних цілей.)
-/


namespace Chapter3

/-- Деякі аксіоми теорії Цермело-Франкеля з атомами  -/
class SetTheory where
  Set : Type -- Аксіома 3.1
  Object : Type -- Аксіома 3.1
  set_to_object : Set ↪ Object -- Аксіома 3.1
  mem : Object → Set → Prop -- Аксіома 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Аксіома 3.2
  emptyset: Set -- Аксіома 3.3
  emptyset_mem x : ¬ mem x emptyset -- Аксіома 3.3
  singleton : Object → Set -- Аксіома 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Аксіома 3.4
  union_pair : Set → Set → Set -- Аксіома 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Аксіома 3.5
  specify A (P: Subtype (mem . A) → Prop) : Set -- Аксіома 3.6
  specification_axiom A (P: Subtype (mem . A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Аксіома 3.6
  replace A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : Set -- Аксіома 3.7
  replacement_axiom A (P: Subtype (mem . A) → Object → Prop)
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') : ∀ y, mem y (replace A P hP) ↔ ∃ x, P x y -- Аксіома 3.7
  nat : Set -- Аксіома 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Аксіома 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Аксіома 3.9
  pow : Set → Set → Set -- Аксіома 3.11
  function_to_object (X: Set) (Y: Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Аксіома 3.11
  power_set_axiom (X: Set) (Y: Set) (F:Object) :
    mem F (pow X Y) ↔ ∃ f: Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Аксіома 3.11
  union : Set → Set -- Аксіома 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Аксіома 3.12

export SetTheory (Set Object)

-- Цей екземпляр неявно нав'язує (деякі) аксіоми теорії множин Цермело-Френкеля з атомами.
variable [SetTheory]


/-- Визначення 3.1.1 (об'єкти можуть бути елементами множин) -/
instance objects_mem_sets : Membership Object Set where
  mem X x := SetTheory.mem x X

/-- Аксіома 3.1 (Множини це об'єкти)-/
instance sets_are_objects : Coe Set Object where
  coe X := SetTheory.set_to_object X

abbrev SetTheory.Set.toObject (X:Set) : Object := X

/-- Аксіома 3.1 (Множини це об'єкти)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: X.toObject = Y.toObject) : X = Y :=
  SetTheory.set_to_object.inj' h

/-- Аксіома 3.1 (Множини це об'єкти)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : X.toObject = Y.toObject ↔  X = Y := by
  constructor
  . exact coe_eq
  intro h; subst h; rfl

/-- Аксіома 3.2 (Рівність множин)-/
abbrev SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := SetTheory.extensionality _ _ h

/-- Аксіома 3.2 (Рівність множин)-/
theorem SetTheory.Set.ext_iff (X Y: Set) : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y := by
  constructor
  . intro h; subst h; simp
  . intro h; apply ext; exact h

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := SetTheory.emptyset

/--
  Axiom 3.3 (порожня множина).
  Примітка: можливо, доведеться явно перетворити ∅ на Set через існуючу нотацію теорії множин Mathlib.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := SetTheory.emptyset_mem

/-- Порожня множина не має елементів -/
theorem SetTheory.Set.eq_empty_iff_forall_notMem {X:Set} : X = ∅ ↔ (∀ x, x ∉ X) := by
  sorry

/-- Порожня множина унікальна -/
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X := by
  sorry

/-- Лема 3.1.5 (Одиничний вибір) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  by_contra! this
  have claim (x:Object) : x ∈ X ↔ x ∈ (∅:Set) := by
    simp [this, not_mem_empty]
  replace claim := ext claim
  contradiction

theorem SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅ := by
  contrapose! h
  rw [eq_empty_iff_forall_notMem] at h
  exact h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := SetTheory.singleton

/--
  Axiom 3.3(a) (сінглтон).
  Зверніть увагу, що, можливо, доведеться явно перетворити {a} на Set через існуючу нотацію теорії множин Mathlib.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := by
  exact SetTheory.singleton_axiom x a


instance SetTheory.Set.instUnion : Union Set where
  union := SetTheory.union_pair

/-- Аксіома 3.4 (Попарне об'єднання)-/
@[simp]
theorem SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  SetTheory.union_pair_axiom X Y x

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

/-- Аксіома 3.3(b) (пара). Зверніть увагу, що часто доводиться перетворювати {a,b} на Set -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Аксіома 3.3(b) (пара). Зверніть увагу, що часто доводиться перетворювати {a,b} на Set -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  simp [pair_eq, mem_union, mem_singleton]

@[simp]
theorem SetTheory.Set.mem_triple (x a b:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  simp [Insert.insert, mem_union, mem_singleton]

/-- Ремарка 3.1.8 -/
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by sorry

/-- Ремарка 3.1.8 -/
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by sorry

/-- Ремарка 3.1.8 -/
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by sorry

/-- Ремарка 3.1.8 -/
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  sorry

/-- Вправа 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) :
    a = c ∧ b = d ∨ a = d ∧ b = c := by
  sorry

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {empty.toObject}
abbrev SetTheory.Set.pair_empty : Set := {empty.toObject, singleton_empty.toObject}

/-- Вправа 3.1.2-/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  sorry

/-- Вправа 3.1.2-/
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by sorry

/-- Вправа 3.1.2-/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  sorry

/--
  Ремарка 3.1.11.
  (Ці результати можна довести або прямим переписуванням, або за допомогою екстенсіональності.)
-/
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by sorry

/--
  Ремарка 3.1.11.
  (Ці результати можна довести або прямим переписуванням, або за допомогою екстенсіональності.)
-/
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by sorry

/-- Лема 3.1.12 (Основні властивості об'єднань) / Вправа 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b:Object) :
    ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  sorry

/-- Лема 3.1.12 (Основні властивості об'єднань) / Вправа 3.1.3 -/
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by sorry

/-- Лема 3.1.12 (Основні властивості об'єднань) / Вправа 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  apply ext
  intro x
  constructor
  . intro hx
    rw [mem_union] at hx
    rcases hx with case1 | case2
    . rw [mem_union] at case1
      rcases case1 with case1a | case1b
      . rw [mem_union]; tauto
      have : x ∈ B ∪ C := by rw [mem_union]; tauto
      rw [mem_union]; tauto
    have : x ∈ B ∪ C := by rw [mem_union]; tauto
    rw [mem_union]; tauto
  sorry

/-- Твердження 3.1.27(c) -/
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  sorry

/-- Твердження 3.1.27(a) -/
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  sorry

/-- Твердження 3.1.27(a) -/
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  sorry

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Приклад 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) :
    ({a,b}:Set) ∪ {b,c} = {a,b,c} := sorry

/-- Визначення 3.1.14.   -/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

/--
  Визначення 3.1.14.
  Зверніть увагу, що операція строгої підмножини в Mathlib позначається `⊂`, а не `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

/-- Визначення 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Визначення 3.1.14.
  Зверніть увагу, що операція строгої підмножини в Mathlib позначається `⊂`, а не `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Ремарка 3.1.15 -/
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by sorry

/-- Приклади 3.1.16 -/
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A := by sorry

/-- Приклади 3.1.16 -/
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A := by sorry

/-- Твердження 3.1.17 (Часткове впорядкування через підмножини) -/
theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  replace hx := hAB x hx
  replace hx := hBC x hx
  assumption

/-- Твердження 3.1.17 (Часткове впорядкування через підмножини) -/
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  sorry

/-- Твердження 3.1.17 (Часткове впорядкування через підмножини) -/
theorem SetTheory.Set.ssubset_trans (A B C:Set) (hAB:A ⊂ B) (hBC:B ⊂ C) : A ⊂ C := by
  sorry

/--
  This defines the subtype `A.toSubtype` for any `A:Set`.  To produce an element `x'` of this
  subtype, use `⟨ x, hx ⟩`, where `x:Object` and `hx:x ∈ A`.  The object `x` associated to a
  subtype element `x'` is recovered as `x.val`, and the property `hx` that `x` belongs to `A` is
  recovered as `x.property`
  Це визначає підтип `A.toSubtype` для будь-якого `A:Set`. Щоб створити елемент `x'` цього підтипу, використовуйте `⟨ x, hx ⟩`, де `x:Object` та `hx:x ∈ A`. Об'єкт `x`, пов'язаний з елементом підтипу `x'`, відновлюється як `x.val`, а властивість `hx`, що `x` належить `A`, відновлюється як `x.property`.
-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)

instance : CoeSort (Set) (Type) where
  coe A := A.toSubtype

/--
  Елементи множини (неявно приведені до підтипу) також є елементами множини
  (щодо операції належності теорії множин).
-/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := rfl

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj


/--
  Якщо є доказ `hx` для `x ∈ A`, тоді `A.subtype_mk hx` зробить елемент `A`
  (розглядаємий як підтип) відповідним `x`.
-/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl



abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

/-- Аксіома 3.6 (аксіома виділення) -/
theorem SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) :
    x ∈ A :=
  (SetTheory.specification_axiom A P).1 x h

/-- Аксіома 3.6 (аксіома виділення) -/
theorem SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A.toSubtype) :
    x.val ∈ A.specify P ↔ P x :=
  (SetTheory.specification_axiom A P).2 x

/-- Аксіома 3.6 (аксіома виділення) -/
theorem SetTheory.Set.specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ := by
  constructor
  . intro h
    have h' := specification_axiom h
    use h'
    rw [←specification_axiom' P ⟨ x, h' ⟩ ]
    simp [h]
  intro h
  obtain ⟨ h, hP ⟩ := h
  rw [←specification_axiom' P ⟨ x,h ⟩ ] at hP
  simp at hP; assumption

theorem SetTheory.Set.specify_subset {A:Set} (P: A → Prop) : A.specify P ⊆ A := by sorry

/-- Ця вправа може вимагати певного розуміння того, як підтипи реалізовані в Lean. -/
theorem SetTheory.Set.specify_congr {A A':Set} (hAA':A = A') {P: A → Prop} {P': A' → Prop}
  (hPP': (x:Object) → (h:x ∈ A) → (h':x ∈ A') → P ⟨ x, h⟩ ↔ P' ⟨ x, h'⟩ ) :
    A.specify P = A'.specify P' := by sorry

instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

/-- Визначення 3.1.22 (Перетин) -/
@[simp]
theorem SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∈ Y) ⟨ x,hX⟩).mpr hY

instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

/-- Визначення 3.1.26 (Різниця) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  . intro h
    have h' := specification_axiom h
    simp [h']
    exact (specification_axiom' _ ⟨ x, h' ⟩ ).mp h
  intro ⟨ hX, hY ⟩
  exact (specification_axiom' (fun x ↦ x.val ∉ Y) ⟨ x, hX⟩ ).mpr hY

/-- Твердження 3.1.27(d) / Вправа 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B:Set) : A ∩ B = B ∩ A := by sorry

/-- Твердження 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X: Set} (hAX: A ⊆ X) : A ∪ X = X := by sorry

/-- Твердження 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X: Set} (hAX: A ⊆ X) : X ∪ A = X := by sorry

/-- Твердження 3.1.27(c) -/
theorem SetTheory.Set.inter_self (A:Set) : A ∩ A = A := by
  sorry

/-- Твердження 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C:Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by sorry

/-- Твердження 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C:Set) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := sorry

/-- Твердження 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := sorry

/-- Твердження 3.1.27(f) -/
theorem SetTheory.Set.union_compl {A X:Set} (hAX: A ⊆ X) : A ∪ (X \ A) = X := by sorry

/-- Твердження 3.1.27(f) -/
theorem SetTheory.Set.inter_compl {A X:Set} (hAX: A ⊆ X) : A ∩ (X \ A) = ∅ := by sorry

/-- Твердження 3.1.27(g) -/
theorem SetTheory.Set.compl_union {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
    X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by sorry

/-- Твердження 3.1.27(g) -/
theorem SetTheory.Set.compl_inter {A B X:Set} (hAX: A ⊆ X) (hBX: B ⊆ X) :
    X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by sorry

/-- Не з підручника: множини утворюють дистрибутивну решітку. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by sorry
  le_sup_right := by sorry
  sup_le := by sorry
  inf_le_left := by sorry
  inf_le_right := by sorry
  le_inf := by sorry
  le_sup_inf := by
    intro X Y Z
    change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]
    exact subset_self _

/-- Множини мають мінімальний елемент.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

/-- Визначення неперетинності (з використанням попередніх прикладів) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Аксіома 3.7 (Аксіомна схема підстановки) -/
theorem SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop}
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y := SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

/-- Аксіома 3.8 (Аксіома нескінченності) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Нижче наведено деякі API для обробки приведень. Це може бути не оптимальним способом налаштування.

instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

example : (5:Nat) ≠ (3:Nat) := by
  simp

example : (5:Object) ≠ (3:Object) := by
  simp

/-- Приклад 3.1.16 (спрощений).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  sorry

/-- Приклад 3.1.17 (спрощений). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3)
 = {(5:Object)} := by
  sorry

/-- Приклад 3.1.24 -/

example : ({1, 2, 4}:Set) ∩ {2,3,4} = {2, 4} := by sorry

/-- Приклад 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by sorry

example : ¬ Disjoint  ({1, 2, 3}:Set)  {2,3,4} := by sorry

example : Disjoint (∅:Set) ∅ := by sorry

/-- Визначення 3.1.26 приклад -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by sorry

/-- Приклад 3.1.30 -/

example : ({3,5,9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ)) (by sorry) = {4,6,10} := by sorry

/-- Приклад 3.1.31 -/

example : ({3,5,9}:Set).replace (P := fun x y ↦ y=1) (by sorry) = {1} := by sorry

/-- Вправа 3.1.5.  Тут можна використовувати тактики `tfae_have` та `tfae_finish`. -/
theorem SetTheory.Set.subset_tfae (A B C:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by sorry

/-- Вправа 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A := by
  sorry

/-- Вправа 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B := by
  sorry

/-- Вправа 3.1.7 -/
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := by
  sorry

/-- Вправа 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B := by
  sorry

/-- Вправа 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B := by
  sorry

/-- Вправа 3.1.7 -/
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := by
  sorry

/-- Вправа 3.1.8 -/
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by sorry

/-- Вправа 3.1.8 -/
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by sorry

/-- Вправа 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    A = X \ B := by sorry

/-- Вправа 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X:Set} (h_union: A ∪ B = X) (h_inter: A ∩ B = ∅) :
    B = X \ A := by
  sorry

/-- Вправа 3.1.10 -/
theorem SetTheory.Set.pairwise_disjoint (A B:Set) :
    Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A]) := by sorry

/-- Вправа 3.1.10 -/
theorem SetTheory.Set.union_eq_partition (A B:Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by sorry

/--
  Вправа 3.1.11.
  Завдання полягає в тому, щоб довести це без використання `Set.specify`, `Set.specification_axiom` або `Set.specification_axiom`.
-/
theorem SetTheory.Set.specification_from_replacement {A:Set} {P: A → Prop} :
    ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x := by sorry

/-- Вправа 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∪ B' ⊆ A ∪ B := by sorry

/-- Вправа 3.1.12.-/
theorem SetTheory.Set.subset_inter_subset {A B A' B':Set} (hA'A: A' ⊆ A) (hB'B: B' ⊆ B) :
    A' ∩ B' ⊆ A ∩ B := by sorry

/-- Вправа 3.1.12.-/
theorem SetTheory.Set.subset_diff_subset_counter :
    ∃ (A B A' B':Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B) := by sorry

/-
  Заключна частина Вправи 3.1.12: сформулюйте та доведіть обґрунтований позитивний результат
  заміни для вищенаведеної теореми, який включає різниці множин.
-/

/-- Вправа 3.1.13 -/
theorem SetTheory.Set.singleton_iff (A:Set) (hA: A ≠ ∅) : (¬∃ B ⊂ A, B ≠ ∅) ↔ ∃ x, A = {x} := by sorry


/-
  Тепер ми введемо зв'язки між цим поняттям множини та поняттям Mathlib.
  Вправа нижче ознайомить вас з API для множин Mathlib.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

/--
  Ін'єктивність перетворення. Зауважте, однак, що ми НЕ стверджуємо, що перетворення є сюръєктивним
  (і насправді парадокс Рассела цьому перешкоджає).
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y:Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y := by
  constructor
  . intro h; apply ext; intro x
    apply_fun (fun S ↦ x ∈ S) at h
    simp at h; assumption
  intro h; subst h; rfl

/-- Сумісність операції належності ∈ -/
theorem SetTheory.Set.mem_coe (X:Set) (x:Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp [Coe.coe]

/-- Сумісність порожньої множини -/
theorem SetTheory.Set.coe_empty : ((∅:Set) : _root_.Set Object) = ∅ := by sorry

/-- Сумісність підмножини -/
theorem SetTheory.Set.coe_subset (X Y:Set) :
    (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y := by sorry

theorem SetTheory.Set.coe_ssubset (X Y:Set) :
    (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y := by sorry

/-- Сумісність синглтона -/
theorem SetTheory.Set.coe_singleton (x: Object) : ({x} : _root_.Set Object) = {x} := by sorry

/-- Сумісність об'еднання -/
theorem SetTheory.Set.coe_union (X Y: Set) :
    (X ∪ Y : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object) := by sorry

/-- Сумісність пари -/
theorem SetTheory.Set.coe_pair (x y: Object) : ({x, y} : _root_.Set Object) = {x, y} := by sorry

/-- Сумісність підтипу -/
theorem SetTheory.Set.coe_subtype (X: Set) :  (X : _root_.Set Object) = X.toSubtype := by sorry

/-- Сумісність перетину -/
theorem SetTheory.Set.coe_intersection (X Y: Set) :
    (X ∩ Y : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object) := by sorry

/-- Сумісність різниці множин-/
theorem SetTheory.Set.coe_diff (X Y: Set) :
    (X \ Y : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object) := by sorry

/-- Сумісність неперетинності -/
theorem SetTheory.Set.coe_Disjoint (X Y: Set) :
    Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y := by sorry

end Chapter3
