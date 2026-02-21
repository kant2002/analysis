import Mathlib.Tactic
import Analysis.Section_4_3

/-!
# Аналіз I, Розділ 5.1: Послідовності Коші

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні побудови та результати цього розділу:

- Поняття послідовності раціональних чисел
- Поняття `ε`-сталість, кінцевої `ε`-сталість та послідовностей Коші

## Підказки від попередніх користувачів

Користувачі супровідного матеріалу, які виконали вправи в цьому розділі, можуть надсилати свої поради майбутнім користувачам цього розділу як PRи.

- (Додайте підказку тут)

-/

namespace Chapter5

/--
  Визначення 5.1.1 (Послідовність). Щоб уникнути деяких технічних питань, пов’язаних із залежними типами, ми розширюємо
послідовності нулями ліворуч від початкової точки `n₀`.
-/
@[ext]
structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0

/-- Послідовності можна розглядати як функції з ℤ у ℚ. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℚ) where
  coe := fun a ↦ a.seq

/--
Функції з ℕ у ℚ можна розглядати як послідовності, що починаються з 0; `ofNatFun` виконує це перетворення.

Атрибут `coe` дозволяє делаборатору виводити `Sequence.ofNatFun f` як `↑f`, що є більш стислим; ви можете безпечно видалити його, якщо віддаєте перевагу більш явному позначенню.
-/
@[coe]
def Sequence.ofNatFun (a : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind

-- Notice how the delaborator prints this as `↑fun x ↦ ↑x ^ 2 : Sequence`.
#check Sequence.ofNatFun (· ^ 2)

/--
Якщо `a : ℕ → ℚ` використовується в контексті, де очікується `Sequence`, автоматично перетворюйте `a` на `Sequence.ofNatFun a` (що буде гарно виведено як `↑a`).
-/
instance : Coe (ℕ → ℚ) Sequence where
  coe := Sequence.ofNatFun

abbrev Sequence.mk' (n₀:ℤ) (a: { n // n ≥ n₀ } → ℚ) : Sequence where
  n₀ := n₀
  seq n := if h : n ≥ n₀ then a ⟨n, h⟩ else 0
  vanish := by grind

lemma Sequence.eval_mk {n n₀:ℤ} (a: { n // n ≥ n₀ } → ℚ) (h: n ≥ n₀) :
    (Sequence.mk' n₀ a) n = a ⟨ n, h ⟩ := by grind

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℚ) : (a:Sequence) n = a n := by norm_cast

@[simp]
lemma Sequence.eval_coe_at_int (n:ℤ) (a: ℕ → ℚ) : (a:Sequence) n = if n ≥ 0 then a n.toNat else 0 := by norm_cast

@[simp]
lemma Sequence.n0_coe (a: ℕ → ℚ) : (a:Sequence).n₀ = 0 := by norm_cast

/-- Приклад 5.1.2 -/
abbrev Sequence.squares : Sequence := ((fun n:ℕ ↦ (n^2:ℚ)):Sequence)

/-- Приклад 5.1.2 -/
example (n:ℕ) : Sequence.squares n = n^2 := Sequence.eval_coe _ _

/-- Приклад 5.1.2 -/
abbrev Sequence.three : Sequence := ((fun (_:ℕ) ↦ (3:ℚ)):Sequence)

/-- Приклад 5.1.2 -/
example (n:ℕ) : Sequence.three n = 3 := Sequence.eval_coe _ (fun (_:ℕ) ↦ (3:ℚ))

/-- Приклад 5.1.2 -/
abbrev Sequence.squares_from_three : Sequence := mk' 3 (·^2)

/-- Приклад 5.1.2 -/
example (n:ℤ) (hn: n ≥ 3) : Sequence.squares_from_three n = n^2 := Sequence.eval_mk _ hn

-- потрібно тимчасово вийти з простору імен `Chapter5`, щоб ввести наступне позначення

end Chapter5

/--
Невелике узагальнення Визначення 5.1.3 — визначення `ε`-сталості для послідовності
з довільною початковою точкою `n₀`.
-/
abbrev Rat.Steady (ε: ℚ) (a: Chapter5.Sequence) : Prop :=
  ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m)

lemma Rat.steady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.n₀, ∀ m ≥ a.n₀, ε.Close (a n) (a m) := by rfl

namespace Chapter5

/--
Визначення 5.1.3 — визначення `ε`-сталості для послідовності, що починається з 0.
-/
lemma Rat.Steady.coe (ε : ℚ) (a:ℕ → ℚ) :
    ε.Steady a ↔ ∀ n m : ℕ, ε.Close (a n) (a m) := by
  constructor
  · intro h n m; specialize h n ?_ m ?_ <;> simp_all
  intro h n hn m hm
  lift n to ℕ using hn
  lift m to ℕ using hm
  simp [h n m]

/--
Не в підручнику: послідовність 3, 3, ... є 1-сталою
Призначено для демонстрації `Rat.Steady.coe`
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  simp [Rat.Steady.coe, Rat.Close]

/--
Порівняйте: якщо потрібно працювати з `Rat.Steady` безпосередньо через перетворення типу, з’являться
додаткові умови `hn : n ≥ 0` та `hm : m ≥ 0`, які доведеться враховувати.
-/
example : (1:ℚ).Steady ((fun _:ℕ ↦ (3:ℚ)):Sequence) := by
  intro n _ m _; simp_all [Sequence.n0_coe, Sequence.eval_coe_at_int, Rat.Close]

/--
Приклад 5.1.5: Послідовність `1, 0, 1, 0, ...` є 1-сталою.
-/
example : (1:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m
  -- Розділіть на чотири випадки залежно від того, чи є n та m парними або непарними
  -- У кожному випадку ми знаємо точне значення a n та a m
  split_ifs <;> simp [Rat.Close]

/--
Приклад 5.1.5: Послідовність `1, 0, 1, 0, ...` не є ½-сталою.
-/
example : ¬ (0.5:ℚ).Steady ((fun n:ℕ ↦ if Even n then (1:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]
  by_contra h; specialize h 0 1; simp [Rat.Close] at h
  norm_num at h

/--
Приклад 5.1.5: Послідовність 0.1, 0.01, 0.001, ... є 0.1-сталою.
-/
example : (0.1:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by
  rw [Rat.Steady.coe]
  intro n m; unfold Rat.Close
  wlog h : m ≤ n
  · specialize this m n (by linarith); rwa [abs_sub_comm]
  rw [abs_sub_comm, abs_of_nonneg]
  . rw [show (0.1:ℚ) = (10:ℚ)^(-1:ℤ) - 0 by norm_num]
    gcongr <;> try grind
    positivity
  linarith [show (10:ℚ) ^ (-(n:ℤ)-1) ≤ (10:ℚ) ^ (-(m:ℤ)-1) by gcongr; norm_num]

/--
Приклад 5.1.5: Послідовність 0.1, 0.01, 0.001, ... не є 0.01-сталою. Залишено як вправу.
-/
example : ¬(0.01:ℚ).Steady ((fun n:ℕ ↦ (10:ℚ) ^ (-(n:ℤ)-1) ):Sequence) := by sorry

/-- Приклад 5.1.5: Послідовність 1, 2, 4, 8, ... не є ε-сталою для жодного ε. Залишено як вправу.
-/
example (ε:ℚ) : ¬ ε.Steady ((fun n:ℕ ↦ (2 ^ (n+1):ℚ) ):Sequence) := by sorry

/-- Приклад 5.1.5:Послідовність 2, 2, 2, ... є ε-сталою для будь-якого ε > 0.
-/
example (ε:ℚ) (hε: ε>0) : ε.Steady ((fun _:ℕ ↦ (2:ℚ) ):Sequence) := by
  rw [Rat.Steady.coe]; simp [Rat.Close]; positivity

/--
Послідовність 10, 0, 0, ... є 10-сталою.
-/
example : (10:ℚ).Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  rw [Rat.Steady.coe]; intro n m
  -- Розділіть на 4 випадки залежно від того, чи n та m дорівнюють 0, чи ні.
  split_ifs <;> simp [Rat.Close]

/--
Послідовність 10, 0, 0, ... не є ε-сталою для будь-якого меншого значення ε.
-/
example (ε:ℚ) (hε:ε<10):  ¬ ε.Steady ((fun n:ℕ ↦ if n = 0 then (10:ℚ) else (0:ℚ)):Sequence) := by
  contrapose! hε; rw [Rat.Steady.coe] at hε; specialize hε 0 1; simpa [Rat.Close] using hε

/--
  a.Від n₁ починається `a:Sequence` з `n₁`. Його призначено для використання, коли `n₁ ≥ n₀`, але
  в іншому випадку воно повертає "сміттєве" значення оригінальної послідовності `a`.
-/
abbrev Sequence.from (a:Sequence) (n₁:ℤ) : Sequence :=
  mk' (max a.n₀ n₁) (fun n ↦ a (n:ℤ))

lemma Sequence.from_eval (a:Sequence) {n₁ n:ℤ} (hn: n ≥ n₁) :
  (a.from n₁) n = a n := by simp [hn]; intro h; exact (a.vanish _ h).symm

end Chapter5

/-- Визначення 5.1.6 (Зрештою ε-стала) -/
abbrev Rat.EventuallySteady (ε: ℚ) (a: Chapter5.Sequence) : Prop := ∃ N ≥ a.n₀, ε.Steady (a.from N)

lemma Rat.eventuallySteady_def (ε: ℚ) (a: Chapter5.Sequence) :
  ε.EventuallySteady a ↔ ∃ N ≥ a.n₀, ε.Steady (a.from N) := by rfl

namespace Chapter5

/--
Приклад 5.1.7: Послідовність 1, 1/2, 1/3, ... не є 0,1-сталою.
-/
lemma Sequence.ex_5_1_7_a : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) := by
  intro h; rw [Rat.Steady.coe] at h; specialize h 0 2; simp [Rat.Close] at h; norm_num at h
  rw [abs_of_nonneg] at h <;> grind

/--
Приклад 5.1.7: Послідовність a_10, a_11, a_12, ... є 0.1-сталою
-/
lemma Sequence.ex_5_1_7_b : (0.1:ℚ).Steady (((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence).from 10) := by
  rw [Rat.Steady]
  intro n hn m hm; simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_all [Rat.Close]
  wlog h : m ≤ n
  · specialize this m n _ _ _ <;> try omega
    rwa [abs_sub_comm] at this
  rw [abs_sub_comm]
  have : ((n:ℚ) + 1)⁻¹ ≤ ((m:ℚ) + 1)⁻¹ := by gcongr
  rw [abs_of_nonneg (by linarith), show (0.1:ℚ) = (10:ℚ)⁻¹ - 0 by norm_num]
  gcongr
  · norm_cast; omega
  positivity

/--
Приклад 5.1.7: Послідовність 1, 1/2, 1/3, ... є зрештою 0,1-сталою.
-/
lemma Sequence.ex_5_1_7_c : (0.1:ℚ).EventuallySteady ((fun n:ℕ ↦ (n+1:ℚ)⁻¹ ):Sequence) :=
  ⟨10, by simp, ex_5_1_7_b⟩

/--
Приклад 5.1.7

Послідовність 10, 0, 0, ... є зрештою ε-сталою для будь-якого ε > 0. Залишено як вправу.
-/
lemma Sequence.ex_5_1_7_d {ε:ℚ} (hε:ε>0) :
    ε.EventuallySteady ((fun n:ℕ ↦ if n=0 then (10:ℚ) else (0:ℚ) ):Sequence) := by sorry

abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℚ), ε.EventuallySteady a

lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

/-- Визначення послідовностей Коші для послідовності, що починається з 0. -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor <;> intro h ε hε
  · choose N hN h' using h ε hε
    lift N to ℕ using hN; use N
    intro j _ k _; simp [Rat.steady_def] at h'; specialize h' j _ k _ <;> try omega
    simp_all; exact h'
  choose N h' using h ε hε
  refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := ?_
  have mpos : 0 ≤ m := ?_
  lift n to ℕ using npos
  lift m to ℕ using mpos
  simp [hn, hm]; specialize h' n _ m _
  all_goals try omega
  norm_cast

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  constructor <;> intro h ε hε <;> choose N hN h' using h ε hε
  · refine ⟨ N, hN, ?_ ⟩; dsimp at hN; intro j _ k _
    simp only [Rat.Steady, show max n₀ N = N by omega] at h'
    specialize h' j _ k _ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
    exact h'
  refine ⟨ max n₀ N, by simp, ?_ ⟩
  intro n _ m _; simp_all
  apply h' n _ m <;> omega

noncomputable def Sequence.sqrt_two : Sequence := (fun n:ℕ ↦ ((⌊ (Real.sqrt 2)*10^n ⌋ / 10^n):ℚ))

/--
  Приклад 5.1.10. (Це вимагає ґрунтовного знайомства з API Mathlib для дійсних чисел.)
-/
theorem Sequence.ex_5_1_10_a : (1:ℚ).Steady sqrt_two := by sorry

/--
  Приклад 5.1.10. (Це вимагає ґрунтовного знайомства з API Mathlib для дійсних чисел.)
-/
theorem Sequence.ex_5_1_10_b : (0.1:ℚ).Steady (sqrt_two.from 1) := by sorry

theorem Sequence.ex_5_1_10_c : (0.1:ℚ).EventuallySteady sqrt_two := by sorry

/-- Твердження 5.1.11. Гармонічна послідовність, визначена як a₁ = 1, a₂ = 1/2, ... є послідовністю Коші. -/
theorem Sequence.IsCauchy.harmonic : (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy := by
  rw [IsCauchy.mk]
  intro ε hε
  -- Ми йдемо у зворотному порядку від книги — спочатку обираємо N таке, що N > 1/ε.
  obtain ⟨ N, hN : N > 1/ε ⟩ := exists_nat_gt (1 / ε)
  have hN' : N > 0 := by
    observe : (1/ε) > 0
    observe : (N:ℚ) > 0
    norm_cast at this
  refine ⟨ N, by norm_cast, ?_ ⟩
  intro j hj k hk
  lift j to ℕ using (by linarith)
  lift k to ℕ using (by linarith)
  norm_cast at hj hk
  simp [show j ≥ 1 by linarith, show k ≥ 1 by linarith]

  have hdist : Section_4_3.dist ((1:ℚ)/j) ((1:ℚ)/k) ≤ (1:ℚ)/N := by
    rw [Section_4_3.dist_eq, abs_le']
    /-
    Ми встановлюємо такі межі:
    - 1/j ∈ [0, 1/N]
    - 1/k ∈ [0, 1/N]
    Це означає, що відстань між 1/j та 1/k не перевищує 1/N — коли вони максимально "рознесені".
    -/
    have : 1/j ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/j
    have : 1/k ≤ (1:ℚ)/N := by gcongr
    observe : (0:ℚ) ≤ 1/k
    grind
  simp at *; apply hdist.trans
  rw [inv_le_comm₀] <;> try positivity
  order

abbrev BoundedBy {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : Prop := ∀ i, |a i| ≤ M

/--
  Визначення 5.1.12 (обмежені послідовності). Тут ми починаємо послідовності з 0 замість 1,
  щоб краще узгоджуватись із конвенціями Mathlib.
-/
lemma boundedBy_def {n:ℕ} (a: Fin n → ℚ) (M:ℚ) : BoundedBy a M ↔ ∀ i, |a i| ≤ M := by rfl

abbrev Sequence.BoundedBy (a:Sequence) (M:ℚ) : Prop := ∀ n, |a n| ≤ M

/-- Визначення 5.1.12 (обмежені послідовності) -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℚ) : a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Визначення 5.1.12 (обмежені послідовності) -/
lemma Sequence.isBounded_def (a:Sequence) : a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

/-- Приклад 5.1.13 -/
example : BoundedBy ![1,-2,3,-4] 4 := by intro i; fin_cases i <;> norm_num

/-- Приклад 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1)^n * (n+1:ℚ)):Sequence).IsBounded := by sorry

/-- Приклад 5.1.13 -/
example : ((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsBounded := by
  refine ⟨ 1, by norm_num, ?_ ⟩; intro i; by_cases h: 0 ≤ i <;> simp [h]

/-- Приклад 5.1.13 -/
example : ¬((fun n:ℕ ↦ (-1:ℚ)^n):Sequence).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  by_contra h; specialize h (1/2 : ℚ) (by norm_num)
  choose N h using h; specialize h N _ (N+1) _ <;> try omega
  by_cases h': Even N
  · simp [h'.neg_one_pow, (h'.add_one).neg_one_pow, Section_4_3.dist] at h
    norm_num at h
  observe h₁: Odd N
  observe h₂: Even (N+1)
  simp [h₁.neg_one_pow, h₂.neg_one_pow, Section_4_3.dist] at h
  norm_num at h

/-- Лема 5.1.14 -/
lemma IsBounded.finite {n:ℕ} (a: Fin n → ℚ) : ∃ M ≥ 0,  BoundedBy a M := by
  -- цей доказ написан так, щоб співпадати із структурою оригінального тексту.
  induction' n with n hn
  . use 0; simp
  set a' : Fin n → ℚ := fun m ↦ a m.castSucc
  choose M hpos hM using hn a'
  have h1 : BoundedBy a' (M + |a (Fin.ofNat _ n)|) := fun m ↦ (hM m).trans (by simp)
  have h2 : |a (Fin.ofNat _ n)| ≤ M + |a (Fin.ofNat _ n)| := by simp [hpos]
  refine ⟨ M + |a (Fin.ofNat _ n)|, by positivity, ?_ ⟩
  intro m; obtain ⟨ j, rfl ⟩ | rfl := Fin.eq_castSucc_or_eq_last m
  . grind
  convert h2; simp

/-- Лема 5.1.15 (Послідовності Коші є обмеженими) / Вправа 5.1.1 -/
lemma Sequence.isBounded_of_isCauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  sorry

/-- Вправа 5.1.2 -/
theorem Sequence.isBounded_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a + b:Sequence).IsBounded := by sorry

theorem Sequence.isBounded_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a - b:Sequence).IsBounded := by sorry

theorem Sequence.isBounded_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hb: (b:Sequence).IsBounded):
    (a * b:Sequence).IsBounded := by sorry

end Chapter5
