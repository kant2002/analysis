import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_1

/-!
# Аналіз I, Розділ 9.3: Граничні значення функцій

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Границі неперервних функцій
- Зв'язок із поняттями збіжності фільтрів у Mathlib
- Закони щодо границь для функцій

Технічна заувага: у тексті функції `f`, які розглядаються, визначені лише на підмножинах `X` множини `ℝ`
і не визначені поза ними. Проте в Lean це призводить до незручних приведень типів при спробах
обмежити `f` до різних підмножин `X` (які технічно не є безпосередньо підмножинами `ℝ`, хоча їх можна
привести до таких). Щоб уникнути цієї проблеми, ми відходимо від тексту й вважаємо, що наші
функції визначені на всьому `ℝ` (зрозуміло, що їм присвоюються "сміттеві" значення поза областю `X`).
-/

/-- Визначення 9.3.1 -/
abbrev Real.CloseFn (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) : Prop :=
  ∀ x ∈ X, |f x - L| < ε

/-- Визначення 9.3.3 -/
abbrev Real.CloseNear (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop :=
  ∃ δ > 0, ε.CloseFn (X ∩ .Ioo (x₀-δ) (x₀+δ)) f L

namespace Chapter9

/-- Приклад 9.3.2 -/
example : (5:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by sorry

/-- Приклад 9.3.2 -/
example : (0.41:ℝ).CloseFn (.Icc 1.9 2.1) (fun x ↦ x^2) 4 := by sorry

/-- Приклад 9.3.4 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by
  sorry

/-- Приклад 9.3.4 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  sorry

/-- Приклад 9.3.5 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 9 := by
  sorry

/-- Приклад 9.3.5 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 9 3 := by
  sorry

/-- Визначення 9.3.6 (Збіжність функцій у точці) -/
abbrev Convergesto (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop := ∀ ε > (0:ℝ), ε.CloseNear X f L x₀

/-- Зв'язок із поняттями збіжності фільтрів у Mathlib -/
theorem Convergesto.iff (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) :
  Convergesto X f L x₀ ↔ (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  unfold Convergesto Real.CloseNear Real.CloseFn nhdsWithin
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  rw [Filter.eventually_inf_principal]
  simp [Filter.Eventually, mem_nhds_iff_exists_Ioo_subset]
  constructor
  . intro ⟨ δ, _, _ ⟩; use x₀-δ, x₀+δ, by grind
    intro _; simp; grind
  intro ⟨ l, u, ⟨ _, _ ⟩, h ⟩
  have h1 : 0 < x₀ - l := by linarith
  have h2 : 0 < u - x₀ := by linarith
  set δ := min (x₀ - l) (u - x₀)
  observe hδ1 : δ ≤ x₀ - l
  observe hδ2 : δ ≤ u - x₀
  use δ, (by positivity); intro x hxX _ _
  specialize h (show x ∈ .Ioo l u by simp; grind)
  simpa [hxX] using h

/-- Приклад 9.3.8 -/
example: Convergesto (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  sorry

/-- Твердження 9.3.9 / Вправа 9.3.1 -/
theorem Convergesto.iff_conv {E:Set ℝ} (f: ℝ → ℝ) (L:ℝ) {x₀:ℝ} (h: AdherentPt x₀ E) :
  Convergesto E f L x₀ ↔ ∀ a:ℕ → ℝ, (∀ n:ℕ, a n ∈ E) →
  Filter.atTop.Tendsto a (nhds x₀) →
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  sorry

theorem Convergesto.comp {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (hf: Convergesto E f L x₀) {a:ℕ → ℝ} (ha: ∀ n:ℕ, a n ∈ E) (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  rw [iff_conv f L h] at hf; solve_by_elim

-- Ремарка 9.3.11: можливо, що це зауваження неточне — гіпотезу `AdherentPt x₀ E` може виявитися безпечно видалити в наведених вище теоремах. Формалізація може це прояснити! Якщо так, цю гіпотезу також можна буде видалити в кількох теоремах нижче.

/-- Наслідок 9.3.13 -/
theorem Convergesto.uniq {E:Set ℝ} {f: ℝ → ℝ} {L L':ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hf': Convergesto E f L' x₀) : L = L' := by
  -- цей доказ написан так, щоб співпадати із структурою оригінального тексту.
  let ⟨ a, ha, hconv ⟩ := (limit_of_AdherentPt _ _).mp h
  exact tendsto_nhds_unique (hf.comp h ha hconv) (hf'.comp h ha hconv)

/-- Твердження 9.3.14 (Закони щодо границь функцій) -/
theorem Convergesto.add {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f + g) (L + M) x₀ := by
    -- цей доказ написан так, щоб співпадати із структурою оригінального тексту.
    rw [iff_conv _ _ h] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    convert hf.add hg using 1

/-- Твердження 9.3.14 (Закони щодо границь функцій) / Вправа 9.3.2 -/
theorem Convergesto.sub {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f - g) (L - M) x₀ := by
    sorry

/-- Твердження 9.3.14 (Закони щодо границь функцій) / Вправа 9.3.2 -/
theorem Convergesto.max {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (max f g) (max L M) x₀ := by
    sorry

/-- Твердження 9.3.14 (Закони щодо границь функцій) / Вправа 9.3.2 -/
theorem Convergesto.min {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (min f g) (min L M) x₀ := by
    sorry

/-- Твердження 9.3.14 (Закони щодо границь функцій) / Вправа 9.3.2 -/
theorem Convergesto.smul {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (c:ℝ) :
  Convergesto E (c • f) (c * L) x₀ := by
    sorry

/-- Твердження 9.3.14 (Limit laws for functions) / Вправа 9.3.2 -/
theorem Convergesto.mul {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f * g) (L * M) x₀ := by
    sorry

/-- Твердження 9.3.14 (Закони щодо границь функцій) / Вправа 9.3.2. Гіпотезу в книзі про те, що `g` не звертається в нулі на `E`, можна опустити. -/
theorem Convergesto.div {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (hM: M ≠ 0)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f / g) (L / M) x₀ := by
    sorry

theorem Convergesto.const {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (c:ℝ)
  : Convergesto E (fun x ↦ c) c x₀ := by
  sorry

theorem Convergesto.id {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  : Convergesto E (fun x ↦ x) x₀ x₀ := by
  sorry

theorem Convergesto.sq {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  : Convergesto E (fun x ↦ x^2) x₀ (x₀^2) := by
  sorry

theorem Convergesto.linear {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (c:ℝ)
  : Convergesto E (fun x ↦ c * x) x₀ (c * x₀) := by
  sorry

theorem Convergesto.quadratic {E:Set ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) (c d:ℝ)
  : Convergesto E (fun x ↦ x^2 + c * x + d) x₀ (x₀^2 + c * x₀ + d) := by
  sorry

theorem Convergesto.restrict {X Y:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ X) (hf: Convergesto X f L x₀) (hY: Y ⊆ X) : Convergesto Y f L x₀ := by
  sorry

theorem Real.sign_def (x:ℝ) : Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 := rfl

/-- Приклад 9.3.16 -/
theorem Convergesto.sign_right : Convergesto (.Ioi 0) Real.sign 1 0 := by sorry

/-- Приклад 9.3.16 -/
theorem Convergesto.sign_left : Convergesto (.Iio 0) Real.sign (-1) 0 := by sorry

/-- Приклад 9.3.16 -/
theorem Convergesto.sign_all : ¬ ∃ L, Convergesto (.univ) Real.sign L 0 := by sorry

noncomputable abbrev f_9_3_17 : ℝ → ℝ := fun x ↦ if x = 0 then 1 else 0

theorem Convergesto.f_9_3_17_remove : Convergesto (.univ \ {0}) f_9_3_17 0 0 := by sorry

theorem Convergesto.f_9_3_17_all : ¬ ∃ L, Convergesto .univ f_9_3_17 L 0 := by sorry

/-- Твердження 9.3.18 / Вправа 9.3.3 -/
theorem Convergesto.local {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (h: AdherentPt x₀ E) {δ:ℝ} (hδ: δ > 0) :
  Convergesto E f L x₀ ↔ Convergesto (E ∩ .Ioo (x₀-δ) (x₀+δ)) f L x₀ := by
    sorry

/-- Приклад 9.3.19. Суть цього прикладу дещо втрачається через можливість прибрати гіпотезу про ненульовість `g` у відповідній частині твердження 9.3.14 -/
example : Convergesto .univ (fun x ↦ (x+2)/(x+1)) (4/3:ℝ) 2 := by sorry

/-- Приклад 9.3.20 -/
example : Convergesto (.univ \ {1}) (fun x ↦ (x^2-1)/(x-1)) 2 1 := by sorry

open Classical in
/-- Приклад 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q:ℚ ↦ (q:ℝ)) '' .univ then 1 else 0

example : Filter.atTop.Tendsto (fun n ↦ f_9_3_21 (1/n:ℝ)) (nhds 1) := by sorry

example : Filter.atTop.Tendsto (fun n ↦ f_9_3_21 ((Real.sqrt 2)/n:ℝ)) (nhds 0) := by sorry

example : ¬ ∃ L, Convergesto .univ f_9_3_21 L 0 := by sorry

/- Вправа 9.3.4: Сформулюйте визначення верхньої та нижньої границі (limit superior і limit inferior) для функцій і доведіть аналог твердження 9.3.9 для цих визначень. -/

/-- Вправа 9.3.5 (Неперервна версія принципу стискування) -/
theorem Convergesto.squeeze {E:Set ℝ} {f g h: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (had: AdherentPt x₀ E)
  (hfg: ∀ x ∈ E, f x ≤ g x) (hgh: ∀ x ∈ E, g x ≤ h x)
  (hf: Convergesto E f L x₀) (hh: Convergesto E h L x₀) :
  Convergesto E g L x₀ := by
    sorry


end Chapter9
