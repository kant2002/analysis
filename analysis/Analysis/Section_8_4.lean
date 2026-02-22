import Mathlib.Tactic
import Analysis.Section_8_1
import Analysis.Section_8_2

/-!
# Аналіз I, Розділ 8.4: Аксіома вибору

Я *(прим. перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним підходом Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підправити",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Огляд типу залежного добутку Mathlib `∀ α, X α`.
- Аксіома вибору в різних еквівалентних формах, а також її рахункова версія.

Оскільки розділ 3, присвячений теорії множин, у багатьох місцях вже не використовується, ми не будемо
вставляти аксіому вибору безпосередньо в цю теорію у цьому тексті; проте це можна зробити за бажання
(наприклад, розширивши клас `Chapter3.SetTheory` до `Chapter3.SetTheoryWithChoice`), і студентам
можна запропонувати зробити це окремо. Натомість ми використовуватимемо вбудовану в Mathlib
аксіому `Classical.choice`. Технічно ця аксіома вже досить часто використовувалась у тексті, оскільки
Mathlib використовує `Classical.choice` для виведення багатьох слабших тверджень, наприклад закону виключеного третього.
Тож розмежування, зроблене в оригінальному тексті щодо того, чи використовує конкретне твердження
аксіому вибору, у цій формалізації дещо розмито. Теоретично можна відновити це розмежування,
прибравши залежність від Mathlib і працюючи з власними структурами типу
`Chapter3.SetTheory` і `Chapter3.SetTheoryWithChoice`, але це було б дуже трудомістким і тут не розглядається.
-/

namespace Chapter8

/-- Визначення 8.4.1 (Нескінченні декартові добутки). Ми уникатимемо використання цієї
дефініції на користь форми Mathlib `∀ α, X α`, яка, як незабаром покажемо є еквівалентною (або,
точніше, такою, що узагальнює) цю.

Оскільки Lean не дозволяє необмежених об'єднань типів, ми дещо обходимо це, припускаючи,
що всі `X α` є підмножинами в спільній універсі `U`. Зауважте, що визначення в Mathlib не має
цього обмеження. -/
abbrev CartesianProduct {I U: Type} (X : I → Set U) := { x : I → ⋃ α, X α // ∀ α, ↑(x α) ∈ X α }

/-- Еквівалентність з добутком у Mathlib -/
def CartesianProduct.equiv {I U: Type} (X : I → Set U) :
  CartesianProduct X ≃ ∀ α, X α := {
  toFun x α := ⟨ x.val α, by aesop ⟩
  invFun x := ⟨ fun α ↦ ⟨ x α, by simp; use α; aesop ⟩, by aesop ⟩
  left_inv x := by aesop
  right_inv x := by aesop
  }

/-- Приклад 8.4.2. -/
def Function.equiv {I X:Type} : (∀ _:I, X) ≃ (I → X) := {
  toFun f := f
  invFun f := f
  left_inv f := rfl
  right_inv f := rfl
}

def product_zero_equiv {X: Fin 0 → Type} : (∀ i:Fin 0, X i) ≃ PUnit := {
  toFun f := PUnit.unit
  invFun x i := nomatch i
  left_inv f := by aesop
  right_inv f := rfl
}

def product_one_equiv {X: Fin 1 → Type} : (∀ i:Fin 1, X i) ≃ X 0 := {
  toFun f := f 0
  invFun x i := by rwa [←Fin.fin_one_eq_zero i] at x
  left_inv f := by ext i; rw [Fin.fin_one_eq_zero i]; simp
  right_inv f := rfl
}

def product_two_equiv {X: Fin 2 → Type} : (∀ i:Fin 2, X i) ≃ (X 0 × X 1) := {
  toFun f := (f 0, f 1)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2
  left_inv f := by aesop
  right_inv f := rfl
}

def product_three_equiv {X: Fin 3 → Type} : (∀ i:Fin 3, X i) ≃ (X 0 × X 1 × X 2) := {
  toFun f := (f 0, f 1, f 2)
  invFun f i := match i with
    | 0 => f.1
    | 1 => f.2.1
    | 2 => f.2.2
  left_inv f := by aesop
  right_inv f := rfl
}

/-- Аксіома 8.1 (Аксіома вибору) -/
theorem axiom_of_choice {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by use fun i ↦ (h i).some

theorem axiom_of_countable_choice {I: Type} {X: I → Type} [Countable I] (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := axiom_of_choice h

/-- Лема 8.4.5 -/
theorem exist_tendsTo_sup {E: Set ℝ} (hnon: E.Nonempty) (hbound: BddAbove E) :
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  -- Доведення написане так, щоб відповідати структурі оригінального тексту.
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1:ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1:ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1:ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, ConditionallyCompleteLattice.le_csSup _ _ hbound hs.1 ⟩
  have ⟨ a ⟩ := axiom_of_countable_choice hX
  use fun n ↦ ↑(a n); constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ sSup E - 1/(n+1:ℝ)) (h := fun _:ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro n; have := (a n).property; simp_all [X]

/-- Зауваження 8.4.6. Цей спеціальний випадок Леми 8.4.5 обходиться без (рахункової) аксіоми вибору. -/
theorem exist_tendsTo_sup_of_closed {E: Set ℝ} (hnon: E.Nonempty) (hbound: BddAbove E) (hclosed: IsClosed E) :
  ∃ a : ℕ → ℝ, (∀ n, a n ∈ E) ∧ Filter.atTop.Tendsto a (nhds (sSup E)) := by
  set X : ℕ → Set ℝ := fun n ↦ { x ∈ E | sSup E - 1 / (n+1:ℝ) ≤ x ∧ x ≤ sSup E }
  have hX : ∀ n, Nonempty (X n) := by
    intro n
    have : 1 / (n+1:ℝ) > 0 := by positivity
    choose s hs using (lt_csSup_iff hbound hnon).mp (show sSup E - 1 / (n+1:ℝ) < sSup E by linarith)
    use s; simp_all [X]
    refine ⟨ by linarith, ConditionallyCompleteLattice.le_csSup _ _ hbound hs.1 ⟩
  set a : ℕ → ℝ := fun n ↦ sInf (X n)
  have ha (n:ℕ) : a n ∈ X n := by
    apply IsClosed.csInf_mem _ Set.Nonempty.of_subtype
    . rw [bddBelow_def]; use sSup E - 1 / (n+1:ℝ); aesop
    . rw [show X n = E ∩ .Icc (sSup E - 1 / (n+1:ℝ)) (sSup E) by ext; aesop]
      exact hclosed.inter isClosed_Icc
  use a; constructor; swap
  apply Filter.Tendsto.squeeze (g := fun n:ℕ ↦ sSup E - 1/(n+1:ℝ)) (h := fun _:ℕ ↦ sSup E)
  . convert tendsto_const_nhds.sub (a := sSup E) (b := 0) _; simp
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  . exact tendsto_const_nhds
  all_goals intro _; simp_all [X]

/-- Твердження 8.4.7 / Вправа 8.4.1 -/
theorem exists_function {X Y : Type} {P : X → Y → Prop} (h: ∀ x, ∃ y, P x y) :
  ∃ f : X → Y, ∀ x, P x (f x) := by
  sorry

/-- Вправа 8.4.1. Сенс цього завдання — встановити цей результат прямо з `exists_function`,
уникаючи попередніх результатів, що більш явно покладалися на аксіому вибору. -/
theorem axiom_of_choice_from_exists_function {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := ⟨ fun i ↦ (h i).some ⟩

/-- Вправа 8.4.2 -/
theorem exists_set_singleton_intersect {I U:Type} {X: I → Set U} (h: Set.PairwiseDisjoint .univ X)
  (hnon: ∀ α, Nonempty (X α)) :
  ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
  sorry

/-- Вправа 8.4.2. Сенс цього завдання — встановити цей результат прямо з `exists_set_singleton_intersect`,
уникаючи попередніх результатів, що більш явно покладалися на аксіому вибору. -/
theorem axiom_of_choice_from_exists_set_singleton_intersect {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by
  sorry

/-- Вправа 8.4.3 -/
theorem Function.Injective.inv_surjective {A B:Type} {g: B → A} (hg: Function.Surjective g) :
  ∃ f : A → B, Function.Injective f ∧ Function.RightInverse f g := by
  sorry

/-- Вправа 8.4.3. Сенс цього завдання — встановити цей результат прямо з `Function.Injective.inv_surjective`,
уникаючи попередніх результатів, що більш явно покладалися на аксіому вибору. -/
theorem axiom_of_choice_from_function_injective_inv_surjective {I: Type} {X: I → Type} (h : ∀ i, Nonempty (X i)) :
  Nonempty (∀ i, X i) := by
  sorry

end Chapter8
