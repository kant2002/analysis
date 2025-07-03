import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Аналіз I, Глава 3.6

Я *(пр.перекл. Терренс Тао)* намагався зробити переклад якомога точнішим перефразуванням оригінального тексту.
Коли є вибір між більш ідіоматичним рішенням Lean та більш точним перекладом, я
зазвичай обирав останній. Зокрема, будуть місця, де код Lean можна було б "підбуцнути",
щоб зробити його більш елегантним та ідіоматичним, але я свідомо уникав цього вибору.

Основні конструкції та результати цього розділу:

- Потужність множини
- Скінченні та нескінченні множини
- Зв'язки з Mathlib-івськіми еквівалентами

Після цього розділу ці нотації будуть вважатися застарілими на користь їхніх еквівалентів із Mathlib.

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Визначення 3.6.1 (Рівна потужність) -/
abbrev SetTheory.Set.equal_card (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Приклад 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : equal_card {0,1,2} {3,4,5} := by sorry

/-- Приклад 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : equal_card nat (nat.specify (fun x ↦ Even (x:ℕ))) := by sorry

/-- Твердження 3.6.4 / Вправа 3.6.1 -/
instance SetTheory.Set.inst_setoid : Setoid SetTheory.Set := {
  r := equal_card,
  iseqv := {
    refl := by sorry
    symm := by sorry
    trans := by sorry
  }
}

/-- Визначення 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

/-- Ремарка 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by sorry

/-- Приклад 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by sorry

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
  (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by sorry

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, equal_card]

/-- Лема 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0)
    rw [mem_Fin]
    use 0, (by linarith); rfl
  rw [has_card_iff] at hX
  obtain ⟨ f, hf ⟩ := hX
  sorry
  -- отримай протиріччя із того факту, що `f` є біекцією
  -- з порожньої множини на непорожню множину

/-- Вправа 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by sorry

/-- Лема 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- Цей доказ написано відповідно до структури оригінального тексту, хоча й з деякими додатковими
  -- нотаціями для відстеження деяких перетворень, які є «невидимими» у доказі для людей.  rw [has_card_iff] at hX
  obtain ⟨ f, hf ⟩ := hX
  classical
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun y ↦ ⟨ y.val, by have := y.property; simp [X'] at this; tauto ⟩
  have := (f x).property
  rw [mem_Fin] at this
  obtain ⟨ m₀, hm₀, hm₀f ⟩ := this

  set g : X' → Fin (n-1) := fun y ↦ by
    have hy := y.property
    simp [X'] at hy
    obtain ⟨ hy1, hy2 ⟩ := hy
    have := (f ⟨ y.val, hy1⟩).property
    rw [mem_Fin] at this
    set hmm := this.choose_spec.2
    set hmn := this.choose_spec.1
    set m' := this.choose
    cases m'.decLt m₀ with
    | isTrue hlt =>
      exact Fin_mk _ m' (by omega)
    | isFalse hlt =>
      have : m' ≠ m₀ := by
        contrapose! hy2
        rwa [hy2,←hm₀f,Subtype.val_inj, hf.injective.eq_iff,←Subtype.val_inj] at hmm
      exact Fin_mk _ (m'-1) (by omega)
  have hg : Function.Bijective g := by sorry
  have : equal_card X' (Fin (n-1)) := by use g
  exact this

/-- Твердження 3.6.8 (Унікальність потужності) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  revert X m
  induction' n with n hn
  . intro X m h1 h2
    rw [has_card_zero] at h1
    contrapose! h1
    exact pos_card_nonempty (by omega) h2
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  obtain ⟨ x, hx ⟩ := nonempty_def this
  set x' : X := ⟨ x, hx ⟩
  have : m ≥ 1 := by
    by_contra! hm
    simp at hm
    rw [hm, has_card_zero] at h2
    contradiction
  have hc : (X \ {x'.val}).has_card (n+1-1) := card_erase (by omega) h1 x'
  have hc' : (X \ {x'.val}).has_card (m-1) := card_erase this h2 x'
  simp at hc
  specialize hn hc hc'
  omega

example : ({0,1,2}:Set).has_card 3 := by sorry

example : ({3,4}:Set).has_card 2 := by sorry

example : ¬ ({0,1,2}:Set) ≈ ({3,4}:Set) := by sorry

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Вправа 3.6.3, сформульовано з використанням натуральних чисел Mathlib -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by sorry

/-- Теорема 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- цей доказ написан так, щоб співпадати із структурою орігінального тексту.
  unfold infinite
  by_contra this
  obtain ⟨ n, hn⟩ := this
  simp [has_card] at hn
  replace hn := Setoid.symm hn
  simp [HasEquiv.Equiv, Setoid.r, equal_card] at hn
  obtain ⟨ f, hf ⟩ := hn
  obtain ⟨ M, hM ⟩ := bounded_on_finite f
  replace hf := hf.surjective (M+1:ℕ)
  have :∀ i, f i ≠ (M+1:ℕ) := by
    intro i
    specialize hM i; contrapose! hM
    apply_fun nat_equiv.symm at hM
    simp at hM; simp [hM]
  contrapose! this; exact hf

/-- Для цілей Lean зручно надавати нескінченним множинам ``сміттєву`` потужність як нуль. -/
noncomputable abbrev SetTheory.Set.card (X:Set) : ℕ := by
  classical
  exact if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

/-- Твердження 3.6.14 (a) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by sorry

/-- Твердження 3.6.14 (b) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by sorry

/-- Твердження 3.6.14 (b) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by sorry

/-- Твердження 3.6.14 (c) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by sorry

/-- Твердження 3.6.14 (c) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by sorry

/-- Твердження 3.6.14 (d) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by sorry

/-- Твердження 3.6.14 (d) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by sorry

/-- Твердження 3.6.14 (e) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by sorry

/-- Твердження 3.6.14 (f) / Вправа 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ^ Y).finite ∧ (X ^ Y).card = X.card ^ Y.card := by sorry

/-- Вправа 3.6.2 -/
theorem SetTheory.Set.card_eq_zero {X:Set} (hX: X.finite) :
    X.card = 0 ↔ X = ∅ := by sorry

/-- Вправа 3.6.5 -/
theorem SetTheory.Set.prod_equal_card_prod (A B:Set) :
    equal_card (A ×ˢ B) (B ×ˢ A) := by sorry

/-- Вправа 3.6.6 -/
theorem SetTheory.Set.pow_pow_equal_card_pow_prod (A B C:Set) :
    equal_card ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by sorry

example (a b c:ℕ): (a^b)^c = a^(b*c) := by sorry

example (a b c:ℕ): (a^b) * a^c = a^(b+c) := by sorry

/-- Вправа 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := sorry

/-- Вправа 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by sorry

/-- Вправа 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by  sorry

/-- Вправа 3.6.10 -/
theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by sorry

/-- Зв'язки іх Mathlib-ім `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by sorry

/-- Зв'язки іх Mathlib-ім `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by sorry

/-- Зв'язки іх Mathlib-ім `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by sorry

/-- Зв'язки іх Mathlib-ім `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by sorry

end Chapter3
