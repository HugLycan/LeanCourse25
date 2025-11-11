import Mathlib.Analysis.Complex.Exponential

import Mathlib
open Real Function Set Nat

/-

* Hand in the solutions to the exercises below. Deadline: **Monday**, 10.11.2025 at **19:00**.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

section calculations

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  calc
    _ = (t - 2) ^ 2 - 21 + t := by ring
    _ ≥ 8 ^ 2 - 21 + 10 := by gcongr; linarith
    _ ≥ 5 := by linarith
  done


/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
  calc
    _ = (t ^ 2) ^ 2 + 3 * t ^ 2 * t - 3 * t ^ 2 - 2 * t - 2 := by ring
    _ = 4 ^ 2 + 3 * 4 * t - 3 * 4 - 2 * t - 2 := by rw [eq_of_sub_eq_zero ht]
    _ = 10 * t + 2 := by ring
  done

end calculations

section Min
variable (a b c d : ℝ)

/- The following theorems characterize `min`.
Let's use this characterization of it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by
  have (x y : ℝ) : min x y ≤ min y x := by
    apply le_min
    apply min_le_right
    apply min_le_left
  exact antisymm (this a b) (this b a)
  done

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by
  apply le_antisymm <;> apply le_min <;> try apply le_min
  . apply min_le_left
  . calc
      _ ≤ min b c := by apply min_le_right
      _ ≤ b := by apply min_le_left
  . calc
      _ ≤ min b c := by apply min_le_right
      _ ≤ c := by apply min_le_right
  . calc
      _ ≤ min a b := by apply min_le_left
      _ ≤ a := by apply min_le_left
  . calc
      _ ≤ min a b := by apply min_le_left
      _ ≤ b := by apply min_le_right
  . apply min_le_right
  done

-- Prove the following exercise. You can use mathlib tactics now.
lemma exercise_min : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  ac_rfl


end Min

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by
  constructor
  . intro hs a
    rw [hs]
    simp only [mem_univ]
  . intro hs
    ext a
    constructor
    . simp only [mem_univ, implies_true]
    . exact fun _ => hs a
  done


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
example (p : Prop) : p ∨ ¬ p := by
  by_contra h
  push_neg at h
  rcases h
  contradiction
  done

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (132 + 32 * 3, (x + y) ^ 2) = (228, x ^ 2 + 2 * x * y + y ^ 2) := by
  ext <;> simp only
  ring
  done

/- Prove a version of the axiom of choice Lean's `Classical.choose`.

Note: this might be a bit harder; you will probably find `Classical.choose` and
`Classical.choose_spec` useful. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by
  use fun i => Classical.choose <| hC i
  exact fun i => Classical.choose_spec <| hC i
  done

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by
  simp only [image_subset_iff, subset_refl]
  done

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by
  intro y hy
  obtain ⟨x, hf⟩ := h y
  use x
  rw [←hf] at hy
  constructor
  assumption'
  done

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro b bh
  obtain ⟨⟨a, a_in_s, fa_eq_b⟩, a', a'_in_t, fa'_eq_b⟩ := bh
  simp only [mem_image, mem_inter_iff]
  specialize h <| fa_eq_b ▸ fa'_eq_b
  rw [h] at a'_in_t
  use a
  done

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by
  ext y
  simp only [image_univ, mem_range, ge_iff_le, mem_setOf_eq]
  constructor
  . intro ⟨x, hx⟩
    rw [←hx]
    positivity
  . intro hy
    use sqrt y
    exact Real.sq_sqrt hy
  done

end Set

section casts

/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by
  norm_cast at h
  exact h.symm
  done

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by
  norm_cast at h ⊢
  linarith
  done

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by
  sorry
  done

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by
  sorry
  done

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by
  sorry
  done

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by
  sorry
  done

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by
  sorry
  done

end casts

/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i ∈ Finset.range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by
  sorry
  done

example (n : ℕ) : ∑ i ∈ Finset.range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by
  sorry
  done

example (n : ℕ) : 6 * ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  sorry
  done

/-! # Exercises to hand-in. -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext x
  simp only [mem_inter_iff, mem_image, mem_preimage]
  constructor
  . intro ⟨⟨y, y_in_s, fy_eq_x⟩, x_in_t⟩
    use y
    rw [fy_eq_x]
    exact ⟨⟨y_in_s, x_in_t⟩, rfl⟩
  . intro ⟨y, ⟨⟨y_in_s, fy_in_t⟩, fy_eq_x⟩⟩
    rw [←fy_eq_x]
    exact ⟨⟨y, y_in_s, rfl⟩, fy_in_t⟩
  done

/- Prove this without using lemmas from Mathlib. -/
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  simp
  constructor
  . intro ⟨j, ⟨⟨i, j_in_Ai⟩, fj_eq_x⟩⟩
    use i, j
  . intro ⟨i, j, j_in_Ai, fj_eq_x⟩
    use j
    constructor
    use i
    assumption
  done

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  sorry
  done

section

-- In class, we saw that Lean does not accept definitions like this:
-- def wrong : ℕ → ℕ
--  | n => 1 + wrong (n + 1)

-- In this case, you can actually derive a contradiction from a function with this property.
-- Do so in the following exercise.
-- (If you'd like a mathematical hint, scroll to the bottom of this file.)
example (f : ℕ → ℕ) (h : ∀ n : ℕ, f n = 1 + f (n + 1)) : False := by
  have (n m : ℕ) : f n > m := by
    induction m generalizing n with
    | zero => simp only [h n, gt_iff_lt, add_pos_iff, zero_lt_one, true_or]
    | succ m ih =>
      rw [h n]
      linarith [ih (n + 1)]
  linarith [this 0 (f 0)]
  done

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ 3) = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 := by
  induction n with
  | zero => simp only [zero_add, Finset.range_one, sum_singleton, CharP.cast_eq_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  | succ n ih => sorry
  done

end

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  unfold SurjectiveFunction at hf ⊢
  constructor
  intro hgf y
  obtain ⟨x, hfx⟩ := hf y
  obtain ⟨x', hgfx⟩ := hgf y
  sorry
  done

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  sorry
  done

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  unfold Surjective
  intro h
  obtain ⟨a, ha⟩ := h {x | x ∉ f x}
  simp only [Set.ext_iff, mem_setOf_eq] at ha
  specialize ha a
  exact ha.2
  done

end Surjectivity

-- Hint for the exercise `contradictory_definition`:
-- use the hypothesis to study `f 0`: can you relate it to `f 1`, `f 2`, etc.?
-- Perhaps you can formulate a hypothesis and prove it by induction.
