/-
Copyright (c) 2026 Brooke Gill and Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brooke Gill and Chi-Yun Hsu
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Automata.DA.Basic
public import Mathlib.Computability.Language
public import Mathlib.Computability.RegularExpressions

/-!
# Kleene's Algorithm
-/

@[expose] public section

namespace Cslib.Language

open scoped FLTS

variable {Symbol : Type*}

section PathSupp

variable {State : Type*}

/-- PathSupp s xs is the set of states that can be reached from state s by reading the string xs,
not including the starting state and the ending state. -/
def PathSupp (flts : FLTS State Symbol) : State → List Symbol → Set State
  | _, [] | _, [_] => ∅
  | s, a :: x => {flts.tr s a} ∪ PathSupp flts (flts.tr s a) x

theorem pathSupp_empty_iff_empty_or_char {flts : FLTS State Symbol} {s : State} {xs : List Symbol} :
    PathSupp flts s xs = ∅ ↔ xs = [] ∨ (∃ a : Symbol, xs = [a]) := by
  match xs with
  | [] | [_] => grind [PathSupp]
  | x :: y :: ys =>
    have : flts.tr s x ∈ PathSupp flts s (x :: y :: ys) := by grind [PathSupp]
    grind

theorem pathSupp_head {flts : FLTS State Symbol} {s : State} {a : Symbol} {xs : List Symbol}
    (hxs : xs ≠ []) : PathSupp flts s (a :: xs) =
    {flts.tr s a} ∪ PathSupp flts (flts.tr s a) xs := by
  grind [PathSupp]

theorem pathSupp_append {flts : FLTS State Symbol} {s : State} {xs ys : List Symbol}
    (hxs : xs ≠ [] ∧ ys ≠ []) : PathSupp flts s (xs ++ ys) =
    {flts.mtr s xs} ∪ PathSupp flts s xs ∪ PathSupp flts (flts.mtr s xs) ys := by
  induction xs generalizing s with
  | nil => grind [PathSupp]
  | cons a xs ih =>
  rw [List.cons_append, pathSupp_head (by simp [hxs.2])]
  by_cases hx : xs = []
  · grind [PathSupp]
  · grind [pathSupp_head hx]

end PathSupp

open Automata Acceptor

/-- A Bounded Path (`BddPath`) has states `Fin n` and accepts strings (lists of symbols)
starting with state `start` and ending with state `finish`
with the intermediate states less than `bound`. -/
structure BddPath (n : ℕ) (Symbol : Type*) extends FLTS (Fin n) Symbol where
  start : Fin n
  finish : Fin n
  bound : ℕ

instance {n : ℕ} : Acceptor (BddPath n Symbol) Symbol where
  Accepts (a : BddPath n Symbol) (xs : List Symbol) :=
    a.mtr a.start xs = a.finish ∧ (∀ i ∈ PathSupp a.toFLTS a.start xs, i < a.bound)

theorem language_bddpath_head_iff {n k : ℕ} {flts : FLTS (Fin n) Symbol} {i j : Fin n}
   {a : Symbol} {xs : List Symbol} :
    a :: xs ∈ language (BddPath.mk flts i j k) ↔
    xs ∈ language (BddPath.mk flts (flts.tr i a) j k) ∧ (flts.tr i a < k ∨ xs = []) := by
  simp only [mem_language, Accepts]
  by_cases hxs : xs = []
  · grind [PathSupp]
  grind [pathSupp_head hxs]

theorem language_bddpath_eq_dfa {n k : ℕ} (flts : FLTS (Fin n) Symbol) (i j : Fin n) (hk : n ≤ k) :
    language (BddPath.mk flts i j k) = language (DA.FinAcc.mk {tr := flts.tr, start := i} {j}) := by
  ext xs
  simp only [mem_language, Accepts]
  grind

open List

section splitLast

/-- The function `splitLastCompl` sends a string to its longest prefix ending at state `t`.
If the string ends at state `t`, then `splitLastCompl` returns the original string.
If the string never passes through state `t` (starting state can be `t`),
then `splitLastCompl` returns the empty string. -/
def splitLastCompl {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) : List Symbol → List Symbol
  | [] => []
  | a :: x => if (splitLastCompl flts (flts.tr s a) t x = []) ∧ flts.tr s a ≠ t then []
  else a :: splitLastCompl flts (flts.tr s a) t x

theorem isPrefix_splitLastCompl {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
    (xs : List Symbol) : IsPrefix (splitLastCompl flts s t xs) xs := by
  induction xs generalizing s with
  | nil => simp [splitLastCompl]
  | cons a xs ih => grind [splitLastCompl]

/-- The function `splitLast` sends a string to its shortest suffix starting at state `t`.
If the string ends at state `t`, then `splitLast` returns the empty string.
If the string never passes through state `t` (starting state can be `t`),
then `splitLast` returns the original string. -/
noncomputable def splitLast {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
    (xs : List Symbol) : List Symbol := (isPrefix_splitLastCompl flts s t xs).choose

theorem splitLast_append {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) (xs : List Symbol) :
    splitLastCompl flts s t xs ++ splitLast flts s t xs = xs := by
  grind [splitLastCompl, splitLast]

theorem splitLast_head {n : ℕ} {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    {a : Symbol} : splitLast flts i k (a :: xs) =
    (if splitLastCompl flts (flts.tr i a) k xs = [] ∧ flts.tr i a ≠ k then a :: xs
    else splitLast flts (flts.tr i a) k xs) := by grind [splitLast, splitLastCompl]

-- def splitLast' [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) :
--     List Symbol → List Symbol
--   | [] => []
--   | a :: x => if (splitLast' flts (flts.tr s a) t x = x) ∧ flts.tr s a ≠ t then a :: x
--   else splitLast' flts (flts.tr s a) t x

-- theorem isSuffix_splitLast' [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
--     (xs : List Symbol) : IsSuffix (splitLast' flts s t xs) xs := by
--   induction xs generalizing s with
--   | nil => simp [splitLast']
--   | cons a xs ih => grind [splitLast']

-- theorem splitLast_append' [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
--     (xs : List Symbol) : splitLastCompl flts s t xs ++ splitLast' flts s t xs = xs := by
--   induction xs generalizing s with
--   | nil => grind [splitLast', splitLastCompl]
--   | cons a xs ih =>
--   simp only [splitLast', splitLastCompl]
--   split_ifs with h h' h'
--   · simp
--   · grind [ih (s := flts.tr s a)]
--   · have := h'.1 ▸ ih (s := flts.tr s a)
--     simp at this
--     grind
--   · simpa using ih (s := flts.tr s a)

-- theorem splitLast_eq' [DecidableEq Symbol] {n : ℕ} {flts : FLTS (Fin n) Symbol} {s t : Fin n}
--     {xs : List Symbol} (h : t ∉ PathSupp flts s xs) (h' : t = flts.mtr s xs) :
--     splitLast' flts s t xs = [] := by
--   induction xs generalizing s with
--   | nil => grind [splitLast', PathSupp]
--   | cons a xs ih =>
--   by_cases hxs : xs = []
--   · grind [splitLast', PathSupp]
--   rw [pathSupp_head hxs, Set.mem_union, Set.mem_singleton_iff] at h
--   grind [splitLast', (isSuffix_splitLast' flts (flts.tr s a) t xs).length_le]

theorem splitLastCompl_eq {n : ℕ} {flts : FLTS (Fin n) Symbol} {s t : Fin n}
    {xs : List Symbol} (h : t ∉ PathSupp flts s xs) (h' : t = flts.mtr s xs) :
    splitLastCompl flts s t xs = xs := by
  induction xs generalizing s with
  | nil => grind [splitLastCompl, PathSupp]
  | cons a xs ih =>
  by_cases hxs : xs = []
  · grind [splitLastCompl, PathSupp]
  rw [pathSupp_head hxs, Set.mem_union, Set.mem_singleton_iff] at h
  grind [splitLastCompl, (isPrefix_splitLastCompl flts (flts.tr s a) t xs).length_le]
  -- classical
  -- simpa [splitLast_eq h h'] using splitLast_append flts s t xs

theorem splitLast_eq {n : ℕ} {flts : FLTS (Fin n) Symbol}
    {s t : Fin n} {xs : List Symbol} (h : t ∉ PathSupp flts s xs) (h' : t = flts.mtr s xs) :
    splitLast flts s t xs = [] := by
  simpa [splitLastCompl_eq h h'] using splitLast_append flts s t xs

-- theorem splitLast_neq_iff_mem_PathSupp' [DecidableEq Symbol] {n : ℕ} {flts : FLTS (Fin n) Symbol}
--    {s t : Fin n} {xs : List Symbol} (hxs : xs ≠ []) :
--     ¬(splitLast' flts s t xs = xs) ↔ t ∈ PathSupp flts s xs ∨ t = flts.mtr s xs := by
--   induction xs generalizing s with
--   | nil => contradiction
--   | cons a xs ih =>
--   by_cases hxs' : xs = []
--   · grind [splitLast', PathSupp]
--   rw [pathSupp_head hxs', Set.mem_union, Set.mem_singleton_iff]
--   grind [splitLast', (isSuffix_splitLast' flts (flts.tr s a) t xs).length_le]

theorem splitLastCompl_nonempty_iff_mem_PathSupp {n : ℕ} {flts : FLTS (Fin n) Symbol}
   {s t : Fin n} {xs : List Symbol} (hxs : xs ≠ []) :
    ¬(splitLastCompl flts s t xs = []) ↔ t ∈ PathSupp flts s xs ∨ t = flts.mtr s xs := by
  induction xs generalizing s with
  | nil => contradiction
  | cons a xs ih =>
  by_cases hxs' : xs = []
  · grind [splitLastCompl, PathSupp]
  rw [pathSupp_head hxs', Set.mem_union, Set.mem_singleton_iff]
  grind [splitLastCompl, (isPrefix_splitLastCompl flts (flts.tr s a) t xs).length_le]
  -- classical
  -- rw [← splitLast_neq_iff_mem_PathSupp hxs, not_iff_not]
  -- nth_rw 3 [← splitLast_append flts s t xs]
  -- simp

theorem splitLast_neq_iff_mem_PathSupp {n : ℕ} {flts : FLTS (Fin n) Symbol}
   {s t : Fin n} {xs : List Symbol} (hxs : xs ≠ []) :
    ¬(splitLast flts s t xs = xs) ↔ t ∈ PathSupp flts s xs ∨ t = flts.mtr s xs := by
  rw [← splitLastCompl_nonempty_iff_mem_PathSupp hxs, not_iff_not]
  nth_rw 2 [← splitLast_append flts s t xs]
  simp

theorem splitLastCompl_aux {n : ℕ} {flts : FLTS (Fin n) Symbol}
    {i j k : Fin n} {xs : List Symbol} {a : Symbol}
    (h : a :: xs ∈ language (BddPath.mk flts i j (k.val + 1)))
    (h' : a :: xs ∉ language (BddPath.mk flts i j k.val))
    (hc : splitLastCompl flts (flts.tr i a) k xs = [] ∧ flts.tr i a ≠ k) : False := by
  simp only [mem_language, Accepts, Order.lt_add_one_iff, Fin.val_fin_le, Fin.val_fin_lt, not_and,
      not_forall, not_lt, ne_eq] at *
  simp only [h, forall_const] at h'
  obtain ⟨x, ⟨hx, hxk⟩⟩ := h'
  have eq := le_antisymm (h.2 x hx) hxk
  rw [eq] at hx
  by_cases hxs : xs = []
  · grind [PathSupp]
  rw [pathSupp_head hxs] at hx h
  rcases hx with hx1 | hx2
  · have := hc.2
    simp only [Set.mem_singleton_iff] at hx1
    symm at hx1
    contradiction
  · grind [(splitLastCompl_nonempty_iff_mem_PathSupp hxs).mpr (Or.inl hx2)]

theorem splitLastCompl_mem {n : ℕ} {flts : FLTS (Fin n) Symbol}
    {i j k : Fin n} {xs : List Symbol}
    (h : xs ∈ language (BddPath.mk flts i j (k.val + 1)))
    (h' : xs ∉ language (BddPath.mk flts i j k.val)) :
    splitLastCompl flts i k xs ∈ language (BddPath.mk flts i k (k.val + 1)) := by
  induction xs generalizing i with
  | nil =>
  simp [Accepts, PathSupp] at h h'
  contradiction
  | cons a xs ih =>
  simp only [splitLastCompl]
  split_ifs with hc
  · exfalso; exact splitLastCompl_aux h h' hc
  · rw [not_and_or, not_not] at hc
    -- The last `k` is later than `flts.tr i a` or equal to it.
    by_cases hc1 : ¬splitLastCompl flts (flts.tr i a) k xs = []
    · by_cases hxs : xs = []
      · grind [splitLastCompl]
      have haux := language_bddpath_head_iff.mp h
      simp only [hxs, or_false] at haux
      refine language_bddpath_head_iff.mpr ⟨?_, Or.inl haux.2⟩
      by_cases hk : k ∈ PathSupp flts (flts.tr i a) xs
      · apply ih haux.1
        simp [Accepts]
        grind
      · have eq : k = flts.mtr (flts.tr i a) xs := by
          simpa [hk] using (splitLastCompl_nonempty_iff_mem_PathSupp hxs).mp hc1
        rw [splitLastCompl_eq hk eq]
        grind [h.1]
        -- simpa [← mtr_head_eq, eq, h.1] using haux.1
    · rw [not_not] at hc1
      simpa [hc1, Accepts, PathSupp, FLTS.mtr] using hc

theorem splitLast_mem {n : ℕ} {flts : FLTS (Fin n) Symbol}
    {i j k : Fin n} {xs : List Symbol}
    (h : xs ∈ language (BddPath.mk flts i j (k.val + 1)))
    (h' : xs ∉ language (BddPath.mk flts i j k.val)) :
    splitLast flts i k xs ∈ language (BddPath.mk flts k j k.val) := by
  induction xs generalizing i with
  | nil =>
  simp [Accepts, PathSupp] at h h'
  contradiction
  | cons a xs ih =>
  have h'' := splitLastCompl_mem h h'
  simp only [splitLastCompl] at h''
  rw [splitLast_head]
  split_ifs with hc
  · exfalso; exact splitLastCompl_aux h h' hc
  · rw [not_and_or, not_not] at hc
    -- The last `k` is later than `flts.tr i a` or equal to it.
    by_cases hc1 : ¬splitLastCompl flts (flts.tr i a) k xs = []
    · by_cases hxs : xs = []
      · grind [splitLast]
      -- First hypothesis of `ih` is implied by `h`
      have haux := language_bddpath_head_iff.mp h
      simp only [hxs, or_false] at haux
      -- Assumptions `h` and `h'` combined says that `k ∈ PathSupp flts i (a :: xs)`
      by_cases hk : k ∈ PathSupp flts (flts.tr i a) xs
      · -- `k` appears in PathSupp
        apply ih haux.1
        simp [Accepts]
        grind
      · -- `k` only appears at the end state
        -- `hk` should contradict with `h` and `h'`
        apply (splitLastCompl_nonempty_iff_mem_PathSupp hxs).mp at hc1
        simp_all [Accepts, PathSupp, splitLast_eq]
    · -- The last `k` is equal to `flts.tr i a`
      -- Cannot apply ih
      -- Directly prove the goal from definition
      simp only [mem_language, Accepts] at h ⊢
      by_cases hxs : xs = []
      · grind [splitLast_eq, PathSupp]
      grind [splitLast_append, splitLastCompl_nonempty_iff_mem_PathSupp, pathSupp_head]

-- The original path1
theorem language_bddpath_splitLast {n : ℕ} (flts : FLTS (Fin n) Symbol) (i j k : Fin n) :
    language (BddPath.mk flts i j (k + 1)) = language (BddPath.mk flts i j k) +
    (language (BddPath.mk flts i k (k + 1)) * language (BddPath.mk flts k j k)) := by
  ext xs
  rw [Language.mem_add, Language.mem_mul]
  constructor
  · intro h
    by_cases h' : xs ∈ language (BddPath.mk flts i j k)
    · left; exact h'
    right
    use splitLastCompl flts i k xs, splitLastCompl_mem h h',
    splitLast flts i k xs,  splitLast_mem h h',
    splitLast_append flts _ _ _
  · rintro (h_left | ⟨ys, ⟨⟨hys, hsuppys⟩, ⟨zs, ⟨⟨hzs, hsuppzs⟩, happend⟩⟩⟩⟩)
    · simp only [mem_language, Accepts] at h_left ⊢
      grind
    · refine ⟨by grind, ?_⟩
      by_cases ys = [] ∨ zs = []
      · grind
      grind [pathSupp_append]

end splitLast

section splitFirst

/-- The function `splitFirst` sends a string to its shortest prefix ending at state `t`.
The string is empty if and only if its `splitFirst` is empty.
If the string never passes through state `t` (starting state can be `t`),
then `splitFirst` returns the original string. -/
def splitFirst {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) : List Symbol → List Symbol
  | [] => []
  | a :: x => if flts.tr s a = t then [a] else a :: splitFirst flts (flts.tr s a) t x

lemma isPrefix_splitFirst {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) (xs : List Symbol) :
    IsPrefix (splitFirst flts s t xs) xs := by
  induction xs generalizing s with
  | nil => simp [splitFirst]
  | cons a xs ih => grind [splitFirst]

noncomputable def splitFirstCompl {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
    (xs : List Symbol) : List Symbol := (isPrefix_splitFirst flts s t xs).choose

lemma splitFirst_append {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) (xs : List Symbol) :
    splitFirst flts s t xs ++ splitFirstCompl flts s t xs = xs := by
  grind [splitFirst, splitFirstCompl]

lemma splitFirst_mem {n : ℕ} {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (h : xs ∈ (language (BddPath.mk flts i k (k.val + 1)))) :
    splitFirst flts i k xs ∈ language (BddPath.mk flts i k k.val) := by
  induction xs generalizing i with
  | nil => simpa [Accepts, splitFirst, PathSupp] using h
  | cons a xs ih =>
  simp only [mem_language, Accepts, Order.lt_add_one_iff, splitFirst] at ih h ⊢
  obtain ⟨h1, h2⟩ := h
  split_ifs with ha
  · refine ⟨by grind, ?_⟩
    have : PathSupp flts i [a] = ∅ := by grind [PathSupp]
    simp [this]
  · have : flts.mtr i (a :: splitFirst flts (flts.tr i a) k xs) =
      flts.mtr (flts.tr i a) (splitFirst flts (flts.tr i a) k xs) := by grind
    by_cases hxs : xs = []
    · grind
    rw [pathSupp_head hxs] at h2
    by_cases hPath : splitFirst flts (flts.tr i a) k xs = []
    · grind
    rw [this, pathSupp_head hPath]
    grind

lemma splitFirst_mem' {n : ℕ} {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (hxs : xs ≠ []) (h : xs ∈ (language (BddPath.mk flts i k (k.val + 1)))) :
    splitFirst flts i k xs ∈ language (BddPath.mk flts i k k.val) - 1 := by
  rw [Language.mem_sub]
  refine ⟨splitFirst_mem h, ?_⟩
  simp only [Language.mem_one]
  induction xs with
  | nil => contradiction
  | cons a xs ih => grind [splitFirst]

lemma splitFirstCompl_mem {n : ℕ} {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (h : xs ∈ (language (BddPath.mk flts i k (k.val + 1)))) :
    splitFirstCompl flts i k xs ∈ language (BddPath.mk flts k k (k.val + 1)) := by
  have h' := splitFirst_mem h
  simp only [mem_language, Accepts] at h h' ⊢
  rw [← splitFirst_append flts i k xs] at h
  refine ⟨by grind, ?_⟩
  by_cases splitFirst flts i k xs = [] ∨ splitFirstCompl flts i k xs = []
  · grind [PathSupp]
  grind [pathSupp_append]

-- The original path2
lemma language_bddpath_splitFirst {n : ℕ} (flts : FLTS (Fin n) Symbol) (i k : Fin n) :
    language (BddPath.mk flts i k (k + 1)) =
    language (BddPath.mk flts i k k) * language (BddPath.mk flts k k (k + 1)) := by
  ext xs
  rw [Language.mem_mul]
  constructor
  · intro h
    use splitFirst flts i k xs, splitFirst_mem h,
      splitFirstCompl flts i k xs, splitFirstCompl_mem h,
      splitFirst_append flts _ _ _
  · intro ⟨ys, ⟨⟨hys, hsuppys⟩, ⟨zs, ⟨⟨hzs, hsuppzs⟩, happend⟩⟩⟩⟩
    refine ⟨by grind, ?_⟩
    by_cases ys = [] ∨ zs = []
    · grind
    grind [pathSupp_append]

end splitFirst

section kstar

open Computability

lemma kstar_eq {α : Type*} (l : Language α) : l∗ = (l - 1)∗ := by
  ext x
  rw [Language.kstar_def_nonempty, Language.mem_kstar]
  exact ⟨fun ⟨S, hx, h⟩ => ⟨S, ⟨hx, fun y ys => h y ys⟩⟩,
    fun ⟨S, ⟨hx, h⟩⟩ => ⟨S, hx, fun y ys => h y ys⟩⟩

lemma language_bddpath_kstar {n : ℕ} (flts : FLTS (Fin n) Symbol) (k : Fin n) :
    language (BddPath.mk flts k k (k + 1)) = (language (BddPath.mk flts k k k))∗ := by
  rw [← mul_one (language (BddPath.mk flts k k ↑k))∗]
  rw [kstar_eq]
  refine (Language.self_eq_mul_add_iff (by simp [Language.mem_sub])).mp ?_
  -- mimic the proof of path2
  ext xs
  simp only [Language.mem_add, Language.mem_mul, Language.mem_sub]
  constructor
  · intro h
    by_cases h' : xs ∈ (1 : Language Symbol)
    · grind
    left
    use splitFirst flts k k xs, splitFirst_mem' h' h,
      splitFirstCompl flts k k xs, splitFirstCompl_mem h,
      splitFirst_append flts _ _ _
  · rintro (⟨ys, ⟨⟨⟨hys, hsuppys⟩, hysnotempty⟩, ⟨zs, ⟨⟨hzs, hsuppzs⟩, happend⟩⟩⟩⟩ | hempty)
    · refine ⟨by grind, ?_⟩
      by_cases zs = []
      · grind
      rw [Language.mem_one] at hysnotempty
      grind [pathSupp_append]
    · rw [Language.mem_one] at hempty
      simp only [mem_language, Accepts]
      grind [PathSupp]

end kstar

open Computability
/-
Regex i j k is the regex for the path from state i to state j passing through states < k.
When k = 0, i = j, the regex is ε union all characters from state i to state i.
When k = 0, i ≠ j, the regex is all characters from state i to state j.
For k + 1, the regex is the union of Regex i j k and
(Regex i k k) (Regex k k k)∗ (Regex k j k).
-/
noncomputable def Regex [Fintype Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol)
    (i j : Fin n) : ℕ → RegularExpression Symbol
  | 0 =>
    let chars := (Finset.univ.filter
      (fun x : Symbol ↦ flts.tr i x = j)).toList.map RegularExpression.char
    if i = j then 1 + chars.sum else chars.sum
  | k + 1 =>
    if h : n ≤ k then Regex flts i j k
    else
      let kFin : Fin n := ⟨k, by omega⟩
      Regex flts i j k + Regex flts i kFin k * (Regex flts kFin kFin k).star * Regex flts kFin j k

open RegularExpression

variable {α : Type*}

theorem mem_sum_matches'_iff (L : List (RegularExpression α)) (x : List α) :
    x ∈ (L.sum).matches' ↔ ∃ P ∈ L, x ∈ P.matches' := by
  induction L with
  | nil => simp
  | cons head tail ih =>
  simp only [sum_cons, matches', Language.mem_add, ih, mem_cons, exists_eq_or_imp]

theorem language_bddpath_eq_regex [Fintype Symbol] {n k : ℕ} {i j : Fin n}
    {flts : FLTS (Fin n) Symbol} :
    language (BddPath.mk flts i j k) = (Regex flts i j k).matches' := by
  induction k generalizing i j with
  | zero =>
    ext xs
    simp only [mem_language, Accepts, not_lt_zero, Regex]
    rw [(by grind : (∀ i_1 ∈ PathSupp flts i xs, False) ↔ PathSupp flts i xs = ∅)]
    split_ifs with heq
    · -- The case of i = j, k = 0
      simp only [matches', Language.mem_add, mem_sum_matches'_iff, pathSupp_empty_iff_empty_or_char]
      aesop
    · -- The case of i ≠ j, k = 0
      rw [mem_sum_matches'_iff, pathSupp_empty_iff_empty_or_char]
      aesop
  | succ k ih =>
    simp only [Regex]
    split_ifs with hk
    · rw [← ih, language_bddpath_eq_dfa flts i j hk, language_bddpath_eq_dfa flts i j (by omega)]
    rw [language_bddpath_splitLast (k := ⟨k, by omega⟩), language_bddpath_splitFirst,
      language_bddpath_kstar]
    grind [matches'_add, matches'_mul, matches'_star]

end Cslib.Language
