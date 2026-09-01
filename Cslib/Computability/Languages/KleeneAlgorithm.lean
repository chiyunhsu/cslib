/-
Copyright (c) 2026 Brooke Gill and Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brooke Gill and Chi-Yun Hsu
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Automata.DA.Basic
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

section splitLast

open List

-- variable [DecidableEq Symbol]

/-- The function `splitLast` sends a string to its shortest suffix starting at state `t`.
If the string ends at state `t`, then `splitLast` returns the empty string.
If the string never passes through state `t` (starting state can be `t`),
then `splitLast` returns the original string. -/
def splitLast [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) :
    List Symbol → List Symbol
  | [] => []
  | a :: x => if (splitLast flts (flts.tr s a) t x = x) ∧ flts.tr s a ≠ t then a :: x
  else splitLast flts (flts.tr s a) t x

theorem isSuffix_splitLast [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
    (xs : List Symbol) : IsSuffix (splitLast flts s t xs) xs := by
  induction xs generalizing s with
  | nil => simp [splitLast]
  | cons a xs ih => grind [splitLast]

def splitLastCompl {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) : List Symbol → List Symbol
  | [] => []
  | a :: x => if (splitLastCompl flts (flts.tr s a) t x = []) ∧ flts.tr s a ≠ t then []
  else a :: splitLastCompl flts (flts.tr s a) t x

theorem splitLast_append [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
    (xs : List Symbol) : splitLastCompl flts s t xs ++ splitLast flts s t xs = xs := by
  induction xs generalizing s with
  | nil => grind [splitLast, splitLastCompl]
  | cons a xs ih =>
  simp only [splitLast, splitLastCompl]
  split_ifs with h h' h'
  · simp
  · grind [ih (s := flts.tr s a)]
  · have := h'.1 ▸ ih (s := flts.tr s a)
    simp at this
    grind
  · simpa using ih (s := flts.tr s a)

theorem splitLast_eq [DecidableEq Symbol] {n : ℕ} {flts : FLTS (Fin n) Symbol} {s t : Fin n}
    {xs : List Symbol} (h : t ∉ PathSupp flts s xs) (h' : t = flts.mtr s xs) :
    splitLast flts s t xs = [] := by
  induction xs generalizing s with
  | nil => grind [splitLast, PathSupp]
  | cons a xs ih =>
  by_cases hxs : xs = []
  · grind [splitLast, PathSupp]
  rw [pathSupp_head hxs, Set.mem_union, Set.mem_singleton_iff] at h
  grind [splitLast, (isSuffix_splitLast flts (flts.tr s a) t xs).length_le]

theorem splitLastCompl_eq {n : ℕ} {flts : FLTS (Fin n) Symbol} {s t : Fin n}
    {xs : List Symbol} (h : t ∉ PathSupp flts s xs) (h' : t = flts.mtr s xs) :
    splitLastCompl flts s t xs = xs := by
  classical
  simpa [splitLast_eq h h'] using splitLast_append flts s t xs

theorem splitLast_neq_iff_mem_PathSupp [DecidableEq Symbol] {n : ℕ} {flts : FLTS (Fin n) Symbol}
   {s t : Fin n} {xs : List Symbol} (hxs : xs ≠ []) :
    ¬(splitLast flts s t xs = xs) ↔ t ∈ PathSupp flts s xs ∨ t = flts.mtr s xs := by
  induction xs generalizing s with
  | nil => contradiction
  | cons a xs ih =>
  by_cases hxs' : xs = []
  · grind [splitLast, PathSupp]
  rw [pathSupp_head hxs', Set.mem_union, Set.mem_singleton_iff]
  grind [splitLast, (isSuffix_splitLast flts (flts.tr s a) t xs).length_le]

theorem splitLastCompl_nonempty_iff_mem_PathSupp {n : ℕ} {flts : FLTS (Fin n) Symbol}
   {s t : Fin n} {xs : List Symbol} (hxs : xs ≠ []) :
    ¬(splitLastCompl flts s t xs = []) ↔ t ∈ PathSupp flts s xs ∨ t = flts.mtr s xs := by
  classical
  rw [← splitLast_neq_iff_mem_PathSupp hxs, not_iff_not]
  nth_rw 3 [← splitLast_append flts s t xs]
  simp

end splitLast

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

end Cslib.Language
