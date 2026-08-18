/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.DA.Congr
public import Cslib.Computability.Automata.DA.Prod
public import Cslib.Computability.Automata.DA.ToNA
public import Cslib.Computability.Automata.NA.Concat
public import Cslib.Computability.Automata.NA.Loop
public import Cslib.Computability.Automata.NA.ToDA
public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Mathlib.Computability.DFA
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Set.Card

public import Mathlib.Computability.NFA
public import Mathlib.Computability.EpsilonNFA
public import Cslib.Computability.Languages.RegularExpressions

/-!
# Regular languages
-/

@[expose] public section

namespace Cslib.Language

open Set List Prod Automata Acceptor RightCongruence
open scoped Computability FLTS DA NA DA.FinAcc NA.FinAcc

variable {Symbol : Type*}

/-- A characterization of `Language.IsRegular` in terms of `DA`. This is the only theorem in Cslib
in which Mathlib's definition of `Language.IsRegular` is used. -/
theorem IsRegular.iff_dfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ dfa : DA.FinAcc State Symbol, language dfa = l := by
  constructor
  · rintro ⟨State, h_fin, ⟨tr, start, acc⟩, rfl⟩
    let dfa := DA.FinAcc.mk {tr, start} acc
    use State, Fintype.finite h_fin, dfa
    rfl
  · rintro ⟨State, h_fin, ⟨⟨flts, start⟩, acc⟩, rfl⟩
    let dfa := DFA.mk flts.tr start acc
    use State, Fintype.ofFinite State, dfa
    rfl

/-- A characterization of Language.IsRegular in terms of NA. -/
theorem IsRegular.iff_nfa {l : Language Symbol} :
    l.IsRegular ↔ ∃ State : Type, ∃ _ : Finite State,
      ∃ nfa : NA.FinAcc State Symbol, language nfa = l := by
  rw [IsRegular.iff_dfa]; constructor
  · rintro ⟨State, h_fin, ⟨da, acc⟩, rfl⟩
    use State, h_fin, ⟨da.toNA, acc⟩
    grind
  · rintro ⟨State, _, na, rfl⟩
    use Set State, inferInstance, na.toDAFinAcc
    grind


/-- The complementation of a regular language is regular. -/
theorem IsRegular.compl {l : Language Symbol} (h : l.IsRegular) : (lᶜ).IsRegular := by
  rw [IsRegular.iff_dfa] at h ⊢
  obtain ⟨State, _, ⟨da, acc⟩, rfl⟩ := h
  use State, inferInstance, ⟨da, accᶜ⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext
  simp only [language, Accepts]
  rfl

/-- The empty language is regular. -/
@[simp]
theorem IsRegular.zero : (0 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_dfa]
  let flts := FLTS.mk (fun () (_ : Symbol) ↦ ())
  use Unit, inferInstance, ⟨DA.mk flts (), ∅⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext
  simp only [language, Accepts]
  rfl

/-- The language containing only the empty word is regular. -/
@[simp]
theorem IsRegular.one : (1 : Language Symbol).IsRegular := by
  rw [IsRegular.iff_dfa]
  let flts := FLTS.mk (fun (_ : Fin 2) (_ : Symbol) ↦ 1)
  use Fin 2, inferInstance, ⟨DA.mk flts 0, {0}⟩
  ext; constructor
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  · intro h; by_contra h'
    have := dropLast_append_getLast h'
    grind [Accepts]
  · grind [Accepts, Language.mem_one]

/-- The language of all finite words is regular. -/
@[simp]
theorem IsRegular.top : (⊤ : Language Symbol).IsRegular := by
  have : (⊥ᶜ : Language Symbol).IsRegular := IsRegular.compl <| IsRegular.zero
  rwa [← compl_bot]

/-- The intersection of two regular languages is regular. -/
@[simp]
theorem IsRegular.inf {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 ⊓ l2).IsRegular := by
  rw [IsRegular.iff_dfa] at h1 h2 ⊢
  obtain ⟨State1, h_fin1, ⟨da1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨da2, acc2⟩, rfl⟩ := h2
  use State1 × State2, inferInstance, ⟨da1.prod da2, fst ⁻¹' acc1 ∩ snd ⁻¹' acc2⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext; grind [Accepts, Language.mem_inf]

/-- The union of two regular languages is regular. -/
@[simp]
theorem IsRegular.add {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 + l2).IsRegular := by
  rw [IsRegular.iff_dfa] at h1 h2 ⊢
  obtain ⟨State1, h_fin1, ⟨da1, acc1⟩, rfl⟩ := h1
  obtain ⟨State2, h_fin1, ⟨da2, acc2⟩, rfl⟩ := h2
  use State1 × State2, inferInstance, ⟨da1.prod da2, fst ⁻¹' acc1 ∪ snd ⁻¹' acc2⟩
  #adaptation_note
  /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
  ext; grind [Accepts, Language.mem_add]

/-- The intersection of any finite number of regular languages is regular. -/
@[simp]
theorem IsRegular.iInf {I : Type*} [Finite I] {s : Set I} {l : I → Language Symbol}
    (h : ∀ i ∈ s, (l i).IsRegular) : (⨅ i ∈ s, l i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero => simp_all [ncard_eq_zero (s := s)]
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
    rw [iInf_insert]
    grind [IsRegular.inf]

/-- The union of any finite number of regular languages is regular. -/
@[simp]
theorem IsRegular.iSup {I : Type*} [Finite I] {s : Set I} {l : I → Language Symbol}
    (h : ∀ i ∈ s, (l i).IsRegular) : (⨆ i ∈ s, l i).IsRegular := by
  generalize h_n : s.ncard = n
  induction n generalizing s
  case zero =>
    obtain ⟨rfl⟩ := (ncard_eq_zero (s := s)).mp h_n
    simp only [mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot]
    exact IsRegular.zero
  case succ n h_ind =>
    obtain ⟨i, t, h_i, rfl, rfl⟩ := (ncard_eq_succ (s := s)).mp h_n
    rw [iSup_insert]
    apply IsRegular.add <;> grind

open NA.FinAcc Sum in
/-- The concatenation of two regular languages is regular. -/
@[simp]
theorem IsRegular.mul {l1 l2 : Language Symbol}
    (h1 : l1.IsRegular) (h2 : l2.IsRegular) : (l1 * l2).IsRegular := by
  obtain (he | hne) := isEmpty_or_nonempty Symbol
  · obtain (rfl | rfl) := Language.eq_zero_or_one_ofIsEmpty l1 <;>
    obtain (rfl | rfl) := Language.eq_zero_or_one_ofIsEmpty l2 <;> simp
  · have := Classical.inhabited_of_nonempty hne
    rw [IsRegular.iff_nfa] at h1 h2 ⊢
    obtain ⟨State1, h_fin1, nfa1, rfl⟩ := h1
    obtain ⟨State2, h_fin1, nfa2, rfl⟩ := h2
    use Option State1 ⊕ Option State2, inferInstance,
      ⟨finConcat nfa1 nfa2, inr '' (some '' nfa2.accept)⟩
    exact finConcat_language_eq

open NA.FinAcc Sum in
/-- The Kleene star of a regular language is regular. -/
@[simp]
theorem IsRegular.kstar {l : Language Symbol}
    (h : l.IsRegular) : (l∗).IsRegular := by
  obtain (he | hne) := isEmpty_or_nonempty Symbol
  · obtain (rfl | rfl) := Language.eq_zero_or_one_ofIsEmpty l <;> simp
  · have := Classical.inhabited_of_nonempty hne
    by_cases h_l : l = 0
    · simp [h_l]
    · rw [IsRegular.iff_nfa] at h ⊢
      obtain ⟨State, h_fin, nfa, rfl⟩ := h
      use Unit ⊕ Option State, inferInstance, ⟨finLoop nfa, {inl ()}⟩, loop_language_eq h_l

/-- If a right congruence is of finite index, then each of its equivalence classes is regular. -/
@[simp]
theorem IsRegular.congr_fin_index {Symbol : Type}
    [c : RightCongruence Symbol] [Finite (Quotient c.eq)]
    (a : Quotient c.eq) : (eqvCls a).IsRegular := by
  rw [IsRegular.iff_dfa]
  use Quotient c.eq, inferInstance, ⟨c.toDA, {a}⟩
  exact DA.FinAcc.congr_language_eq

/-- The language containing only the one character string `a` is regular. -/
@[simp]
theorem IsRegular.char (a : Symbol) : ({[a]} : Language Symbol).IsRegular := by
  rw [IsRegular.iff_dfa]
  classical
  let flts := FLTS.mk (fun (s : Fin 3) (x : Symbol) ↦ if (s = 0 ∧ x = a) then 1 else 2)
  use Fin 3, inferInstance, ⟨DA.mk flts 0, {1}⟩
  ext xs
  induction xs using List.reverseRec with
  | nil => grind [Accepts, Language.mem_singleton]
  | append_singleton xs x ih =>
    simp only [mem_language, Accepts, Language.mem_singleton, FLTS.mtr_concat_eq] at ih ⊢
    constructor
    · induction xs using List.reverseRec <;> grind
    · simp_all [flts, List.append_eq_cons_iff]

/-- Languages matching regular expressions are regular. -/
theorem IsRegular.regex {r : RegularExpression Symbol} :
    r.matches'.IsRegular := by
  induction r with
  | zero => simp
  | epsilon => simp
  | char a => simp [IsRegular.char a]
  | plus P Q hP hQ => grind [RegularExpression.matches', IsRegular.add]
  | comp P Q hP hQ => grind [RegularExpression.matches', IsRegular.mul]
  | star P hP => grind [RegularExpression.matches', IsRegular.kstar]

/- We use Kleene's Algorithm for DFA to prove a regular language can be expressed as a regex. -/
section RegularExpression

open RegularExpression

-- Ask Chou whether to add reindex lemma for cslib DFA,
-- rather than using reindex lemma for mathlib DFA.
theorem IsRegular.iff_dfa' {l : Language Symbol} :
    l.IsRegular ↔ ∃ (n : ℕ), ∃ dfa : DA.FinAcc (Fin n) Symbol, language dfa = l := by
  rw [IsRegular.iff_dfa]
  constructor
  · rintro ⟨State, h_fin, ⟨⟨flts, start⟩, acc⟩, rfl⟩
    have : Fintype State := Fintype.ofFinite State
    let dfa := DFA.mk flts.tr start acc -- mathlib
    let dfa2 := DFA.reindex (Fintype.equivFin State) dfa -- mathlib on Fin n
    let dfa3 := DA.FinAcc.mk {tr := dfa2.step, start := dfa2.start} dfa2.accept -- cslib on Fin n
    exact ⟨Fintype.card State, dfa3, DFA.accepts_reindex dfa (Fintype.equivFin State)⟩
    -- exact ⟨n, dfa3, DFA.accepts_reindex dfa (Fintype.equivFin State)⟩
    -- exact DFA.accepts_reindex dfa (Fintype.equivFin State)
  · intro ⟨n, dfa, h⟩
    exact ⟨Fin n, inferInstance, dfa, h⟩

/-
regex i j k is the regex for the path from state i to state j passing through states < k.
When k = 0, i = j, the regex is ε union all characters from state i to state i.
When k = 0, i ≠ j, the regex is all characters from state i to state j.
For k + 1, the regex is the union of regex i j k and
regex i k k concat (regex k k k)^* concat regex k j k.
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

#check εNFA.IsPath
-- Mimicing the definition of NFA.Path. Path s xs is the type of
-- inductive Path : State → List Symbol → Type (max u_1 u_2)
--   | nil (s : State) : Path s []
--   | cons (s u : State) (a : Symbol) (x : List Symbol) : Path (flts.tr s a) x → Path s (a :: x)

def PathSupp {State : Type*} (flts : FLTS State Symbol) : State → List Symbol → Set State
  | _, [] | _,  [_] => ∅
  | s, a :: x => {flts.tr s a} ∪ PathSupp flts (flts.tr s a) x

lemma pathSupp_empty_iff_empty_or_char {State : Type*} {flts : FLTS State Symbol} {s : State}
    {xs : List Symbol} : PathSupp flts s xs = ∅ ↔ xs = [] ∨ (∃ a : Symbol, xs = [a]) := by
  match xs with
  | [] | [_] => grind [PathSupp]
  | x :: y :: ys =>
    have h1 : flts.tr s x ∈ PathSupp flts s (x :: y :: ys) := by grind [PathSupp]
    grind

lemma pathSupp_head {State : Type*} {flts : FLTS State Symbol} {s : State}
    {a : Symbol} {xs : List Symbol} (hxs : xs ≠ []) :
    PathSupp flts s (a :: xs) = {flts.tr s a} ∪ PathSupp flts (flts.tr s a) xs := by
  grind [PathSupp]

-- Brooke can work on this lemma (first)
lemma pathSupp_append {State : Type*} {flts : FLTS State Symbol} {s : State}
    {xs ys : List Symbol} (hxs : xs ≠ [] ∧ ys ≠ []) :
    PathSupp flts s (xs ++ ys) =
    {flts.mtr s xs} ∪ PathSupp flts s xs ∪ PathSupp flts (flts.mtr s xs) ys := by
  induction xs generalizing s with
  | nil => grind [PathSupp]
  | cons a xs ih =>
  rw [List.cons_append, pathSupp_head (by simp [hxs.2])]
  by_cases hx : xs = []
  · grind [PathSupp]
  · rw [pathSupp_head hx]
    grind

structure BoundedPath (n : ℕ) (Symbol : Type*) extends FLTS (Fin n) Symbol where
  start : Fin n
  finish : Fin n
  bound : ℕ

instance {n : ℕ} : Acceptor (BoundedPath n Symbol) Symbol where
  Accepts (a : BoundedPath n Symbol) (xs : List Symbol) :=
    a.mtr a.start xs = a.finish ∧ (∀ i ∈ PathSupp a.toFLTS a.start xs, i < a.bound)

-- This is the original aux
lemma language_path_eq_dfa {n : ℕ} (flts : FLTS (Fin n) Symbol) (i j : Fin n) {k : ℕ} (hk : n ≤ k) :
    language (BoundedPath.mk flts i j k) =
    language (DA.FinAcc.mk {tr := flts.tr, start := i} {j}) := by
  ext xs
  simp only [mem_language, Accepts]
  grind

-- The function sending a string to its shortest suffix which starts at state `t`.
def splitLast [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n) :
    List Symbol → List Symbol
  | [] => []
  | a :: x => if (splitLast flts (flts.tr s a) t x = x) ∧ flts.tr s a ≠ t then a :: x
  else splitLast flts (flts.tr s a) t x

lemma isSuffix_splitLast [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
  (xs : List Symbol) : IsSuffix (splitLast flts s t xs) xs := by
  induction xs generalizing s with
  | nil => simp [splitLast]
  | cons a xs ih => grind [splitLast]

noncomputable def splitLastCompl [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol)
    (s t : Fin n) (xs : List Symbol) : List Symbol := (isSuffix_splitLast flts s t xs).choose

lemma splitLast_append [DecidableEq Symbol] {n : ℕ} (flts : FLTS (Fin n) Symbol) (s t : Fin n)
    (xs : List Symbol) :
    splitLastCompl flts s t xs ++ splitLast flts s t xs = xs := by
  grind [splitLast, splitLastCompl]

theorem mtr_head_eq {State Label : Type*} {flts : FLTS State Label} {s : State}
    {x : Label} {xs : List Label} : flts.mtr s (x :: xs) = flts.mtr (flts.tr s x) xs := by grind

set_option pp.structureInstances false -- remove later; this just makes the goals easier to read
lemma splitLast_mem [DecidableEq Symbol] {n : ℕ} {flts : FLTS (Fin n) Symbol}
    {i j k : Fin n} {xs : List Symbol}
    (h : xs ∈ language (BoundedPath.mk flts i j (k.val + 1)))
    (h' : xs ∉ language (BoundedPath.mk flts i j k.val)) :
    splitLast flts i k xs ∈ language (BoundedPath.mk flts k j k.val) := by
  induction xs with
  | nil =>
  simp only [mem_language, Accepts] at h h' ⊢
  grind [PathSupp]
  | cons a xs ih =>
  simp only [splitLast]
  split_ifs with hc
  · -- Harder. Will deduce that i = k
    sorry
  -- Brooke can work on this (third/fourth) Easier
  ·

lemma splitLastCompl_mem [DecidableEq Symbol] {n : ℕ} {flts : FLTS (Fin n) Symbol}
    {i j k : Fin n} {xs : List Symbol}
    (h : xs ∈ language (BoundedPath.mk flts i j (k.val + 1)))
    (h' : xs ∉ language (BoundedPath.mk flts i j k.val)) :
    splitLastCompl flts i k xs ∈ language (BoundedPath.mk flts i k (k.val + 1)) := by sorry

-- Brooke can work on this (third/fourth)
set_option pp.structureInstances false -- delete this once lemmas are resolved
lemma path1 {n : ℕ} (flts : FLTS (Fin n) Symbol) (i j k : Fin n) :
    language (BoundedPath.mk flts i j (k + 1)) = language (BoundedPath.mk flts i j k) +
    (language (BoundedPath.mk flts i k (k + 1)) * language (BoundedPath.mk flts k j k)) := by
  ext xs
  rw [Language.mem_add, Language.mem_mul]
  constructor
  · intro h
    by_cases h' : xs ∈ language (BoundedPath.mk flts i j k)
    · left; exact h'
    right
    sorry
  · sorry

-- The function sending a string to its shortest prefix which ends at state `t`.
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
    (h : xs ∈ (language (BoundedPath.mk flts i k (k.val + 1)))) :
    splitFirst flts i k xs ∈ language (BoundedPath.mk flts i k k.val) := by
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
    (hxs : xs ≠ []) (h : xs ∈ (language (BoundedPath.mk flts i k (k.val + 1)))) :
    splitFirst flts i k xs ∈ language (BoundedPath.mk flts i k k.val) - 1 := by
  rw [Language.mem_sub]
  refine ⟨splitFirst_mem h, ?_⟩
  simp only [Language.mem_one]
  induction xs with
  | nil => contradiction
  | cons a xs ih => grind [splitFirst]

theorem mtr_append_eq {State Label : Type*} {flts : FLTS State Label} {s : State}
    {xs ys : List Label} : flts.mtr s (xs ++ ys) = flts.mtr (flts.mtr s xs) ys := by grind

lemma splitFirstCompl_mem {n : ℕ} {flts : FLTS (Fin n) Symbol} {i k : Fin n} {xs : List Symbol}
    (h : xs ∈ (language (BoundedPath.mk flts i k (k.val + 1)))) :
    splitFirstCompl flts i k xs ∈ language (BoundedPath.mk flts k k (k.val + 1)) := by
  have h' := splitFirst_mem h
  simp only [mem_language, Accepts] at h h' ⊢
  rw [← splitFirst_append flts i k xs, mtr_append_eq] at h
  refine ⟨by simpa [h'.1] using h.1, ?_⟩
  by_cases splitFirst flts i k xs = [] ∨ splitFirstCompl flts i k xs = []
  · grind [PathSupp]
  grind [pathSupp_append]

lemma path2 {n : ℕ} (flts : FLTS (Fin n) Symbol) (i k : Fin n) :
    language (BoundedPath.mk flts i k (k + 1)) =
    language (BoundedPath.mk flts i k k) * language (BoundedPath.mk flts k k (k + 1)) := by
  ext xs
  rw [Language.mem_mul]
  constructor
  · intro h
    use splitFirst flts i k xs, splitFirst_mem h,
      splitFirstCompl flts i k xs, splitFirstCompl_mem h,
      splitFirst_append flts _ _ _
  · simp only [mem_language, Accepts]
    intro ⟨ys, ⟨⟨hys, hsuppys⟩, ⟨zs, ⟨⟨hzs, hsuppzs⟩, happend⟩⟩⟩⟩
    refine ⟨by grind, ?_⟩
    by_cases ys = [] ∨ zs = []
    · grind
    grind [pathSupp_append]

lemma kstar_eq {α : Type*} (l : Language α) : l∗ = (l - 1)∗ := by
  ext x
  rw [Language.kstar_def_nonempty, Language.mem_kstar]
  -- aesop
  exact ⟨fun ⟨S, hx, h⟩ => ⟨S, ⟨hx, fun y ys => h y ys⟩⟩,
    fun ⟨S, ⟨hx, h⟩⟩ => ⟨S, hx, fun y ys => h y ys⟩⟩

lemma path3 {n : ℕ} (flts : FLTS (Fin n) Symbol) (k : Fin n) :
    language (BoundedPath.mk flts k k (k + 1)) = (language (BoundedPath.mk flts k k k))∗ := by
  rw [← mul_one (language (BoundedPath.mk flts k k ↑k))∗]
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

lemma set_aux {α : Type*} (A : Set α) : (∀ (i : α), i ∉ A) ↔ A = ∅ := by
  grind

theorem language_path_eq_regex [Fintype Symbol] {n k : ℕ} {i j : Fin n}
    {flts : FLTS (Fin n) Symbol} :
    language (BoundedPath.mk flts i j k) = matches' (Regex flts i j k) := by
  induction k generalizing i j with
  | zero =>
    ext xs
    simp only [mem_language, Accepts]
    simp only [not_lt_zero, imp_false, Regex]
    split_ifs with heq
    · -- The case of i = j, k = 0
      rw [set_aux, mem_add_matches'_iff, mem_sum_matches'_iff, pathSupp_empty_iff_empty_or_char]
      aesop
    · -- The case of i ≠ j, k = 0
      rw [set_aux, mem_sum_matches'_iff, pathSupp_empty_iff_empty_or_char]
      aesop
  | succ k ih =>
    simp only [Regex]
    split_ifs with hk
    · rw [← ih, language_path_eq_dfa flts i j hk, language_path_eq_dfa flts i j (by omega)]
    rw [path1 (k := ⟨k, by omega⟩), path2, path3]
    simp only [matches'_add, matches'_mul, matches'_star]
    grind

lemma aux {n : ℕ} {s : Fin n} {dfa : DA.FinAcc (Fin n) Symbol} (h : dfa.accept = {s}) :
    language dfa = language (BoundedPath.mk dfa.toFLTS dfa.start s n) := by
  ext xs
  simp only [mem_language, Accepts]
  grind

/- IsRegular.iff_regex in the situation where the there is a single accepting state -/
theorem acc_singleton [Fintype Symbol] {n : ℕ} {s : Fin n} {dfa : DA.FinAcc (Fin n) Symbol}
    (h : dfa.accept = {s}) : language dfa = matches' (Regex dfa.toFLTS dfa.start s n) := by
  rw [aux h]
  exact language_path_eq_regex

/- Modified from Yi-Siong's PR: https://github.com/leanprover-community/mathlib4/pull/35600 -/
theorem matches'_sum (L : List (RegularExpression Symbol)) :
    (L.sum).matches' = (L.map matches').sum := by
  induction L with
  | nil => simp
  | cons b L' ih => simp [ih]

noncomputable instance {n : ℕ} (dfa : DA.FinAcc (Fin n) Symbol) :
    Fintype dfa.accept := Fintype.ofFinite dfa.accept

theorem language_sum {n : ℕ} {dfa : DA.FinAcc (Fin n) Symbol} :
    language dfa = (((dfa.accept.toFinset).sort (· ≤ ·)).map
    (fun s ↦ language {dfa with accept := {s}})).sum := by
  ext xs
  simp only [mem_language]
  have memsum (l : List (Fin n)) : xs ∈ (l.map (fun s ↦ language {dfa with accept := {s}})).sum
  ↔ ∃ s ∈ l, xs ∈ language {dfa with accept := {s}} := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, Language.mem_add, List.mem_cons, ih]
      grind
  simp only [memsum, Finset.mem_sort, Set.mem_toFinset, mem_language]
  grind [Accepts]

theorem IsRegular.iff_regex [Finite Symbol] {l : Language Symbol} :
    l.IsRegular ↔ ∃ r : RegularExpression Symbol, l = matches' r := by
  refine ⟨fun h => ?_, fun ⟨r, hr⟩ => hr ▸ IsRegular.regex⟩
  obtain ⟨n, dfa, rfl⟩ := Cslib.Language.IsRegular.iff_dfa'.mp h
  set acc_List : List (Fin n) := (dfa.accept.toFinset).sort (· ≤ ·) with h_acc
  rw [language_sum]
  let : Fintype Symbol := Fintype.ofFinite Symbol
  let regex :=
    (acc_List.map (fun i => Regex dfa.toFLTS (dfa.start) i n)).sum
  use regex
  simp only [matches'_sum, regex]
  apply congrArg
  rw [← h_acc, List.map_map]
  simp only [map_inj_left, Function.comp_apply]
  suffices h :
    (fun s => language {dfa with accept := {s}}) =
    (fun i => matches' (Regex dfa.toFLTS dfa.start i n)) by exact fun i hi ↦ congrFun h i
  funext s
  exact acc_singleton rfl

end RegularExpression

end Cslib.Language
