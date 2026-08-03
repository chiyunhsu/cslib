/-
Copyright (c) 2026 Brooke Gill and Chi-Yun Hsu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brooke Gill and Chi-Yun Hsu
-/

module

public import Mathlib.Computability.RegularExpressions

open RegularExpression

variable {α : Type*}

theorem mem_zero_matches'_iff (x : List α) :
    x ∈ (0 : RegularExpression α).matches' ↔ False := by
  classical
  rw [← rmatch_iff_matches']
  sorry

theorem mem_one_matches'_iff (x : List α) :
    x ∈ (1 : RegularExpression α).matches' ↔ x = [] := by
  classical
  rw [← rmatch_iff_matches', one_rmatch_iff]

theorem mem_char_matches'_iff (a : α) (x : List α) :
    x ∈ (char a).matches' ↔ x = [a] := by sorry

theorem mem_star_matches'_iff (P : RegularExpression α) (x : List α) :
    x ∈ (star P).matches' ↔ ∃ S : List (List α), x
          = S.flatten ∧ ∀ t ∈ S, t ≠ [] ∧ t ∈ P.matches' := by sorry

theorem mem_sum_matches'_iff (P Q : RegularExpression α) (x : List α) :
    x ∈ (P + Q).matches' ↔ x ∈ P.matches' ∨ x ∈ Q.matches' := by
  classical
  repeat rw [← rmatch_iff_matches']
  rw [add_rmatch_iff]

theorem mem_prod_matches'_iff (P Q : RegularExpression α) (x : List α) :
    x ∈ (P * Q).matches' ↔ ∃ y z, x = y ++ z ∧ y ∈ P.matches' ∧ z ∈ Q.matches' := by sorry
