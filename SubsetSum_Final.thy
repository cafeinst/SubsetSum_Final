theory SubsetSum_Final
  imports
    SubsetSum_DecisionTree
    SubsetSum_DTM_Bridge
    SubsetSum_DTM_Bridge2
    SubsetSum_DTM_vs_DT
begin

text ‹Top-level packaging of the conditional separation.›

context Coverage_TM
begin

(* If you want a single-number pivot instead of a free kk, fix it here, e.g.: *)
definition kk0 :: nat where "kk0 ≡ 0"  (* or floor (n/2) if you encoded that *)

(* Ready-made lower bound you already proved (just a friendly name): *)
lemma steps_sqrt_lower_bound:
  assumes "n = length as" "kk ≤ n" "distinct_subset_sums as"
  shows   "real (steps M (enc as s kk)) ≥ 2 * sqrt ((2::real) ^ n)"
  using steps_ge_two_sqrt_pow2[OF assms] .

(* The “no poly bound on distinct family” theorem you finished: *)
theorem no_polytime_on_distinct_family:
  shows "¬ (∃(c::real)>0. ∃(d::nat).
            ∀as s. distinct_subset_sums as ⟶
              steps M (enc as s kk) ≤ nat ⌈ c * real (length as) ^ d ⌉)"
  by (rule no_polytime_in_n_on_distinct_family)

end
