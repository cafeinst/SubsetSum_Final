theory SubsetSum_Final
  imports
    SubsetSum_DecisionTree
    SubsetSum_DTM_Bridge
    SubsetSum_DTM_vs_DT
begin

text \<open>Top-level packaging of the conditional separation.\<close>

context Coverage_TM
begin

(* If you want a single-number pivot instead of a free kk, fix it here, e.g.: *)
definition kk0 :: nat where "kk0 \<equiv> 0"  (* or floor (n/2) if you encoded that *)

(* Ready-made lower bound you already proved (just a friendly name): *)
lemma steps_sqrt_lower_bound:
  assumes "n = length as" "kk \<le> n" "distinct_subset_sums as"
  shows   "real (steps M (enc as s kk)) \<ge> 2 * sqrt ((2::real) ^ n)"
  using steps_ge_two_sqrt_pow2[OF assms] .

(* The “no poly bound on distinct family” theorem you finished: *)
theorem no_polytime_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
            \<forall>as s. distinct_subset_sums as \<longrightarrow>
              steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>)"
  by (rule no_polytime_in_n_on_distinct_family)

end