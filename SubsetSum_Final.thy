theory SubsetSum_Final
  imports
    SubsetSum_DecisionTree
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
      and "\<exists>S \<subseteq> {..<length as}. sum_over as S = s"
  shows   "real (steps M (enc as s kk)) \<ge> 2 * sqrt ((2::real) ^ n)"
  using steps_ge_two_sqrt_pow2[OF assms] .

(* The "no poly bound on distinct family" theorem you finished: *)
theorem no_polytime_on_distinct_family:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
            \<forall>as s. distinct_subset_sums as \<and> (\<exists>S \<subseteq> {..<length as}. sum_over as S = s) \<longrightarrow>
              steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>)"
  by (rule no_polytime_in_n_on_distinct_family)

corollary no_polytime_on_all_inputs:
  shows "\<not> (\<exists>(c::real)>0. \<exists>(d::nat).
            \<forall>as s. (\<exists>S \<subseteq> {..<length as}. sum_over as S = s) \<longrightarrow>
              steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>)"
proof
  assume "\<exists>(c::real)>0. \<exists>d. \<forall>as s. (\<exists>S \<subseteq> {..<length as}. sum_over as S = s) \<longrightarrow>
                                    steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>"
  then obtain c d where cpos: "c > 0"
    and UB: "\<forall>as s. (\<exists>S \<subseteq> {..<length as}. sum_over as S = s) \<longrightarrow>
                     steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>" by blast
  have "\<exists>(c::real)>0. \<exists>d.
          \<forall>as s. distinct_subset_sums as \<and> (\<exists>S \<subseteq> {..<length as}. sum_over as S = s) \<longrightarrow>
                 steps M (enc as s kk) \<le> nat \<lceil> c * real (length as) ^ d \<rceil>"
    using cpos UB by blast
  with no_polytime_on_distinct_family show False by blast
qed

end
end
