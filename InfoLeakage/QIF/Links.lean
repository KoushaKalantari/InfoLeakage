/-
Copyright (c) 2026 Kousha Kalantari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kousha Kalantari
-/
module

public import InfoLeakage.QIF.GainFunctions
public import InfoLeakage.QIF.MinEntropy

/-!
# g-leakage under the identity gain function is min-entropy leakage

Under the identity gain function `g_id(w, x) = [w = x]`, the g-vulnerabilities of
`InfoLeakage.QIF.GainFunctions` are the vulnerabilities of `InfoLeakage.QIF.MinEntropy`, so
`g_id`-leakage is the min-entropy leakage of Smith (Proposition 3.1 of Alvim, Chatzikokolakis,
Palamidessi and Smith, *Measuring Information Leakage using Generalized Gain Functions*,
CSF 2012), and `g_id`-capacity is the min-capacity: the multiplicative form `gCapacityRatio gId`
(the exponential of the min-capacity) is the sum of the column maxima of the channel matrix, so
the logarithmic `g_id`-capacity `gCapacity gId = log ∑_y max_x C[x, y]` is the min-capacity
(Theorem 2.1 of the same paper, which is Proposition 5.1 of Braun, Chatzikokolakis and
Palamidessi, MFPS 2009).

## Main statements

* `gVulnerability_gId_eq_vulnerability`, `postGVulnerability_gId_eq_postVulnerability`:
  Proposition 3.1 of Alvim et al. (CSF 2012), prior and posterior.
* `gLeakageRatio_gId`, `gLeakage_gId`: `g_id`-leakage is min-entropy leakage.
* `gCapacityRatio_gId`, `gCapacityRatio_gId_eq_sum_iSup`: the multiplicative `g_id`-capacity is
  the exponential of the min-capacity, `∑_y max_x C[x, y]` (Theorem 2.1 of Alvim et al.,
  CSF 2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {κ : Kernel α β} [Fintype α] [DecidableEq α] [Fintype β]

/-- **Proposition 3.1 of Alvim et al. (CSF 2012)**: the prior `g_id`-vulnerability is the
vulnerability `V(π)`. -/
theorem gVulnerability_gId_eq_vulnerability : gVulnerability gId μ = vulnerability μ :=
  gVulnerability_gId

/-- The posterior `g_id`-vulnerability is the posterior vulnerability `V(π, C)`. -/
theorem postGVulnerability_gId_eq_postVulnerability :
    postGVulnerability gId μ κ = postVulnerability μ κ :=
  postGVulnerability_gId

/-- The `g_id`-leakage ratio is the multiplicative leakage `L×(π)` of Braun et al. -/
theorem gLeakageRatio_gId : gLeakageRatio gId μ κ = multLeakage μ κ := by
  rw [gLeakageRatio, multLeakage, gVulnerability_gId_eq_vulnerability,
    postGVulnerability_gId_eq_postVulnerability]

/-- **`g_id`-leakage is min-entropy leakage** (Section III-A of Alvim et al., CSF 2012):
`L_{g_id}(π, C) = H∞(X) - H∞(X | Y)`. -/
theorem gLeakage_gId [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] :
    gLeakage gId μ κ = minEntropyLeakage μ κ := by
  rw [gLeakage, gLeakageRatio_gId, minEntropyLeakage_eq_log_multLeakage]

/-- The multiplicative `g_id`-capacity is the worst-case multiplicative leakage `ML×` of Braun
et al. -/
theorem gCapacityRatio_gId : gCapacityRatio gId κ = maxMultLeakage κ := by
  simp_rw [gCapacityRatio, gLeakageRatio_gId, maxMultLeakage]

/-- **Theorem 2.1 of Alvim et al. (CSF 2012)**, multiplicative form: the multiplicative
`g_id`-capacity `gCapacityRatio gId κ`, the exponential of the min-capacity, is the sum of the
column maxima of the channel matrix. The min-capacity itself is its logarithm,
`gCapacity gId κ = log ∑_y max_x C[x, y]`. -/
theorem gCapacityRatio_gId_eq_sum_iSup [MeasurableSingletonClass α] [Nonempty α] :
    gCapacityRatio gId κ = ∑ y, ⨆ x, κ x {y} :=
  gCapacityRatio_gId.trans maxMultLeakage_eq.1

end InformationTheory
