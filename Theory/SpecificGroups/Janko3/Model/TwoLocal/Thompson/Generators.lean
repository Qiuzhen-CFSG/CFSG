module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen0
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen1
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen2
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen3
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen4
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen5
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen6
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen8

/-!
# Generators for a polycyclic series of the J₃ local candidate

Eight certified copies of the original generators and one product will give
successive relative orders 2,2,2,2,2,2,3,3,2. The relations are proved in the
certificate modules; these definitions alone assert no group order.
Source: GLS 3, Table 5.3h, printed p.269.
-/

namespace Sporadic.Janko3.TwoLocal.ThompsonCertificate
@[expose] public def g7 : Model := g8 * g6 * g8

@[expose] public def gen : ℕ → Model
  | 0 => g0
  | 1 => g1
  | 2 => g2
  | 3 => g3
  | 4 => g4
  | 5 => g5
  | 6 => g6
  | 7 => g7
  | 8 => g8
  | _ => 1

public theorem gen_mem (i : ℕ) : gen i ∈ thompsonNormalizerCandidate := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · change g0 ∈ thompsonNormalizerCandidate
    rw [g0_eq]
    exact thompsonNormalizerGenerator_mem 5
  · change g1 ∈ thompsonNormalizerCandidate
    rw [g1_eq]
    exact thompsonNormalizerGenerator_mem 0
  · change g2 ∈ thompsonNormalizerCandidate
    rw [g2_eq]
    exact thompsonNormalizerGenerator_mem 4
  · change g3 ∈ thompsonNormalizerCandidate
    rw [g3_eq]
    exact thompsonNormalizerGenerator_mem 3
  · change g4 ∈ thompsonNormalizerCandidate
    rw [g4_eq]
    exact thompsonNormalizerGenerator_mem 2
  · change g5 ∈ thompsonNormalizerCandidate
    rw [g5_eq]
    exact thompsonNormalizerGenerator_mem 1
  · change g6 ∈ thompsonNormalizerCandidate
    rw [g6_eq]
    exact thompsonNormalizerGenerator_mem 7
  · exact thompsonNormalizerCandidate.mul_mem
      (thompsonNormalizerCandidate.mul_mem
        (g8_eq.symm ▸ thompsonNormalizerGenerator_mem 6)
        (g6_eq.symm ▸ thompsonNormalizerGenerator_mem 7))
      (g8_eq.symm ▸ thompsonNormalizerGenerator_mem 6)
  · change g8 ∈ thompsonNormalizerCandidate
    rw [g8_eq]
    exact thompsonNormalizerGenerator_mem 6
  · exact thompsonNormalizerCandidate.one_mem

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
