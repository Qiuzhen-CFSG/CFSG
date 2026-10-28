module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Generators
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Structure

/-!+# The order and characteristic two of the fixed J₃ Thompson-normalizer candidate

The eight original model words generate a group of order 1152. Inside this
group we construct a normal subgroup of order 64 whose centralizer lies in
itself. Consequently the intrinsic two-core is self-centralizing.

The proof uses a cyclic series with factors 2,2,2,2,2,2,3,3,2. Its collection
relations are checked on all 6156 letters of the ATLAS permutation model.
Separating letters prove distinctness of the normal forms, and explicit
noncommuting letters exclude every form outside the order-64 subgroup from
its centralizer. No external calculation is a proof premise.

Source: GLS, Number 3, Table 5.3h, printed p.269, the local
`2^(2+4).(S₃ × C₃)`; application: Aschbacher–Smith, Theorem 0.1.2(5), p.4.
The candidate's ambient normalizer identification and exhaustive local
coverage are separate obligations. Reproducible data and generators are
retained under `TwoLocal/source` and `Thompson/source`.
-/

namespace Sporadic.Janko3.TwoLocal

/-- The original eight-generator candidate has order 1152. -/
public theorem thompsonNormalizerCandidate_card :
    Nat.card thompsonNormalizerCandidate = 1152 :=
  ThompsonCertificate.candidate_card

/-- The normal order-64 subgroup is intrinsic to the local candidate. -/
@[expose] public def thompsonNormalizerTwoSubgroup :
    Subgroup thompsonNormalizerCandidate := ThompsonCertificate.intrinsicCore

public theorem thompsonNormalizerTwoSubgroup_normal :
    thompsonNormalizerTwoSubgroup.Normal := ThompsonCertificate.intrinsicCore_normal

public theorem thompsonNormalizerTwoSubgroup_card :
    Nat.card thompsonNormalizerTwoSubgroup = 64 := ThompsonCertificate.intrinsicCore_card

public theorem thompsonNormalizerTwoSubgroup_isPGroup :
    IsPGroup 2 thompsonNormalizerTwoSubgroup := ThompsonCertificate.intrinsicCore_isPGroup

/-- Centralization is taken in the local candidate, not in the ambient model. -/
public theorem thompsonNormalizerTwoSubgroup_selfCentralizing :
    Subgroup.centralizer (thompsonNormalizerTwoSubgroup : Set thompsonNormalizerCandidate) ≤
      thompsonNormalizerTwoSubgroup := ThompsonCertificate.intrinsicCore_selfCentralizing

/-- The intrinsic two-core of the order-1152 candidate is self-centralizing. -/
public theorem thompsonNormalizerCandidate_centralizer_pCore_le :
    Subgroup.centralizer (pCore 2 thompsonNormalizerCandidate : Set thompsonNormalizerCandidate) ≤
      pCore 2 thompsonNormalizerCandidate := ThompsonCertificate.candidate_centralizer_pCore_le

/-- Cardinality in the indexing used by the local-family consumer. -/
public theorem localFamily_two_card : Nat.card (localFamily 2) = 1152 :=
  thompsonNormalizerCandidate_card

/-- Intrinsic characteristic two in the indexing used by the local-family consumer. -/
public theorem localFamily_two_centralizer_pCore_le :
    Subgroup.centralizer (pCore 2 (localFamily 2) : Set (localFamily 2)) ≤
      pCore 2 (localFamily 2) := thompsonNormalizerCandidate_centralizer_pCore_le

end Sporadic.Janko3.TwoLocal
