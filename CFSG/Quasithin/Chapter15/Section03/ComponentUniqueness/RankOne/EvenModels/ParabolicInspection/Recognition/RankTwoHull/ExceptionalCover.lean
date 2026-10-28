module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoHull.LocalCover
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.SylowAlignment
public import Theory.SpecificGroups.Triality.TwoLocalCover.SylowAlignment
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.SylowAlignment

/-!
# Exceptional rank-two coverage for the invariant parabolic hull

For G₂, genuine graph-field triality, and the large Ree groups, a Sylow
two-subgroup normalizing a four-group has its full normalizer in a common
proper overgroup with the four-group normalizer. The concrete hexagon or
octagon first covers the latter normalizer. The positive-root Sylow's Borel
normalizer and Sylow conjugacy inside that same parabolic give simultaneous
coverage. Actual model isomorphisms transport this intrinsic conclusion.

These are the exceptional rank-two inputs to the characteristic-two paragraph
following Aschbacher--Smith 15.3.43(e), printed p.1140. The model catalogue is
1.1.5(3)(a)--(c), pp.501--502, and A.2.3--4, p.33. The source field restrictions
are retained; the Ree model has field order `2^(2*m+1)` with `1 ≤ m`.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

open Subgroup

private theorem fourGroup_ne_bot {G : Type*} [Group G] (R : Subgroup G)
    (hR : Nat.card R = 4) : R ≠ ⊥ := by
  intro h
  subst R
  simp at hR

/-- The split-octonion G₂ model supplies simultaneous four-group and Sylow
normalizer coverage over the source's nonbinary fields. -/
theorem g2_fourGroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (_hn : 1 < n) (hK : ClassificationModels.IsG2At K (2 ^ n)) :
    FourGroupNormalizerCover K := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hK
  let : Field F := hF
  let : Finite F := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  apply FourGroupNormalizerCover.of_mulEquiv (e := e)
  intro P R he hc hn
  let : IsElementaryAbelian 2 R := he
  exact Atlas.G2.EvenLocal.NormalizerCover.normalizer_sup_lt_top P R
    (fourGroup_ne_bot R hc) (IsElementaryAbelian.isPGroup 2 R) hn

/-- The carrier here is the genuine D₄ graph-field fixed-group construction. -/
theorem triality_fourGroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 1 < n) (hK : Triality.Standard.IsTrialityGroupAt (2 ^ n) K) :
    FourGroupNormalizerCover K := by
  have hn₀ : 0 < n := Nat.zero_lt_of_lt hn
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff K n hn₀).mp hK
  apply FourGroupNormalizerCover.of_mulEquiv (e := e)
  intro P R he hc hP
  let : IsElementaryAbelian 2 R := he
  exact Triality.Standard.TwoLocalCover.normalizer_sup_lt_top n hn₀ P R
    (fourGroup_ne_bot R hc) (IsElementaryAbelian.isPGroup 2 R) hP

/-- Coverage for the actual large Ree model, transported by its specified
group isomorphism. The degree-one full and Tits groups are excluded by `hm`. -/
theorem ree_fourGroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nonempty (K ≃* ReeF4.Model m)) :
    FourGroupNormalizerCover K := by
  obtain ⟨e⟩ := hK
  apply FourGroupNormalizerCover.of_mulEquiv (e := e)
  intro P R he hc hP
  let : IsElementaryAbelian 2 R := he
  exact ReeF4.ConverseParabolics.normalizer_sup_lt_top hm P R
    (fourGroup_ne_bot R hc) (IsElementaryAbelian.isPGroup 2 R) hP

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
