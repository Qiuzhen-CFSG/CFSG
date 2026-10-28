module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.Cover
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.SylowAlignment
public import Theory.SpecificGroups.Triality.TwoLocalCover.SylowAlignment
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.SylowAlignment

/-!
# Exceptional normalizer covers without an order-four restriction

The checked hexagon and octagon covers already allow every nonidentity
two-subgroup. Their simultaneous Sylow-normalizer coverage transports through
the genuine octonion, graph-field D₄ and Ree model equivalences. In particular,
the triality result retains its degree-one case. Central covers in 1.1.5 are
handled by the component-quotient equivalences before these results are applied.

Source: Aschbacher--Smith, 15.3.41 and the parabolic step of 15.3.35,
printed pp.1138--1139. G₂ uses the licensed ATLAS port (LICENSES/ATLAS.txt).
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

/-- Coverage on the actual split-octonion G₂ carrier. -/
theorem g2_twoSubgroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hK : ClassificationModels.IsG2At K (2 ^ n)) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hK
  let : Field F := hF
  let : Finite F := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  apply TwoSubgroupNormalizerCover.of_mulEquiv (e := e)
  exact Atlas.G2.EvenLocal.NormalizerCover.normalizer_sup_lt_top

/-- Coverage for genuine triality, including the field of order two. -/
theorem triality_twoSubgroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {n : ℕ} (hn : 0 < n) (hK : Triality.Standard.IsTrialityGroupAt (2 ^ n) K) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff K n hn).mp hK
  apply TwoSubgroupNormalizerCover.of_mulEquiv (e := e)
  exact Triality.Standard.TwoLocalCover.normalizer_sup_lt_top n hn

/-- Coverage for the source's Ree fixed group, through its canonical model equivalence. -/
theorem ree_twoSubgroupNormalizerCover {K : Type*} [Group K] [Finite K]
    {m : ℕ} (hm : 1 ≤ m) (hK : Chapter1.Section02.LocalModels.IsReeF4At K m) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨d, ⟨e⟩⟩ := hK
  apply TwoSubgroupNormalizerCover.of_mulEquiv (e := e.trans d.modelEquiv)
  exact ReeF4.ConverseParabolics.normalizer_sup_lt_top hm

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
