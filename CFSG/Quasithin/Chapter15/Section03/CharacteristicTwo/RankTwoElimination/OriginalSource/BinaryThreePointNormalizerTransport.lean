module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanUnique
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanCanonicalKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralEight

/-!
# The marked fixed-span normalizer and an escaping cubic

The unique-complement source transports the full residual-and-S normalizer to
U.  The canonical two-core source then transports it to F.  The same original
residual geometry supplies a literal cubic in Y_C which moves the chosen
intrinsic-four point; this keeps the cubic action and the full kernel in the
same ambient normalizer.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section03.RankTwo
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_moves_intrinsicFour_transport
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (a : G) (ha : a ∈ YC d c.L) (ha3 : orderOf a = 3) :
    a ∉ centralizer (intrinsicFour c.L : Set G) := by
  intro haf
  obtain ⟨i,j,hij,hm,hf,_,hsup,_⟩ := hg.coordinates
  have hfour : intrinsicFour c.L = d.action.plane i :=
    (intrinsicFour_eq_complementary_plane_of_MS93 d c.L e h hg b t common earlier).trans hf
  have hac : a ∈ centralizer (d.V : Set G) := by
    have hm := (le_centralizer_iff.mp (zpowers_le.mpr (hg.plane_centralized ha)))
    have hf := (le_centralizer_iff.mp (zpowers_le.mpr (hfour ▸ haf)))
    exact (le_centralizer_iff.mp (hsup ▸ sup_le hm hf)) (mem_zpowers a)
  have haY : a ∈ d.Y := hg.first_choice ▸
    ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left) ha
  have h9 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9 := hg.first_choice ▸ h.quotient_card
  have hk := residualY_centralizer_eq_twoCore d.action h.image h9
  have hak : (⟨a,haY⟩ : d.Y) ∈ pCore 2 d.Y := hk ▸ hac
  let x : pCore 2 d.Y := ⟨⟨a,haY⟩,hak⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change a ^ 3 = 1
    rw [←ha3]
    exact pow_orderOf_eq_one a
  have hx1 : x = 1 := (pCore_isPGroup (p := 2) (G := d.Y)).powEquiv
    (by decide : Nat.Coprime 2 3) |>.injective (by
      simpa only [IsPGroup.powEquiv_apply,one_pow] using hx3)
  have ha1 : a = 1 := congrArg (fun x : pCore 2 d.Y => ((x : d.Y) : G)) hx1
  rw [ha1,orderOf_one] at ha3
  omega

/-- The actual cubic in the original residual moves the chosen intrinsic
four while preserving any fixed-span normalizer supplied by the unique
complement source. -/
theorem binary_three_source_cubic_fixed_span_transport
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (C : Subgroup G)
    (hNU : YC d c.L ≤ normalizer
      (conjugateSpanBy (intrinsicFour c.L) C : Set G)) :
    ∃ a : G, a ∈ YC d c.L ∧ orderOf a = 3 ∧
      a ∉ centralizer (intrinsicFour c.L : Set G) ∧
      a ∈ normalizer (conjugateSpanBy (intrinsicFour c.L) C : Set G) := by
  have hdiv : 3 ∣ Nat.card (YC d c.L) := by
    apply Nat.dvd_of_factorization_pos
    intro hzfac
    have hc3 := h.centralizer_three_part
    rw [hzfac,pow_zero] at hc3
    omega
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := YC d c.L) 3 hdiv
  have ha3 : orderOf (a : G) = 3 :=
    (Subgroup.orderOf_coe a).trans ha
  have hamove : (a : G) ∉ centralizer (intrinsicFour c.L : Set G) :=
    cubic_moves_intrinsicFour_transport d c e h hg b t common earlier
      (a : G) a.property ha3
  exact ⟨a,a.property,ha3,hamove,hNU a.property⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93

/-- Once the unique-complement normalizer is supplied, the full residual-and-S
normalizer is an actual outside member.  The proof keeps the literal
component escape and only uses the supplied elementary two-group U. -/
theorem binary_three_source_fixed_span_normalizer_enlargement
    {G : Type*} [Group G] [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (C : Subgroup G)
    (hYL : d.Yplus ≤ normalizer (c.L : Set G))
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hNU : normalizer (c.L : Set G) ≤ normalizer
      (conjugateSpanBy (intrinsicFour c.L) C : Set G))
    (hUp : IsPGroup 2 (conjugateSpanBy (intrinsicFour c.L) C))
    (z : G) (hzU : z ∈ conjugateSpanBy (intrinsicFour c.L) C)
    (hz2 : orderOf z = 2) :
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let NU := normalizer (U : Set G)
    (d.Yplus ⊔ d.S ≤ NU) ∧ d.S ≤ NU ∧ NU ∈ d.Hplus := by
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let NU := normalizer (U : Set G)
  have hYS : d.Yplus ⊔ d.S ≤ NU :=
    sup_le (hYL.trans hNU) (hSL.trans hNU)
  have hLNU : c.L ≤ NU := c.L.le_normalizer.trans hNU
  have hnotM : ¬ NU ≤ d.M := by
    intro hNM
    exact c.outside (hLNU.trans hNM)
  have hNUnorm : NU ≤ normalizer (U : Set G) := by rfl
  have hUcore : U ≤ NU.pCoreIn 2 := le_pCoreIn_of_normalizes hUp U.le_normalizer hNUnorm
  have hpcoren : NU.pCoreIn 2 ≠ ⊥ := by
    intro hbot
    have hz1 : z = 1 := hbot.le (hUcore hzU)
    rw [hz1,orderOf_one] at hz2
    omega
  exact ⟨hYS,le_sup_right.trans hYS,⟨⟨hpcoren,hYS⟩,hnotM⟩⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
