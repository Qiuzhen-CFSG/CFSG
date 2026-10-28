module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubic
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Cubics at the original intrinsic-four point

For the caller's chosen point z of the original intrinsic four and any
exchange element g in T outside S, g⁻¹zg lies in the original moving plane.
Apply the proved original cubic construction there and conjugate its two
outputs by g. Residual exchange puts the first cubic in YL and the second
in the conjugated component. Their separation survives conjugation, so they
generate an elementary abelian subgroup of order nine in the same C_G(z).

All BinaryMS, CommonFacts and Earlier inputs remain those of the original
component. The final consumer preserves the point selected by the existing
point-centralizer theorem. This is a pair of cubic directions for the binary
branch of Aschbacher–Smith 15.3.23, printed pp.1128–1129.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The original moving-plane cubic pair conjugates to every chosen point of
its intrinsic four. All source inputs remain the original unchanged inputs. -/
theorem intrinsicFour_point_conjugate_cubics
    {κ : GroupClass} (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (b : BinaryMS.Input κ (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ a v : G, a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a = 3 ∧ orderOf v = 3 ∧
      a ∈ centralizer ({z} : Set G) ∧ v ∈ centralizer ({z} : Set G) ∧
      a * v = v * a ∧ v ∉ YL d c.L := by
  have hgTi : g⁻¹ ∈ (d.T : Subgroup G) := inv_mem hgT
  have hgSi : g⁻¹ ∉ d.S := fun hh => hgS (inv_mem_iff.mp hh)
  let f := MulAut.conj g
  let w := (MulAut.conj g⁻¹) z
  have hwz : f w = z := by simp [f,w,MulAut.conj_apply,mul_assoc]
  have hw : w ∈ movingPlane d c.L := by
    rw [←intrinsicFour_conjugate_eq_movingPlane_of_MS93
      d c.L e h hg b t common earlier g⁻¹ hgTi hgSi]
    exact mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hz
  obtain ⟨a,v,ha,hv,haz,hvz,hav,hvS⟩ := movingPlane_commuting_cubics
    d c e h hg b t common earlier w hw
  have hY : (YC d c.L).conjBy g = YL d c.L := by
    rw [←hg.exchange g⁻¹ hgTi hgSi,conjBy_inv']
  have haY : f (a : G) ∈ YL d c.L := by
    rw [←hY]
    exact mem_map_of_mem f.toMonoidHom a.property
  have hvL : f (v : G) ∈ c.L.conjBy g :=
    mem_map_of_mem f.toMonoidHom v.property
  have hc : ∀ x : G, x ∈ centralizer ({w} : Set G) →
      f x ∈ centralizer ({z} : Set G) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg f (mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul,hwz] using hh
  refine ⟨f (a : G),f (v : G),haY,hvL,
    (orderOf_injective f.toMonoidHom f.injective (a : G)).trans ha,
    (orderOf_injective f.toMonoidHom f.injective (v : G)).trans hv,
    hc _ haz,hc _ hvz,?_,?_⟩
  · simpa only [map_mul] using congrArg f hav
  · intro hvY
    rw [←hY] at hvY
    obtain ⟨x,hx,he⟩ := hvY
    have hxv : x = (v : G) := f.injective he
    apply hvS
    exact ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)
      (hxv ▸ hx)

/-- Two commuting cubic directions with the second outside the first's
containing subgroup generate an actual elementary abelian group of order nine. -/
theorem elementary_nine_of_commuting_cubics
    (A : Subgroup G) (z a v : G) (haA : a ∈ A) (hvA : v ∉ A)
    (ha : orderOf a = 3) (hv : orderOf v = 3)
    (haz : a ∈ centralizer ({z} : Set G))
    (hvz : v ∈ centralizer ({z} : Set G)) (hav : a * v = v * a) :
    ∃ E : Subgroup G, E ≤ centralizer ({z} : Set G) ∧
      a ∈ E ∧ v ∈ E ∧ IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  let D := zpowers a
  have hD : IsElementaryAbelian 3 D :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ha ▸ pow_orderOf_eq_one a)
  let := hD
  have hvD : v ∉ D := fun hh => hvA ((zpowers_le.mpr haA) hh)
  have hfix : D ≤ centralizer ({v} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hav)
  have hcard : Nat.card D = 3 ^ 1 := by rw [Nat.card_zpowers,ha]; norm_num
  obtain ⟨he,hsize⟩ := IsElementaryAbelian.fixed_join_card D v hv
    (D.disjoint_zpowers_of_prime_order_not_mem v hv hvD) hfix hcard
  refine ⟨D ⊔ zpowers v,sup_le (zpowers_le.mpr haz) (zpowers_le.mpr hvz),
    (show D ≤ D ⊔ zpowers v from le_sup_left) (mem_zpowers a),
    (show zpowers v ≤ D ⊔ zpowers v from le_sup_right) (mem_zpowers v),he,?_⟩
  exact hsize

/-- A cubic commuting with a YL cubic and independent of YL lies outside the
entire original component, whose three-rank is one. -/
theorem commuting_cubic_not_mem_original_component
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (a v : G) (haY : a ∈ YL d c.L) (hvY : v ∉ YL d c.L)
    (ha : orderOf a = 3) (hv : orderOf v = 3) (hav : a * v = v * a) :
    v ∉ c.L := by
  intro hvL
  have hYL : YL d c.L ≤ c.L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  let aa : c.L := ⟨a,hYL haY⟩
  let vv : c.L := ⟨v,hvL⟩
  have haa : orderOf aa = 3 := (Subgroup.orderOf_coe aa).symm.trans ha
  have hvv : orderOf vv = 3 := (Subgroup.orderOf_coe vv).symm.trans hv
  let D := zpowers aa
  let : IsElementaryAbelian 3 D :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (haa ▸ pow_orderOf_eq_one aa)
  have hDY : D.map c.L.subtype ≤ YL d c.L := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr haY
  have hvD : vv ∉ D := fun hh => hvY (hDY (mem_map_of_mem c.L.subtype hh))
  have hfix : D ≤ centralizer ({vv} : Set c.L) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (Subtype.ext hav))
  have hcard : Nat.card D = 3 ^ 1 := by rw [Nat.card_zpowers,haa]; norm_num
  have hr := IsElementaryAbelian.primeRank_ge_of_fixed_join D vv hvv hvD hfix hcard
  rw [component_three_rank d c e] at hr
  omega


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- Full original Chapter15 data give commuting cubic directions in the
centralizer of the caller's chosen intrinsic-four point. -/
theorem binary_three_source_intrinsic_point_conjugate_cubics
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ a v : G, a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a = 3 ∧ orderOf v = 3 ∧
      a ∈ centralizer ({z} : Set G) ∧ v ∈ centralizer ({z} : Set G) ∧
      a * v = v * a ∧ v ∉ YL d c.L := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  let := hW
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hgeo⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  exact intrinsicFour_point_conjugate_cubics d c eSL h hgeo b t common earlier z hz g hgT hgS

/-- The same chosen intrinsic-four point has an explicit elementary nine
with one cubic in YL and the other in the conjugated component. -/
theorem binary_three_source_intrinsic_point_elementary_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ a v : G, ∃ E : Subgroup G,
      a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a = 3 ∧ orderOf v = 3 ∧
      a ∈ centralizer ({z} : Set G) ∧ v ∈ centralizer ({z} : Set G) ∧
      a * v = v * a ∧ v ∉ YL d c.L ∧
      E ≤ centralizer ({z} : Set G) ∧ a ∈ E ∧ v ∈ E ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨a,v,haY,hvL,ha,hv,haz,hvz,hav,hvY⟩ :=
    binary_three_source_intrinsic_point_conjugate_cubics
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  obtain ⟨E,hEC,haE,hvE,hE,hcard⟩ :=
    elementary_nine_of_commuting_cubics (YL d c.L) z a v haY hvY ha hv haz hvz hav
  exact ⟨a,v,E,haY,hvL,ha,hv,haz,hvz,hav,hvY,hEC,haE,hvE,hE,hcard⟩

/-- Preserve the literal involution selected by the existing point-centralizer
consumer and construct an elementary nine in that same centralizer. -/
theorem binary_three_source_point_centralizer_with_elementary_nine
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      (d.T : Subgroup G) ⊓ centralizer ({z} : Set G) = d.S ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      IsSQTK KnownSimple.IsKnownSimple (centralizer ({z} : Set G)) ∧
      primeRank 3 (centralizer ({z} : Set G)) ≤ 2 ∧
      ∃ E : Subgroup G, E ≤ centralizer ({z} : Set G) ∧
        IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨z,hz,hz2,hLS,hCT,hout,hsq,hr⟩ := binary_three_source_point_centralizer
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier
  obtain ⟨a,v,E,_,_,_,_,_,_,_,_,hEC,_,_,hE,hcard⟩ :=
    binary_three_source_intrinsic_point_elementary_nine
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  exact ⟨z,hz,hz2,hLS,hCT,hout,hsq,hr,E,hEC,hE,hcard⟩

/-- At the caller's original point, the second cubic lies in the conjugated
component and outside the original component. The original MS inputs suffice. -/
theorem binary_three_source_intrinsic_point_outside_cubic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ a v : G, ∃ E : Subgroup G,
      a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a = 3 ∧ orderOf v = 3 ∧
      a ∈ centralizer ({z} : Set G) ∧ v ∈ centralizer ({z} : Set G) ∧
      a * v = v * a ∧ v ∉ c.L ∧
      E ≤ centralizer ({z} : Set G) ∧ a ∈ E ∧ v ∈ E ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨a,v,E,haY,hvL,ha,hv,haz,hvz,hav,hvY,hEC,haE,hvE,hE,hcard⟩ :=
    binary_three_source_intrinsic_point_elementary_nine
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  have hvout := commuting_cubic_not_mem_original_component d c eSL a v haY hvY ha hv hav
  exact ⟨a,v,E,haY,hvL,ha,hv,haz,hvz,hav,hvout,hEC,haE,hvE,hE,hcard⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
