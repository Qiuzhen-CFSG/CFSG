module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointIndex
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubicMovement
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The cubic orbit at the original displacement point

The elementary nine supplied by the T-conjugate component has exactly one
cubic direction in the normalizer of the original component L. Indeed the
point normalizer has three-part three, and the original YL cubic belongs to
both subgroups. The chosen opposite cubic therefore moves L, producing
three distinct conjugates with that same residual cubic in their intersection.
It also acts nontrivially on the full original commutator core.

These conjugates remain distinct in C_G(z)/O₂(C_G(z)). The quotient kernel
lies in O₂(LS) and normalizes the original perfect L, so the normalizer of
its image lifts to the original normalizer. Coprimality preserves both
cubic orders, including the common intersection subgroup.

The final theorem applies this calculation at the actual original-core
displacement involution, retaining the full Sylow S, original component,
T-conjugation and local data. CommonFacts and Earlier are discharged by the
proved MS93 path theorem. This supplies original ambient geometry for the
remaining input of `source_lemma_15_3_23_of_large_distance`, and hence of
`SourceRankTwo.source_lemma_15_3_13_of_binary_three_large_distance`.
The exclusion of this configuration still requires the nonabelian core and
paired action argument; this module does not prove that exclusion or the
legacy universal MS classification.

Source: the original setup of Aschbacher--Smith 15.3.23, printed
pp.1128--1129, with the intrinsic four from MS93 (4.5), pp.895--900.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem nine_normalizer_intersection
    (L E : Subgroup G) (z a : G) (hEC : E ≤ centralizer ({z} : Set G))
    (hE : Nat.card E = 9)
    (hn : ¬ 9 ∣ Nat.card (normalizer (L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G))
    (haE : a ∈ E) (haL : a ∈ L) (ha : orderOf a = 3) :
    E ⊓ normalizer (L : Set G) = zpowers a := by
  let H := E ⊓ normalizer (L : Set G)
  have hH : H ≤ normalizer (L : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hEC)
  have hdiv : Nat.card H ∣ 3 ^ 2 := by
    simpa only [hE,show (3 : ℕ)^2 = 9 from rfl] using
      (card_dvd_of_le (show H ≤ E from inf_le_left))
  have h9 : ¬ 9 ∣ Nat.card H := fun hh => hn (hh.trans (card_dvd_of_le hH))
  have hsmall : Nat.card H ≤ 3 := by
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
    interval_cases k
    · rw [he]; decide
    · rw [he]; decide
    · exact (h9 (he ▸ dvd_rfl)).elim
  have hA : zpowers a ≤ H := zpowers_le.mpr ⟨haE,L.le_normalizer haL⟩
  exact (eq_of_le_of_card_ge hA (by
    simpa only [Nat.card_zpowers,ha] using hsmall)).symm

omit [Finite G] in
private theorem cubic_conjugates_distinct
    (L : Subgroup G) (v : G) (hv : orderOf v = 3)
    (hn : v ∉ normalizer (L : Set G)) :
    L.conjBy v ≠ L ∧ L.conjBy v⁻¹ ≠ L ∧ L.conjBy v ≠ L.conjBy v⁻¹ := by
  have h1 : L.conjBy v ≠ L := fun he => hn (mem_normalizer_iff_map_conj_eq.mpr he)
  have h2 : L.conjBy v⁻¹ ≠ L := fun he =>
    hn (inv_mem_iff.mp (mem_normalizer_iff_map_conj_eq.mpr he))
  refine ⟨h1,h2,?_⟩
  intro he
  have h3 : v^3 = 1 := by simpa only [hv] using pow_orderOf_eq_one v
  have hp : v * v = v⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa only [pow_succ,pow_zero,one_mul] using h3)
  have hh := congrArg (fun H : Subgroup G => H.conjBy v) he
  rw [←conjBy_mul, hp, conjBy_inv'] at hh
  exact h2 hh

omit [Finite G] in
private theorem commuting_common_subgroup
    (L : Subgroup G) (a v : G) (ha : a ∈ L) (hav : a * v = v * a) :
    zpowers a ≤ L ⊓ (L.conjBy v ⊓ L.conjBy v⁻¹) := by
  have hai : a * v⁻¹ = v⁻¹ * a := (show Commute a v from hav).inv_right
  apply zpowers_le.mpr
  refine ⟨ha,⟨a,ha,?_⟩,⟨a,ha,?_⟩⟩
  · change v * a * v⁻¹ = a
    rw [←hav,mul_inv_cancel_right]
  · change v⁻¹ * a * (v⁻¹)⁻¹ = a
    rw [inv_inv,←hai,inv_mul_cancel_right]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
include hG hempty hM hu hmany hI htwo hf e b t common earlier

/-- At each nonidentity intrinsic-four point, the actual opposite cubic
escapes N_G(L). Its elementary nine meets N_G(L) in precisely the original
YL cubic, which lies in all three distinct conjugates of L. -/
theorem binary_three_source_point_cubic_orbit
    (z : G) (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ a v : G, ∃ E : Subgroup G,
      a ∈ YL d c.L ∧ v ∈ c.L.conjBy g ∧
      orderOf a = 3 ∧ orderOf v = 3 ∧ a * v = v * a ∧
      E ≤ centralizer ({z} : Set G) ∧ a ∈ E ∧ v ∈ E ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ⊓ normalizer (c.L : Set G) = zpowers a ∧
      v ∉ normalizer (c.L : Set G) ∧
      v ∉ centralizer (LinearThree.commutatorCore c.L : Set G) ∧
      zpowers a ≤ c.L ⊓ (c.L.conjBy v ⊓ c.L.conjBy v⁻¹) ∧
      c.L.conjBy v ≠ c.L ∧ c.L.conjBy v⁻¹ ≠ c.L ∧
      c.L.conjBy v ≠ c.L.conjBy v⁻¹ := by
  obtain ⟨a,v,E,haY,hvL,ha,hv,_,_,hav,hvout,hEC,haE,hvE,hE,hcard,hmove⟩ :=
    binary_three_source_intrinsic_point_moving_cubic
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  have haL : a ∈ c.L :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right) haY
  have hN := (binary_three_source_point_normalizer_three_part
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1).2
  have hEq := nine_normalizer_intersection c.L E z a hEC hcard hN haE haL ha
  have hvN : v ∉ normalizer (c.L : Set G) := by
    intro hvn
    have hvA : v ∈ zpowers a := hEq ▸ (show v ∈ E ⊓ normalizer (c.L : Set G) from ⟨hvE,hvn⟩)
    exact hvout ((zpowers_le.mpr haL) hvA)
  exact ⟨a,v,E,haY,hvL,ha,hv,hav,hEC,haE,hvE,hE,hcard,hEq,hvN,hmove,
    commuting_common_subgroup c.L a v haL hav,
    cubic_conjugates_distinct c.L v hv hvN⟩

omit common earlier t in
private theorem point_quotient_normalizer_preimage
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    (normalizer ((c.L.subgroupOf C).map q : Set (C ⧸ pCore 2 C))).comap q =
      (normalizer (c.L : Set G)).subgroupOf C := by
  let C := centralizer ({z} : Set G)
  let J := c.L ⊔ d.S
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := c.L.subgroupOf C
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  obtain ⟨hcore,_,_,_⟩ := binary_three_source_point_opposite_core
    hG d hempty hM hu hmany hI htwo hf c e z hLS P hP g hgT hgS
  have hJN : J ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hqn : q.ker ≤ normalizer (B : Set C) := by
    rw [QuotientGroup.ker_mk',←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact hJN ((hcore.trans (J.pCoreIn_le 2)) (mem_map_of_mem C.subtype hx))
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let : Group.IsPerfect (c.L.subgroupOf J) := b.component.perfect
  let ec : (c.L.subgroupOf J) ≃* B :=
    (subgroupOfEquivOfLe (show c.L ≤ J from le_sup_left)).trans
      (subgroupOfEquivOfLe hLC).symm
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := ec.toMonoidHom) ec.surjective
  have hp : IsPPerfect 2 B := by
    intro N hN htwoN
    let := hN
    have hs : Subsingleton (B ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (B ⧸ N) htwoN.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  exact (comap_normalizer_map_of_pPerfect q B hp hq hqn).trans
    (subgroupOf_normalizer_eq hLC).symm

omit common earlier in
/-- The original large-distance source supplies a three-member component
orbit at its displacement point. The literal two-core quotient preserves
the orbit and its common cubic, with no extra MS classification premise. -/
theorem binary_three_large_distance_point_cubic_quotient_orbit
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, orderOf z = 2 ∧
      ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ = zpowers z ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      (d.T : Subgroup G) ⊓ centralizer ({z} : Set G) = d.S ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      ∃ a v : C, ∃ E : Subgroup G,
        (a : G) ∈ YL d c.L ∧ (v : G) ∈ c.L.conjBy g ∧
        orderOf a = 3 ∧ orderOf v = 3 ∧ a * v = v * a ∧
        E ≤ C ∧ (a : G) ∈ E ∧ (v : G) ∈ E ∧
        IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
        E ⊓ normalizer (c.L : Set G) = zpowers (a : G) ∧
        (v : G) ∉ normalizer (c.L : Set G) ∧
        (v : G) ∉ centralizer (LinearThree.commutatorCore c.L : Set G) ∧
        q v ∉ normalizer (B : Set (C ⧸ pCore 2 C)) ∧
        orderOf (q a) = 3 ∧ orderOf (q v) = 3 ∧
        zpowers (q a) ≤ B ⊓ (B.conjBy (q v) ⊓ B.conjBy (q v)⁻¹) ∧
        B.conjBy (q v) ≠ B ∧ B.conjBy (q v)⁻¹ ≠ B ∧
        B.conjBy (q v) ≠ B.conjBy (q v)⁻¹ ∧
        ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S := by
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨z,hz2,hline,hLS,hTS,hout,_,P,hP⟩ :=
    binary_three_large_distance_displacement_point hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz2; omega
  have he := (binary_three_source_original_displacement_eq_fixedLine
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier).1
  have hz : z ∈ intrinsicFour c.L := by
    have hm : z ∈ ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ := hline.symm ▸ mem_zpowers z
    rw [he] at hm
    exact hm.1
  obtain ⟨a,v,E,haY,hvL,ha,hv,hav,hEC,haE,hvE,hE,hcard,hEq,hvN,hmove,_,_,_,_⟩ :=
    binary_three_source_point_cubic_orbit
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1 g hgT hgS
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let aa : C := ⟨a,hEC haE⟩
  let vv : C := ⟨v,hEC hvE⟩
  have hvqN : q vv ∉ normalizer (B : Set (C ⧸ pCore 2 C)) := by
    intro hm
    have hm' : vv ∈ (normalizer (B : Set (C ⧸ pCore 2 C))).comap q := hm
    rw [point_quotient_normalizer_preimage
      hG d hempty hM hu hmany hI htwo hf c e b z hLS P hP g hgT hgS] at hm'
    exact hvN hm'
  have hvv : orderOf vv = 3 := (Subgroup.orderOf_coe vv).symm.trans hv
  have haa : orderOf aa = 3 := (Subgroup.orderOf_coe aa).symm.trans ha
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have haq3 : orderOf (q aa) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hq aa (by rw [haa]; decide)).trans haa
  have hvq : orderOf (q vv) = 3 :=
    (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hq vv (by rw [hvv]; decide)).trans hvv
  obtain ⟨h1,h2,h3⟩ := cubic_conjugates_distinct B (q vv) hvq hvqN
  have haL : a ∈ c.L :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right) haY
  have haq : q aa ∈ B := mem_map_of_mem q (show aa ∈ c.L.subgroupOf C from haL)
  have havq : q aa * q vv = q vv * q aa := by
    simpa only [map_mul] using congrArg q (show aa * vv = vv * aa from Subtype.ext hav)
  exact ⟨z,hz2,hline,hLS,hTS,hout,aa,vv,E,haY,hvL,
    haa,hvv,Subtype.ext hav,hEC,haE,hvE,
    hE,hcard,hEq,hvN,hmove,hvqN,haq3,hvq,
    commuting_common_subgroup B (q aa) (q vv) haq havq,h1,h2,h3,P,hP⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
