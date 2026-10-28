module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.Assembly
public import Theory.GroupTheory.TwoOrbitOddPrime.BinaryIndex
public import Theory.SpecificGroups.SL2.PairBorelOddOrder

/-!
# Recognition of the original Cartan in the orthogonal join

For every prime dividing q−1, the source rank bound makes the index of
K∨L₂ in G_P coprime to that prime. The order of the original SL₃ Cartan
therefore puts X inside Y. Its normalization of the original Sylow and
the ordered quotient marking bound the Y-Sylow normalizer's odd part by
(q−1)², proving that X is its odd Hall subgroup.

Only the two relative component assertions are explicit here. Their
recognition and final discharge belong to the common-core orthogonal owner.
Source: Aschbacher--Smith, printed p.774, last sentence.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem binary_component_join_index
    {J : Type*} [Group J] [Finite J] (B C : Subgroup J) [B.Normal] [C.Normal]
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C)
    {F : Type*} [Field F] [Finite F] [CharP F 2] [IsSimpleGroup PSL(2,F)]
    (eB : (B ⧸ pCore 2 B) ≃* PSL(2,F))
    (eC : (C ⧸ pCore 2 C) ≃* PSL(2,F))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ Nat.card PSL(2,F))
    (hr : primeRank p J ≤ 2) : Nat.Coprime p (B ⊔ C).index := by
  let := pCore_isNilpotent (p := 2) (G := J)
  let q := QuotientGroup.mk' (pCore 2 J)
  let B' := B.map q
  let C' := C.map q
  let : B'.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : C'.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let b : B' ≃* PSL(2,F) := (cComponentTwoCoreQuotientEquiv hB).symm.trans eB
  let c : C' ≃* PSL(2,F) := (cComponentTwoCoreQuotientEquiv hC).symm.trans eC
  let : IsSimpleGroup B' := b.isSimpleGroup
  let : IsSimpleGroup C' := c.isSimpleGroup
  let : Group.IsPerfect B' := (hB.map_quotient _).perfect
  let : Group.IsPerfect C' := (hC.map_quotient _).perfect
  have hneq : B' ≠ C' := fun he => hne (hB.eq_of_map_quotient_eq hC _ he)
  have hc : ⁅B',C'⁆ = ⊥ := simple_subnormal_commute_of_ne _ _
    (hB.map_quotient _).subnormal (hC.map_quotient _).subnormal hneq
  have hzB : center B' = ⊥ :=
    (inferInstance : (center B').Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative B' (center_eq_top_iff.mp he))
  have hzC : center C' = ⊥ :=
    (inferInstance : (center C').Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C' (center_eq_top_iff.mp he))
  have hi := TwoOrbitOddPrime.binary_join_index_coprime p B' C' F b c hc hzB hzC
    (by rwa [Nat.card_congr b.toEquiv]) (by rwa [Nat.card_congr c.toEquiv])
    ((primeRank_quotient_le_of_isTwoGroup p hp _ pCore_isPGroup).trans hr)
  change Nat.Coprime p (B.map q ⊔ C.map q).index at hi
  rw [← Subgroup.map_sup,index_map,QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),index_top,mul_one] at hi
  have hp2 : Nat.Coprime p 2 := hp.coprime_two_right
  have hcore : Nat.Coprime p (Nat.card (pCore 2 J)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_dvd_pow
    exact (hp2.pow_right n).coprime_dvd_right hn
  rw [← relIndex_mul_index (show B ⊔ C ≤ B ⊔ C ⊔ pCore 2 J from le_sup_left)]
  apply Nat.Coprime.mul_right _ hi
  rw [relIndex_sup_left]
  exact hcore.coprime_dvd_right (relIndex_dvd_card _ _)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

theorem source_orthogonalJoin_index_coprime_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1) :
    Nat.Coprime p ((orthogonalJoin (f.Li 1) V h).subgroupOf
      (coreNormalizer V H h)).index := by
  let : Fact p.Prime := ⟨hp⟩
  let N := coreNormalizer V H h
  let B := (outsideResidual H).subgroupOf N
  let C := (f.Li 1).subgroupOf N
  have hn := source_factors_normal_of_components d hK hL
  let : B.Normal := hn.1
  let : C.Normal := hn.2
  have hne : B ≠ C := by
    intro he
    have hh := congrArg (map N.subtype) he
    rw [map_subgroupOf_eq_of_le hK.1,map_subgroupOf_eq_of_le hL.1] at hh
    exact source_residual_ne_local d hh
  let : Fintype d.pair_field.Carrier := Fintype.ofFinite _
  let : Fintype S.field.Carrier := Fintype.ofFinite _
  let ef : d.pair_field.Carrier ≃+* S.field.Carrier := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
      d.pair_field.card_eq,S.field.card_eq,d.pair_degree])
  let b := subgroupOfEquivOfLe hK.1
  let c := subgroupOfEquivOfLe hL.1
  let eB : (B ⧸ pCore 2 B) ≃* PSL(2,S.field.Carrier) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
      ((d.pair_natural.quotientEquiv.trans (GorensteinWalter.sl2RingEquiv ef)).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := S.field.Carrier)))
  let eC : (C ⧸ pCore 2 C) ≃* PSL(2,S.field.Carrier) :=
    (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans (SL3.flagLocalCoreEquiv S m f 1)
  let : IsSimpleGroup PSL(2,S.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [S.field.card_eq]
      exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
        (Nat.pow_le_pow_right (by decide) S.nonbinary))
  have ho : Odd p := by
    apply Odd.of_dvd_nat _ hd
    have he : Even (2 ^ S.field.degree) := even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.ne_of_gt S.field.degree_pos))
    exact Nat.Even.sub_odd Nat.one_le_two_pow he (by decide)
  have hd' : p ∣ Nat.card PSL(2,S.field.Carrier) := by
    rw [← Nat.card_congr (Atlas.RankOneFieldAutomorphisms.slEquivPSL
      (F := S.field.Carrier)).toEquiv,GorensteinWalter.sl2_card_formula,S.field.card_eq]
    have hfac : (2 ^ S.field.degree)^2 - 1 =
        (2 ^ S.field.degree - 1) * (2 ^ S.field.degree + 1) := by
      have hpos := Nat.one_le_two_pow (n := S.field.degree)
      have hpos2 : 1 ≤ (2 ^ S.field.degree)^2 := one_le_pow₀ hpos
      nlinarith [Nat.sub_add_cancel hpos,Nat.sub_add_cancel hpos2]
    rw [hfac]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _
  have hi := binary_component_join_index B C hK.2 hL.2 hne eB eC ho hd'
    ((S.source.simpleQTKE.twoLocal_sqtk
      (coreNormalizer_twoLocal f d.conjugator_mem d.axis_eq_plane)).stronglyQuasithin p hp ho)
  rwa [← subgroupOf_sup hK.1 hL.1,
    ← (source_factorJoin_and_residual_of_components d hK hL).1] at hi

/-- The original Cartan is contained in Y; no Cartan placement is assumed. -/
theorem source_cartan_le_orthogonalJoin_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    X ≤ orthogonalJoin (f.Li 1) V h := by
  let N := coreNormalizer V H h
  let J := (orthogonalJoin (f.Li 1) V h).subgroupOf N
  have hn := source_factors_normal_of_components d hK hL
  let : ((outsideResidual H).subgroupOf N).Normal := hn.1
  let : ((f.Li 1).subgroupOf N).Normal := hn.2
  let : J.Normal := by
    dsimp only [J]
    rw [(source_factorJoin_and_residual_of_components d hK hL).1,
      subgroupOf_sup hK.1 hL.1]
    infer_instance
  let q := (QuotientGroup.mk' J).comp (inclusion (source_cartan_le_coreNormalizer d))
  have hcop : Nat.Coprime (Nat.card X) J.index := by
    rw [(Coordinates.sl3 m).cartan_card d.cartan]
    apply Nat.Coprime.pow_left
    apply Nat.coprime_of_dvd
    intro p hp hpx hpJ
    exact hp.coprime_iff_not_dvd.mp
      (source_orthogonalJoin_index_coprime_of_components d hK hL hp hpx) hpJ
  have hc : Nat.card q.range = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (card_range_dvd q) q.range.card_subgroup_dvd_card
  have hz : q.range = ⊥ := card_eq_one.mp hc
  intro x hx
  have he : q ⟨x,hx⟩ = 1 := mem_bot.mp (hz ▸ (show q ⟨x,hx⟩ ∈ q.range from ⟨⟨x,hx⟩,rfl⟩))
  exact (QuotientGroup.eq_one_iff (N := J)
    (inclusion (source_cartan_le_coreNormalizer d) ⟨x,hx⟩)).mp he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)} {h : G}
    (d : OrthogonalInput D S m f H X A h)
include d

/-- The original Cartan is the odd Hall in the literal Y-Sylow normalizer. -/
theorem source_cartan_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    IsCartan T (orthogonalJoin (f.Li 1) V h) X := by
  let Y := orthogonalJoin (f.Li 1) V h
  have hTY : (T : Subgroup G) ≤ Y := source_sylow_le_orthogonalJoin d
  have hXY : X ≤ Y := source_cartan_le_orthogonalJoin_of_components d hK hL
  have hXT : X ≤ normalizer ((T : Subgroup G) : Set G) := by
    have he : sourceTL T L = T := inf_eq_left.mpr
      ((source_original_sylow_placement d).2.1.trans le_sup_left)
    simpa only [cartanNormalizer,he] using d.cartan.1.trans inf_le_right
  have ht : sourceTL T Y = T := inf_eq_left.mpr (hTY.trans le_sup_left)
  let N := cartanNormalizer T Y
  have hXN : X ≤ N := by
    change X ≤ Y ⊓ normalizer (sourceTL T Y : Set G)
    rw [ht]
    exact le_inf hXY hXT
  have hNY : N ≤ Y := inf_le_left
  let R := T.subtype hTY
  have hNR : N.subgroupOf Y = normalizer ((R : Subgroup Y) : Set Y) := by
    change (Y ⊓ normalizer (sourceTL T Y : Set G)).subgroupOf Y = _
    rw [ht]
    change (Y ⊓ normalizer ((T : Subgroup G) : Set G)).subgroupOf Y =
      normalizer (((T : Subgroup G).subgroupOf Y) : Set Y)
    rw [← subgroupOf_normalizer_eq hTY]
    ext y
    exact and_iff_right y.property
  obtain ⟨a⟩ := source_product_quotient_of_components d hK hL
  let q := a.projection
  let Q := R.mapSurjective a.surjective
  let g := q.comp (inclusion hNY)
  have hg : g.range ≤ normalizer ((Q : Subgroup
      (SL(2,S.field.Carrier) × SL(2,S.field.Carrier))) : Set _) := by
    rintro _ ⟨n,rfl⟩
    apply (R : Subgroup Y).le_normalizer_map q
    apply mem_map.mpr
    refine ⟨inclusion hNY n,?_,rfl⟩
    rw [← hNR]
    exact n.property
  have hk : IsPGroup 2 g.ker := by
    change IsPGroup 2 (q.ker.comap (inclusion hNY))
    rw [a.kernel]
    exact ((isPGroup_pCoreIn 2 (outsideResidual H)).of_injective
      (MulEquiv.subgroupCongr d.residual_core.symm).toMonoidHom
      (MulEquiv.subgroupCongr d.residual_core.symm).injective).comap_subtype.comap_of_injective _
      (inclusion_injective hNY)
  obtain ⟨r,hr⟩ := hk.exists_card_eq
  have hdiv : Nat.card N ∣ 2 ^ (r + 2 * S.field.degree) * (2 ^ S.field.degree - 1)^2 := by
    have hd := Nat.mul_dvd_mul_left (Nat.card g.ker) (card_dvd_of_le hg)
    rw [← index_ker, g.ker.card_mul_index] at hd
    rw [Matrix.SpecialLinearGroup.card_pair_sylow_normalizer_even,S.field.card_eq,hr] at hd
    simpa only [pow_add,pow_mul,mul_assoc,Nat.mul_comm 2 S.field.degree] using hd
  have hcard : Nat.card (X.subgroupOf N) = (2 ^ S.field.degree - 1)^2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv).trans
      ((Coordinates.sl3 m).cartan_card d.cartan)
  have hindex : (X.subgroupOf N).index ∣ 2 ^ (r + 2 * S.field.degree) := by
    rw [← (X.subgroupOf N).index_mul_card,hcard] at hdiv
    exact (Nat.mul_dvd_mul_iff_right (by
      have hq : 1 < 2 ^ S.field.degree :=
        Nat.one_lt_pow (Nat.ne_of_gt S.field.degree_pos) (by decide)
      exact pow_pos (Nat.sub_pos_of_lt hq) 2)).mp hdiv
  refine ⟨hXN, ?_⟩
  constructor
  · intro p hp hp2
    have hp' : (p : ℕ) ∣ Nat.card X := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv] at hp
    have he : (p : ℕ) = 2 := hp2
    exact d.cartan.odd.not_two_dvd_nat (he ▸ hp')
  · intro p hp hp2
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two (hp.trans hindex))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

