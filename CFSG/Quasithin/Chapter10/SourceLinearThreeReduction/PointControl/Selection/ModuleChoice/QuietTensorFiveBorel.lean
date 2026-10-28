module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorPrimeFive
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorBinaryNumerical
public import Theory.Alternating.FivePairBorelJoin
public import Theory.GroupTheory.SolvableSylowControl.PrimeKernel

/-!
# The full Borel in the original prime-five tensor point centralizer

The original cubic plane and exchanged component determine a noncentral
swapped input, retaining their full two-core kernels. The actual PSL₂(5)
to PSL₂(4) comparison applies the binary Borel and H-star theorem to this
same component. In its square quotient the cubic plane fills the Borel's
odd part; pulling back the Sylow normalizer identifies the full Borel as
X(T intersect K_z). Solvable Sylow control through the original kernel
then proves K_z intersect M is this Borel and K_z T intersect M is XT.

The Source application supplies every displayed local input from its
retained prime-five reduction, for each original cubic Sylow. Tensor-base
recognition, the ambient equalities in 8.3.10(2), strict r bound, point-core
containment, both quiet exclusions and the distinct positive-fixed-layer
output remain obligations of the selected-module owner.
Source: Aschbacher--Smith 8.3.10(1), printed pp.725--726, using the genuine
rank-one Borels and the literal original point and residual.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
open Chapter1 Chapter1.XiEmbedding ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem swapped_noncentral {T P K : Subgroup G}
    (hs : SwappedFactors T P K) (hP : IsPGroup 3 P) (hne : P ≠ ⊥)
    (hz : center (XiQuotient K) = ⊥) : ¬ ⁅K,P⁆ ≤ K.pCoreIn 2 := by
  intro hcomm
  let q := QuotientGroup.mk' (pCore 2 K)
  have hk : ⁅(⊤ : Subgroup K), P.subgroupOf K⁆ ≤ pCore 2 K := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_commutator, ←MonoidHom.range_eq_map, range_subtype, subgroupOf_map_subtype]
    exact (commutator_mono le_rfl inf_le_left).trans hcomm
  have hc : ⁅(⊤ : Subgroup (XiQuotient K)), (P.subgroupOf K).map q⁆ = ⊥ := by
    rw [←map_top_of_surjective q (QuotientGroup.mk'_surjective _), ←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hk
  have he : (P.subgroupOf K).map q = ⊥ :=
    bot_unique ((commutator_top_left_eq_bot_iff_le_center.mp hc).trans_eq hz)
  have hp : P.subgroupOf K ≤ pCore 2 K := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
  have hi : P ⊓ K = ⊥ := by
    apply bot_unique
    intro x hx
    have hcore : x ∈ K.pCoreIn 2 := mem_map_of_mem K.subtype (hp (show (⟨x,hx.2⟩ : K) ∈ P.subgroupOf K from hx.1))
    exact (hP.disjoint_of_coprime (isPGroup_pCoreIn 2 K) (by decide)).le_bot ⟨hx.1,hcore⟩
  obtain ⟨_,t,_,_,hf,_,_⟩ := hs
  apply hne
  simpa only [hi,Subgroup.conjBy,Subgroup.map_bot,sup_bot_eq] using hf

private theorem five_binary_model {Q : Type*} [Group Q]
    (hm : ClassicalGroup.IsPSL Q 2 5) : ClassicalGroup.IsPSL Q 2 (2^2) := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,
    GaloisField.card 2 2 (by decide),⟨a.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF)⟩⟩

/-- The actual exchanged prime-five orbit has the Borel X(T intersect K_z). -/
theorem swapped_five_borel_eq_join {T : Sylow 2 G} {X P H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X P H I)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 5) :
    borel (componentOrbit I (T : Subgroup G)) (T : Subgroup G) =
      X ⊔ ((T : Subgroup G) ⊓ componentOrbit I (T : Subgroup G)) := by
  let K := componentOrbit I (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 K)
  let R := (T : Subgroup G).subgroupOf K
  have hi := hs.toLocalInput
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hXK : X ≤ K := hi.le_of_complement_le hs.complement_le_orbit
    ((normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal)
  have hPK : P ≤ K := hs.complement_le_orbit
  obtain ⟨S,hS⟩ := SwappedSylow.orbit_quotient_sylow hs
  obtain ⟨c⟩ := swapped_product hs
  have hp := hi.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput c)
  let ep := InvariantThree.complementEquiv hi hPK
  have hP3 : IsPGroup 3 (quotientImage K P) :=
    hp.1.isPGroup.of_equiv ep
  have hcard : Nat.card (quotientImage K P) = 9 :=
    (Nat.card_congr ep.toEquiv).symm.trans hp.2
  have hm4 := five_binary_model hm
  let S' := S.mapSurjective (f := c.toMonoidHom) c.surjective
  let P' := (quotientImage K P).map c.toMonoidHom
  let : Group.IsSolvable (quotientImage K P ⊔ (S : Subgroup (XiQuotient K)) : Subgroup _) := by
    rw [hS]
    exact SwappedSylow.quotient_solvable hs.toSwappedInput
  let : Group.IsSolvable (P' ⊔ (S' : Subgroup (XiQuotient I × XiQuotient I)) : Subgroup _) := by
    change Group.IsSolvable ((quotientImage K P).map c.toMonoidHom ⊔
      (S : Subgroup (XiQuotient K)).map c.toMonoidHom : Subgroup _)
    rw [←Subgroup.map_sup]
    exact Group.isSolvable_of_surjective (c.toMonoidHom.subgroupMap_surjective _)
  have hPN : quotientImage K P ≤ normalizer (S : Set (XiQuotient K)) := by
    apply (map_le_map_iff_of_injective (f := c.toMonoidHom) c.injective).mp
    change (quotientImage K P).map c.toMonoidHom ≤
      (normalizer ((S : Subgroup (XiQuotient K)) : Set _)).map c.toMonoidHom
    rw [map_equiv_normalizer_eq]
    exact SwappedSylow.binary_model_prod_le_normalizer (by decide : 2 ≤ 2) hm4 S' P'
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm4
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let e := c.trans (MulEquiv.prodCongr (a.trans b) (a.trans b))
  have hjoin := Theory.AlternatingFive.sylow_normalizer_eq_cubic_join e S (quotientImage K P) hP3 hcard hPN
  have hR : (S : Subgroup (XiQuotient K)).comap q = R := by
    rw [hS]
    exact SwappedSylow.twoImage_preimage hs
  have hcore : pCore 2 K ≤ R := by
    rw [←hR]
    intro x hx
    change q x ∈ (S : Subgroup (XiQuotient K))
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hpre : normalizer (R : Set K) = P.subgroupOf K ⊔ R := by
    have hh := congrArg (comap q) hjoin
    change (quotientImage K P ⊔ (S : Subgroup (XiQuotient K))).comap q =
      (normalizer ((S : Subgroup (XiQuotient K)) : Set (XiQuotient K))).comap q at hh
    rw [comap_normalizer_eq_of_surjective (S : Subgroup (XiQuotient K))
      (f := q) (QuotientGroup.mk'_surjective _),hR] at hh
    rw [hS] at hh
    change ((P.subgroupOf K).map q ⊔ R.map q).comap q = _ at hh
    rw [←Subgroup.map_sup,comap_map_eq,QuotientGroup.ker_mk',
      sup_of_le_left (hcore.trans le_sup_right)] at hh
    exact hh.symm
  have hb : (borel K (T : Subgroup G)).subgroupOf K = normalizer (R : Set K) := by
    change (K ⊓ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).subgroupOf K = _
    rw [inf_subgroupOf_left,subgroupOf_normalizer_eq inf_le_right]
    congr 1
    ext x
    exact and_iff_left x.property
  have hb' : borel K (T : Subgroup G) = P ⊔ ((T : Subgroup G) ⊓ K) := by
    have hh := congrArg (map K.subtype) (hb.trans hpre)
    rw [map_subgroupOf_eq_of_le (show borel K (T : Subgroup G) ≤ K from inf_le_left),
      Subgroup.map_sup,map_subgroupOf_eq_of_le hPK,subgroupOf_map_subtype] at hh
    exact hh
  rw [hb']
  apply le_antisymm (sup_le_sup_right hi.complement_le _)
  apply sup_le _ le_sup_right
  rw [←hi.complement]
  exact sup_le ((le_inf hi.core_le_two_group ((pCoreIn_le 2 X).trans hXK)).trans le_sup_right) le_sup_left

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Recover the original swapped input from its retained factorization and cubic plane. -/
theorem quiet_tensor_five_swapped_input
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {K : Subgroup G}
    (hK : K ∈ cComponentsIn (centralizer ({z} : Set G)))
    (hq : IsQuasisimple (XiQuotient K))
    (hclosure : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩ = componentOrbit K (T : Subgroup G))
    (hcomm : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      ⁅d.Kz,(P : Subgroup d.X).map d.X.subtype⁆ = d.Kz)
    (hplane : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      Nonempty (((P : Subgroup d.X).map d.X.subtype) ≃* Plane 3))
    (hswap : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      SwappedFactors (T : Subgroup G) ((P : Subgroup d.X).map d.X.subtype) K)
    (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 5) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X
      ((P : Subgroup d.X).map d.X.subtype) d.Gz K := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let P₀ := (P : Subgroup d.X).map d.X.subtype
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.Gz :=
    D.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hz2)
  have hcenter : center (XiQuotient K) = ⊥ := by
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    exact (Theory.PSL2.primeField_center_outer_of_equiv (by decide : Nat.Prime 5)
      (by decide : Odd 5) hF a).1
  have hne : P₀ ≠ ⊥ := by
    obtain ⟨a⟩ := hplane
    have hc := Nat.card_congr a.toEquiv
    have hc' : Nat.card (Plane 3) = 9 := by simp [Plane]
    change Nat.card P₀ = Nat.card (Plane 3) at hc
    intro hh
    rw [hh,Subgroup.card_bot,hc'] at hc
    omega
  exact {
    toLocalInput := hi
    sqtk := hsq
    component := hK
    quasisimple := hq
    orbit_normal := hclosure ▸ d.Kz_normal
    complement_le_orbit := hi.complement_le.trans (d.X_le_Kz.trans_eq hclosure)
    orbit_commutator := hclosure ▸ hcomm
    noncentral := swapped_noncentral hswap (P.isPGroup'.map d.X.subtype) hne hcenter
    not_invariant := hswap.1
    sylow_two := ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩ }

/-- The same original prime-five component gives the full point Borel and H-star.
The displayed Borel is the literal normalizer of T intersect K_z. -/
theorem quiet_tensor_five_borel_hstar
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {K : Subgroup G}
    (hs : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X
        ((P : Subgroup d.X).map d.X.subtype) d.Gz K)
    (hclosure : CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩ = componentOrbit K (T : Subgroup G))
    (hm : ClassicalGroup.IsPSL (XiQuotient K) 2 5) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    d.KzT ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal ∧
      d.Kz ⊓ D.maximalLocal = borel d.Kz (T : Subgroup G) ∧
      borel d.Kz (T : Subgroup G) = d.X ⊔ ((T : Subgroup G) ⊓ d.Kz) ∧
      (d.KzT ⊓ D.maximalLocal) = d.XT := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let B := borel K (T : Subgroup G) ⊔ (T : Subgroup G)
  have hm4 := five_binary_model hm
  obtain ⟨hb,hKM,hEM,hstar,_⟩ := quiet_tensor_point_binary_hstar
    D hmany hmin hn hJ cL e hbase hzV hz1 hzT P hs hclosure (by decide : 2 ≤ 2) hm4
  have hj : d.KzT = K ⊔ (T : Subgroup G) := by
    change d.Kz ⊔ (T : Subgroup G) = _
    rw [hclosure]
    exact le_antisymm (sup_le (componentOrbit_le_sup K (T : Subgroup G)) le_sup_right)
      (sup_le_sup_right (le_componentOrbit K (T : Subgroup G)) _)
  have hBT : (T : Subgroup G) ≤ B := le_sup_right
  have hBH : B ≤ d.Gz := sup_le (inf_le_left.trans hs.component.1) hzT
  have hTB : (T : Subgroup G) ⊓ normalizer (K : Set G) ≤
      normalizer (borel K (T : Subgroup G) : Set G) := by
    apply (le_inf inf_le_right ?_).trans inf_normalizer_le_normalizer_inf
    exact ((le_inf (inf_le_left.trans (T : Subgroup G).le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf).trans (normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)).le_normalizer
  let : Group.IsSolvable B := hs.component.2.relative_local_adjoin_isSolvable
    hs.component.1 inf_le_left hzT T.isPGroup' hTB hb.solvable
  obtain ⟨c⟩ := swapped_product hs
  have hcontrol : SolvableSylowControl 2 (XiQuotient d.Kz) := by
    rw [hclosure]
    apply SolvableSylowControl.of_equiv c
    intro S A hA hSA
    let : Group.IsSolvable A := hA
    let : Group.IsSolvable (A ⊔ (S : Subgroup (XiQuotient K × XiQuotient K)) : Subgroup _) := by
      rw [sup_eq_left.mpr hSA]
      infer_instance
    exact SwappedSylow.binary_model_prod_le_normalizer (by decide : 2 ≤ 2) hm4 S A
  have hc : SolvableSylowControl 2 d.Kz :=
    SolvableSylowControl.of_surjective_pKernel (QuotientGroup.mk' (pCore 2 d.Kz))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hcontrol
  obtain ⟨S,hS⟩ : IsSylowIn 2 ((T : Subgroup G) ⊓ d.Kz) d.Kz :=
    hclosure.symm ▸ SwappedSylow.orbit_sylow hs
  have hBN : B ≤ normalizer (((T : Subgroup G) ⊓ d.Kz : Subgroup G) : Set G) := by
    have hh := hc.normalizes_sylow d.Kz B S
      (hBH.trans (le_normalizer_conjugateSpanBy d.X d.Gz))
      (hS.le.trans (inf_le_left.trans hBT))
    rwa [hS] at hh
  have hBorel : borel d.Kz (T : Subgroup G) = d.X ⊔ ((T : Subgroup G) ⊓ d.Kz) := by
    simpa only [←hclosure] using swapped_five_borel_eq_join hs hm
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hXM : d.X ≤ D.maximalLocal := d.X_le.trans inf_le_left |>.trans (localOrbit T L).le_normalizer
  have hBM : d.Kz ⊓ D.maximalLocal = borel d.Kz (T : Subgroup G) := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,hBN ?_⟩
      exact hEM.le ⟨(hj ▸ (show d.Kz ≤ d.KzT from le_sup_left)) hx.1,hx.2⟩
    · rw [hBorel]
      exact sup_le (le_inf d.X_le_Kz hXM) (le_inf inf_le_right (inf_le_left.trans hTM))
  have hMT : d.KzT ⊓ D.maximalLocal = d.XT := by
    have hfactor : d.KzT ⊓ D.maximalLocal =
        (d.Kz ⊓ D.maximalLocal) ⊔ (T : Subgroup G) := by
      apply le_antisymm
      · rintro x ⟨hx,hxM⟩
        have hp : x ∈ (d.Kz : Set G) * ((T : Subgroup G) : Set G) := by
          rw [←coe_mul_of_right_le_normalizer_left d.Kz (T : Subgroup G)
            (hzT.trans (le_normalizer_conjugateSpanBy d.X d.Gz))]
          exact hx
        obtain ⟨k,hk,t,ht,hkt⟩ := hp
        have hkM : k ∈ D.maximalLocal := by
          have hh := D.maximalLocal.mul_mem hxM (D.maximalLocal.inv_mem (hTM ht))
          rwa [←hkt,mul_inv_cancel_right] at hh
        rw [←hkt]
        exact mul_mem_sup ⟨hk,hkM⟩ ht
      · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
          (le_inf le_sup_right hTM)
    rw [hfactor,hBM,hBorel,sup_assoc,
      show ((T : Subgroup G) ⊓ d.Kz) ⊔ (T : Subgroup G) = (T : Subgroup G) from
        sup_eq_right.mpr inf_le_left]
    rfl
  exact ⟨hj.symm ▸ hstar,hBM,hBorel,hMT⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
