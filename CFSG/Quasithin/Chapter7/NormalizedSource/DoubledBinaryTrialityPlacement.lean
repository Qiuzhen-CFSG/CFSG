module
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.NormalizedRootCentralizers

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields
public import Theory.SpecificGroups.Triality.ElementaryNine
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.PerfectCentralCoverKernelLowerBound
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer

/-!
# Triality Sylow placement on the binary paired plane

An element with centralizer index at most two in the genuine triality
Sylow centralizes a nonzero central-simple root parameter. Coroot rescaling
reduces the relevant matrix entry to the checked parameter-one calculation,
putting the element in the arms radical. Every noncentral element of that
radical has a commutator map onto the fixed field, contradicting index two
when q > 2. Thus the original moving sixteen lies in the full Sylow center
and the same field exponent is at least four.

The large-field two-primary covering calculation makes the original
component center odd. Centerlessness, supplied by the source odd-core
argument, and cubic rank two give relative component normality. The actual
fixed-field torus acts freely on a nonidentity highest-root element, forcing
centralizer index at least fifteen in the original Sylow normalizer.

NonFFSourceDoubledBinaryTrialityPlacement applies these results to the
canonical inner action and the original component Sylow, placing it in Q.
Source: Aschbacher–Smith 7.7.6, printed p.706, refs/quasithin.pdf; the genuine
graph-field coordinates and covers use GLS3 §§2.4, 2.6 and 6.1, as cited in
the imported triality modules. No auxiliary triality carrier is used.
-/

open Subgroup
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.PositiveCoordinates Triality.Standard.ConcreteBruhat
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.Parabolics.RankOneMatrices

public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTrialityPlacement
private theorem arm_pairings (j : Fin 12) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 0) =
      (∑ k : Fin 4, rootCoords (simpleIndex 0) k * rootCoords (positiveIndex j) k) := by
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = _
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [Int.cast_sum, Int.cast_mul, ← typeDRootPairing_root_val, rootCoords_spec]

private theorem first_coordinate_zero_of_nonzero (P : Parameters) (hp : P.prime = 2)
    (v : Coordinates P) (t : ExtensionField P) (ht : t ≠ 0)
    (hc : Commute (orderedProduct P v) (curve P 3 t)) : v 0 = 0 := by
  let a := Units.mk0 t ht
  let g := torusWord P 0 a
  let w : Coordinates P := fun j =>
    t ^ ((typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 0)) * v j
  have hp3 : (typeDRootPairing 2).pairingIn ℤ (rootIndex 3) (typeDSimpleRootIndex 2 0) = -1 := by
    rw [arm_pairings]; decide
  have hprod : g * orderedProduct P v * g⁻¹ = orderedProduct P w := by
    change MulAut.conj g (orderedProduct P v) = _
    simp only [orderedProduct, map_list_prod, List.map_ofFn]
    congr 2
    funext j
    exact torusWord_curve_conjugate P hp 0 a j (v j)
  have hcurve : g * curve P 3 t * g⁻¹ = curve P 3 1 := by
    rw [torusWord_curve_conjugate P hp, hp3]
    simp only [a, Units.val_mk0, zpow_neg_one, inv_mul_cancel₀ ht]
  have hh := hc.map (MulAut.conj g).toMonoidHom
  change Commute (g * orderedProduct P v * g⁻¹) (g * curve P 3 t * g⁻¹) at hh
  rw [hprod,hcurve] at hh
  have hz := UnipotentMatrices.first_coordinate_zero P hp w hh
  change t ^ ((typeDRootPairing 2).pairingIn ℤ (rootIndex 0) (typeDSimpleRootIndex 2 0)) * v 0 = 0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (zpow_ne_zero _ ht)

private theorem fixed_commutant_le_arms (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hg : g ∈ positiveSubgroup P)
    (hfix : graphFieldAutomorphism P g = g)
    (t : ExtensionField P) (ht : t ≠ 0) (hc : Commute g (curve P 3 t)) :
    g ∈ rootSubgroup P .arms := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  obtain ⟨v, rfl⟩ := (show g ∈ Set.range (orderedProduct (binaryParameters n hn)) by
    rw [range_orderedProduct_binary]; exact hg)
  have hv := (orderedProduct_mem_fixedSubgroup_iff_binary n hn v).mp hfix
  have h0 := first_coordinate_zero_of_nonzero _ rfl v t ht hc
  have h1 : v 1 = 0 := by simpa only [show diagram 0 = 1 from rfl, h0, map_zero] using hv 0
  have h2 : v 2 = 0 := by simpa only [show diagram 1 = 2 from rfl, h1, map_zero] using hv 1
  apply orderedProduct_mem_rootSubgroup _ .arms ⟨v, ?_⟩
  intro i hi
  have hi' : i.val < 3 := by simpa only [rootSupport, not_le] using hi
  fin_cases i <;> first | exact h0 | exact h1 | exact h2 | norm_num at hi'

private theorem index_comap_le {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (C : Subgroup Y) (f : X →* Y) : (C.comap f).index ≤ C.index := by
  rw [C.index_comap]
  exact (relIndex_le_of_le_right (H := C) (le_top : f.range ≤ ⊤)
    (by simpa using C.index_ne_zero_of_finite)).trans_eq C.relIndex_top_right

private def centralSimpleElementary (P : Parameters) : Multiplicative (fixedField P) →* ElementaryGroup P where
  toFun t := ElementaryCentralKernel.centralElementary P true t.toAdd.val t.toAdd.property
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change positiveRoot P 1 0 = 1
    simpa only [curve_simple] using curve_zero P (simplePosition 1)
  map_mul' s t := by
    apply Subtype.ext
    apply Subtype.ext
    change positiveRoot P 1 (s.toAdd.val + t.toAdd.val) =
      positiveRoot P 1 s.toAdd.val * positiveRoot P 1 t.toAdd.val
    simpa only [curve_simple] using curve_add P (simplePosition 1) s.toAdd.val t.toAdd.val

private def centralSimpleHom (P : Parameters) : Multiplicative (fixedField P) →* unipotent P :=
  ((toCarrier P).comp (centralSimpleElementary P)).codRestrict _
    (fun t => ⟨_,positiveRoot_mem_positiveSubgroup P 1 t.toAdd.val,rfl⟩)

private theorem small_centralizer_le_arms (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (x : unipotent P)
    (hi : (centralizer ({x} : Set (unipotent P))).index ≤ 2) :
    x.val ∈ armsSubgroup P := by
  let C := (centralizer ({x} : Set (unipotent P))).comap (centralSimpleHom P)
  have hC : C.index ≤ 2 := (index_comap_le _ _).trans hi
  have hn : C ≠ ⊥ := by
    intro h
    rw [h,index_bot] at hC
    have hc : Nat.card (Multiplicative (fixedField P)) = P.q :=
      card_fixedField P
    rw [hc] at hC
    omega
  obtain ⟨t,ht,htne⟩ := C.bot_or_exists_ne_one.resolve_left hn
  have ht0 : t.toAdd.val ≠ 0 := by
    intro hh
    apply htne
    exact congrArg Multiplicative.ofAdd (Subtype.ext hh)
  obtain ⟨e,he,hex⟩ := x.property
  let c := ElementaryCentralKernel.centralElementary P true t.toAdd.val t.toAdd.property
  have hc : Commute (toCarrier P e) (toCarrier P c) := by
    have hh : Commute ((centralSimpleHom P) t).val x.val :=
      congrArg (fun z : unipotent P => (z : Carrier P)) (mem_centralizer_singleton_iff.mp ht)
    change Commute (toCarrier P c) x.val at hh
    exact (congrArg (fun z : Carrier P => Commute z (toCarrier P c)) hex).mpr hh.symm
  have hec : Commute e c := Commute.of_map (ElementaryCentralKernel.toCarrier_injective P hp) hc
  refine ⟨e,fixed_commutant_le_arms P hp (elementaryInclusion P e) he e.val.property
    t.toAdd.val ht0 ?_,hex⟩
  have hh := hec.map (elementaryInclusion P)
  change Commute (elementaryInclusion P e) (positiveRoot P 1 t.toAdd.val) at hh
  simpa only [show (3 : Fin 12) = simplePosition 1 from rfl, curve_simple] using hh

private theorem arms_commutator_surjective (P : Parameters) (hp : P.prime = 2)
    (v : ArmsParameters P) (hne : v ≠ centralParameters P (v.2 2)) :
    Function.Surjective (armsCommutator P v) := by
  intro z
  by_cases h1 : v.2 1 = 0
  · by_cases h0 : v.2 0 = 0
    · by_cases ha : v.1 0 = 0
      · by_cases hb : v.1 1 = 0
        · exfalso
          apply hne
          apply Prod.ext <;> funext i <;> fin_cases i <;>
            simp [centralParameters,ha,hb,h0,h1]
        · obtain ⟨b,hb⟩ := armsPairing_surjective_left P hp (v.1 1) hb z
          exact ⟨(![b,0],0),by simpa [armsCommutator,armsCocycle] using hb⟩
      · obtain ⟨b,hb⟩ := armsPairing_surjective_right P hp (v.1 0) ha z
        exact ⟨(![0,b],0),by simpa [armsCommutator,armsCocycle] using hb⟩
    · refine ⟨(0,![0,z / v.2 0,0]),?_⟩
      simp [armsCommutator,armsCocycle,h0]
  · refine ⟨(0,![z / v.2 1,0,0]),?_⟩
    simp only [armsCommutator,armsCocycle,Pi.zero_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      armsPairing_zero_left,armsPairing_zero_right,zero_mul,add_zero]
    exact mul_div_cancel₀ _ h1

private def armsCommutatorHom (P : Parameters) (hp : P.prime = 2)
    (v : ArmsParameters P) : armsSubgroup P →* Multiplicative (fixedField P) where
  toFun y := Multiplicative.ofAdd (armsCommutator P v ((armsEquiv P hp).symm y))
  map_one' := by
    have hh : (armsEquiv P hp).symm 1 = centralParameters P 0 := by
      apply (armsEquiv P hp).injective
      rw [Equiv.apply_symm_apply,(armsEquiv_central_eq_one_iff P hp 0).mpr rfl]
    change armsCommutator P v ((armsEquiv P hp).symm 1) = 0
    rw [hh,armsCommutator_central_right]
  map_mul' x y := by
    obtain ⟨a,rfl⟩ := (armsEquiv P hp).surjective x
    obtain ⟨b,rfl⟩ := (armsEquiv P hp).surjective y
    change armsCommutator P v ((armsEquiv P hp).symm (armsEquiv P hp a * armsEquiv P hp b)) =
      armsCommutator P v ((armsEquiv P hp).symm (armsEquiv P hp a)) +
      armsCommutator P v ((armsEquiv P hp).symm (armsEquiv P hp b))
    rw [←armsEquiv_multiply,Equiv.symm_apply_apply,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    simp only [armsCommutator,armsCocycle,armsMultiply,Pi.add_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,armsPairing_add_left,armsPairing_add_right,
      mul_add,add_mul]
    abel

private theorem arms_small_centralizer (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (x : armsSubgroup P)
    (hi : (centralizer ({x} : Set (armsSubgroup P))).index ≤ 2) :
    x ∈ center (armsSubgroup P) := by
  obtain ⟨v,rfl⟩ := (armsEquiv P hp).surjective x
  by_cases hv : v = centralParameters P (v.2 2)
  · rw [hv]
    exact centralParameters_mem_center P hp _
  let f := armsCommutatorHom P hp v
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w,hw⟩ := arms_commutator_surjective P hp v hv z.toAdd
    refine ⟨armsEquiv P hp w,?_⟩
    change Multiplicative.ofAdd (armsCommutator P v ((armsEquiv P hp).symm (armsEquiv P hp w))) = z
    rw [Equiv.symm_apply_apply]
    exact congrArg Multiplicative.ofAdd hw
  have hk : f.ker = centralizer ({armsEquiv P hp v} : Set (armsSubgroup P)) := by
    ext y
    obtain ⟨w,rfl⟩ := (armsEquiv P hp).surjective y
    change Multiplicative.ofAdd (armsCommutator P v ((armsEquiv P hp).symm (armsEquiv P hp w))) = 1 ↔ _
    rw [Equiv.symm_apply_apply]
    change armsCommutator P v w = 0 ↔ _
    rw [←armsEquiv_central_eq_one_iff P hp,←armsEquiv_commutator,
      commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff]
    exact eq_comm
  have hcard : f.ker.index = P.q := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top]
    exact card_fixedField P
  rw [hk] at hcard
  omega
private theorem triality_coordinate_central (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (x : unipotent P)
    (hi : (centralizer ({x} : Set (unipotent P))).index ≤ 2) :
    x ∈ center (unipotent P) := by
  have hxR := small_centralizer_le_arms P hp hq x hi
  have hRU : armsSubgroup P ≤ unipotent P :=
    descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .arms)
  let y : armsSubgroup P := ⟨x.val,hxR⟩
  have hC : (centralizer ({x} : Set (unipotent P))).comap (inclusion hRU) =
      centralizer ({y} : Set (armsSubgroup P)) := by
    ext z
    simp only [mem_comap,mem_centralizer_singleton_iff]
    constructor
    · intro hh
      apply Subtype.ext
      exact congrArg (fun z : unipotent P => (z : Carrier P)) hh
    · intro hh
      apply Subtype.ext
      exact congrArg (fun z : armsSubgroup P => (z : Carrier P)) hh
  have hy := arms_small_centralizer P hp hq y (by
    rw [←hC]
    exact (index_comap_le _ _).trans hi)
  have hh : x.val ∈ highestRoot P := by
    rw [←embedded_center_arms P hp]
    exact ⟨y,hy,rfl⟩
  rw [←embedded_center_unipotent P hp] at hh
  obtain ⟨z,hz,hzx⟩ := hh
  exact (Subtype.ext hzx : z = x) ▸ hz

private theorem centralizer_comap_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (x : X) :
    (centralizer ({e x} : Set Y)).comap e.toMonoidHom = centralizer ({x} : Set X) := by
  ext y
  simp only [mem_comap, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    ← map_mul, e.injective.eq_iff]

theorem triality_centralizes {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : IsTrialityGroupAt (2^n) G)
    (S : Sylow 2 G) (A : Subgroup G)
    (hAS : A ≤ (S : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (S : Subgroup G)).index ≤ 2) :
    A ≤ (center S).map (S : Subgroup G).subtype := by
  obtain ⟨P,hq,⟨e⟩⟩ := hm
  have hp : P.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
    have hd : P.prime ∣ 2^n := hq ▸ dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
    exact P.prime_prime.dvd_of_dvd_pow hd
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let c : S ≃* unipotent P :=
    (e.subgroupMap (S : Subgroup G)).trans (R.equiv (unipotentSylow P hp))
  have hbig : 2 < P.q := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at hh
    omega
  intro a ha
  let x : S := ⟨a,hAS ha⟩
  have hC : (centralizer ({x} : Set S)) = (centralizer ({a} : Set G)).subgroupOf
      (S : Subgroup G) := by
    ext y
    simp only [mem_centralizer_singleton_iff,mem_subgroupOf,x]
    exact Subtype.ext_iff
  have hidx : (centralizer ({x} : Set S)).index ≤ 2 := by
    rw [hC]
    apply le_trans _ hi
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
      (index_dvd_of_le (comap_mono (centralizer_le (Set.singleton_subset_iff.mpr ha))))
  have hcidx : (centralizer ({c x} : Set (unipotent P))).index ≤ 2 := by
    rw [←(centralizer ({c x} : Set _)).index_comap_of_surjective
      (f := c.toMonoidHom) c.surjective,centralizer_comap_equiv]
    exact hidx
  refine ⟨x,mem_center_iff.mpr ?_,rfl⟩
  intro y
  apply c.injective
  simpa only [map_mul] using mem_center_iff.mp (triality_coordinate_central P hp hbig (c x) hcidx) (c y)

theorem triality_degree_ge_four {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : IsTrialityGroupAt (2^n) G)
    (S : Sylow 2 G) (A : Subgroup G) (hA : Nat.card A = 16)
    (hAS : A ≤ (S : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (S : Subgroup G)).index ≤ 2) :
    4 ≤ n := by
  have hAZ := triality_centralizes hn hm S A hAS hi
  obtain ⟨P,hq,⟨e⟩⟩ := hm
  have hp : P.prime = 2 := by
    apply (Nat.prime_dvd_prime_iff_eq P.prime_prime Nat.prime_two).mp
    have hd : P.prime ∣ 2^n := hq ▸ dvd_pow_self P.prime (Nat.ne_of_gt P.exponent_pos)
    exact P.prime_prime.dvd_of_dvd_pow hd
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let c : S ≃* unipotent P :=
    (e.subgroupMap (S : Subgroup G)).trans (R.equiv (unipotentSylow P hp))
  have hcard : Nat.card (center S) = 2^n := by
    rw [Nat.card_congr (centerCongr c).toEquiv,card_center_unipotent P hp,hq]
  have hb := Nat.card_le_card_of_injective (inclusion hAZ) (inclusion_injective hAZ)
  rw [card_map_of_injective (S : Subgroup G).subtype_injective,hcard,hA] at hb
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hb


open Theory.GroupTheory

theorem triality_center_odd {K : Type*} [Group K] [Finite K]
    [IsQuasisimple K] {n : ℕ} (hn : 2 ≤ n)
    (hm : IsTrialityGroupAt (2^n) (K ⧸ center K)) : Odd (Nat.card (center K)) := by
  have hn0 : 0 < n := by omega
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ n hn0).mp hm
  have hker := CentralCovers.TwoPrimary.universal_not_two_dvd_kernel_of_two_le n hn0 hn
  have hd := (PerfectCentralCovering.centralQuotientCover e).kernel_card_dvd_universal
  rw [PerfectCentralCovering.centralQuotientCover_ker] at hd
  exact Nat.not_even_iff_odd.mp (fun he => hker ((even_iff_two_dvd.mp he).trans hd))

theorem triality_component_normal {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : IsComponentIn K H)
    (hH : primeRank 3 H ≤ 2) (hz : center K = ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hm : IsTrialityGroupAt (2^n) (K ⧸ center K)) :
    (K.subgroupOf H).Normal := by
  let := hK.quasisimple
  have hn0 : 0 < n := by omega
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ n hn0).mp hm
  let eK : K ≃* BinaryCarrier n hn0 := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)
  let e₀ := (subgroupOfEquivOfLe hK.1).trans eK
  have hz₀ : center (K.subgroupOf H) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hK.1)).toEquiv,hz,card_bot]
  apply hK.2.normal_of_centerless_primeRank (p := 3) hz₀
  · rw [primeRank_equiv 3 e₀]
    let E := ElementaryNine.subgroup (binaryParameters n hn0) rfl
    let : IsElementaryAbelian 3 E := ElementaryNine.subgroup_elementary _ _
    exact IsElementaryAbelian.primeRank_ge_of_card E (ElementaryNine.card_subgroup _ _)
  · exact hH

private def scalarNormalizer (P : Parameters) (hp : P.prime = 2) :
    (fixedField P)ˣ →* normalizer (unipotent P : Set (Carrier P)) :=
  (((torus P).subtype.comp (TorusCoordinates.torusMulEquiv P hp).toMonoidHom).comp
    (MonoidHom.inr (ExtensionField P)ˣ (fixedField P)ˣ)).codRestrict _ (fun t => by
      rw [normalizer_unipotent_eq_borel P hp]
      exact torus_le_borel P (TorusCoordinates.torusMulEquiv P hp (1,t)).property)

private theorem triality_standard_index (P : Parameters) (hp : P.prime = 2)
    (A : Subgroup (Carrier P)) (hne : A ≠ ⊥)
    (hAZ : A ≤ (center (unipotent P)).map (unipotent P).subtype) :
    P.q - 1 ≤ ((centralizer (A : Set (Carrier P))).subgroupOf
      (normalizer (unipotent P : Set (Carrier P)))).index := by
  let C := (centralizer (A : Set (Carrier P))).subgroupOf
    (normalizer (unipotent P : Set (Carrier P)))
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hroot := hAZ ha
  rw [embedded_center_unipotent P hp,←highestHom_range P hp] at hroot
  obtain ⟨c,rfl⟩ := hroot
  have hc0 : c.toAdd ≠ 0 := by
    intro h0
    apply hane
    change highestHom P hp c = 1
    have he : c = 1 := h0
    rw [he,map_one]
  have hk : C.comap (scalarNormalizer P hp) = ⊥ := by
    apply bot_unique
    intro t ht
    have hcomm := mem_centralizer_iff.mp ht (highestHom P hp c) ha
    change highestHom P hp c * (TorusCoordinates.torusMulEquiv P hp (1,t)).val =
      (TorusCoordinates.torusMulEquiv P hp (1,t)).val * highestHom P hp c at hcomm
    have hfix := mul_inv_eq_iff_eq_mul.mpr hcomm.symm
    have hscalar := NormalizedRootCentralizers.torus_conjugate_highestHom P hp (1,t) c.toAdd
    change (TorusCoordinates.torusMulEquiv P hp (1,t)).val * highestHom P hp c *
      (TorusCoordinates.torusMulEquiv P hp (1,t)).val⁻¹ = _ at hscalar
    have heq := hscalar.symm.trans hfix
    have he : t.val * c.toAdd = c.toAdd := congrArg Multiplicative.toAdd (highestHom_injective P hp heq)
    exact Units.ext (mul_right_cancel₀ hc0 (he.trans (one_mul _).symm))
  have hi := index_comap_le C (scalarNormalizer P hp)
  rw [hk,index_bot,Nat.card_units,card_fixedField] at hi
  exact hi
private theorem centralizer_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image (A : Set G) e.toMonoidHom)
  intro x hx
  obtain ⟨y,rfl⟩ := e.surjective x
  refine ⟨y,?_,rfl⟩
  intro a ha
  apply e.injective
  simpa only [map_mul] using hx (e a) (mem_map_of_mem e.toMonoidHom ha)

/-- The actual triality Sylow normalizer has index at least fifteen over the
centralizer of the moving sixteen. -/
theorem triality_normalizer_index {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : IsTrialityGroupAt (2^n) G)
    (P : Sylow 2 G) (A : Subgroup G) (hA : Nat.card A = 16)
    (hAP : A ≤ (P : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    15 ≤ ((centralizer (A : Set G)).subgroupOf (normalizer (P : Set G))).index := by
  have hAZ := triality_centralizes hn hm P A hAP hi
  have hn4 := triality_degree_ge_four hn hm P A hA hAP hi
  obtain ⟨R,hq,⟨e⟩⟩ := hm
  have hp : R.prime = 2 := by
    apply Nat.prime_eq_prime_of_dvd_pow R.prime_prime Nat.prime_two
    rw [←hq]
    exact dvd_pow_self _ (Nat.ne_of_gt R.exponent_pos)
  let P₀ := (unipotentSylow R hp).mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P₀ P
  let f := e.symm.trans (MulAut.conj g)
  have hP : (unipotent R).map f.toMonoidHom = (P : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent R).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup G) at hh
    change (unipotent R).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [←map_map]
    exact hh
  have hZ : ((center (unipotent R)).map (unipotent R).subtype).map f.toMonoidHom =
      (center P).map (P : Subgroup G).subtype := by
    rw [map_embeddedCenter _ _ f.injective,hP]
  let A₀ := A.map f.symm.toMonoidHom
  have hA₀ : A₀.map f.toMonoidHom = A := by
    change (A.map f.symm.toMonoidHom).map f.toMonoidHom = A
    rw [map_map]
    rw [show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id _ by
      ext x; exact f.apply_symm_apply x, map_id]
  have hAZ₀ : A₀ ≤ (center (unipotent R)).map (unipotent R).subtype := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [hA₀,hZ]
    exact hAZ
  have hcard : Nat.card A₀ = 16 := (card_map_of_injective f.symm.injective).trans hA
  have hne : A₀ ≠ ⊥ := by intro hh; rw [hh,card_bot] at hcard; omega
  have hb := triality_standard_index R hp A₀ hne hAZ₀
  have hlarge : 16 ≤ R.q := hq ▸ Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn4
  have hN : (normalizer (unipotent R : Set (Carrier R))).map f.toMonoidHom =
      normalizer (P : Set G) := by
    rw [map_equiv_normalizer_eq,hP]
    rfl
  have hC : (centralizer (A₀ : Set (Carrier R))).map f.toMonoidHom = centralizer (A : Set G) := by
    rw [centralizer_map_equiv,hA₀]
  change 15 ≤ (centralizer (A : Set G)).relIndex (normalizer (P : Set G))
  rw [←hC,←hN,relIndex_map_map_of_injective _ _ f.injective]
  exact (by omega : 15 ≤ R.q - 1).trans hb

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTrialityPlacement
