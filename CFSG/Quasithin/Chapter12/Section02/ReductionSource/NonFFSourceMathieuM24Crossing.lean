module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24CoreFactors
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetCrossing
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointLocalCore
public import Theory.GroupTheory.TwoFixedLinesIrreducible
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Component

/-!
# Crossing and the original M24 cocode core intersections

The unique nontrivial Sylow-fixed vector lies in the selected offender
three-space. Comparing its sextet marking with the independent trio marking
places V_z in the original pair core B. Its order 128 exceeds |U|=8, so the
same selected conjugator moves V_z across A∩O₂(LT)=U. Relative normality
inside C_G(z) then forces the original closure E outside O₂(LT).

The irreducible hexacode core section fills the local core modulo the full
O₂(LT): E O₂(LT)=O₂(L_z) O₂(LT). The original commutator bound and fixed
subgroup modulo ⟨z⟩ identify V∩O₂(C_G(z))=V∩E=V_z. The reused local-core
lemmas have group-theoretic hypotheses independent of the Hermitian model;
the M24 application discharges all of those hypotheses here.

The full intersection O₂(LT)∩O₂(C_G(z)), extraspecial recognition, the earlier
whole-cocode marking, remaining Mathieu branches and ambient J4 recognition
remain with qt-d-1222-nonff-mathieu. In particular no Sylow containment in
the perfect sextet residual is imported from the distinct PSL₃(4) model.
Source: Aschbacher–Smith 8.2.12, printed p.722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Stellmacher
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

private theorem selected_pair_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom) :
    let W := D.sourceOrbit
    let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
    ∃ (q : L →* M24) (F : Additive W ≃ₗ[ZMod 2] Cocode),
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      (∀ (l : L) (w : W),
        F (Additive.ofMul (W.normalizerMonoidHom
          ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
          cocodeRepresentation (q l) (F (Additive.ofMul w))) ∧
      (∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) ∧
      ∀ w : W, (w : G) ∈ W ⊓ I.pCoreIn 2 ↔
        F (Additive.ofMul w) ∈ standardPairSpace := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let B := W ⊓ I.pCoreIn 2
  have hRL : R ≤ L := (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_left
  have hRW : R ≤ normalizer (W : Set G) := hRL.trans D.sourceOrbit_component_normalizes
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro u hu x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hu)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  obtain ⟨_,_,_,_,hn,hcomm,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  have hRI : R ≤ normalizer (I : Set G) := by
    rw [←s.generate]
    exact Chapter8.Section02.Normalizer.normalizes_twoConjugate R W i.val hRW
      (hn (Subgroup.centralizer_le_normalizer _ (hIC i.property)))
  have hWB : ⁅R,W⁆ ≤ B := MathieuPair.residual_commutator_le_pair_factor R I W
    (s.generate ▸ le_sup_left) hRI ((hIC.trans (Subgroup.centralizer_le_normalizer _)).trans hn)
    hRW ((commutator_mono le_rfl hIC).trans hcomm)
  have hdim : rank B = 9 := MathieuPair.selected_two_intersection_rank s
    ((Chapter7.log_card_eq_finrank W).trans (E.finrank_eq.trans finrank_cocode))
  obtain ⟨q,F,hqsur,hqker,hF,hplane⟩ := D.fixedPlane_marking h hmany hV hq hnon a E hE hg
  obtain ⟨f,hf,hfmark⟩ := MathieuTrio.plane_residual_marking W L U
    D.sourceOrbit_component_normalizes inf_le_left q hqsur F hF hplane
  have hFR (r : R) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w)) =
        cocodeRepresentation (f r).val (F (Additive.ofMul w)) := by
    rw [hfmark]
    exact hF (inclusion hRL r) w
  exact ⟨q,F,hqsur,hqker,hF,hplane,
    MathieuTrio.pair_space_marking W R B inf_le_left hRW hWB hdim F f hf hFR⟩

private theorem marked_central_sextet
    (q : L →* M24) (hqsur : Function.Surjective q)
    (F : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : D.sourceOrbit),
      F (Additive.ofMul (D.sourceOrbit.normalizerMonoidHom
        ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ X : Sextet, F (Additive.ofMul z) = sextetVector X := by
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hP]
    exact inf_le_left.trans (by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)])
  let Q := P.mapSurjective (f := q) hqsur
  have hfixQ (b : Q) : cocodeRepresentation b.val (F (Additive.ofMul z)) = F (Additive.ofMul z) := by
    obtain ⟨l,hl,hb⟩ := b.property
    rw [←hb,←hF]
    apply congrArg F
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G)*(z : G)*(l : G)⁻¹=(z : G)
    rw [hz l (hPT (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]
  have hv : F (Additive.ofMul z) ≠ 0 := by
    intro he
    exact hne (congrArg Additive.toMul (F.injective (he.trans F.map_zero.symm)))
  obtain ⟨X,hX,_⟩ := MathieuSextet.sylow_fixed_sextet Q _ hv hfixQ
  exact ⟨X,hX⟩

/-- The same selected M24 pair places the point seven-space in its core
and crosses the original centralizer closure out of the full LT core. -/
theorem sourceOrbit_m24_selected_point_crossing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    (z : G) ∈ U ∧ commutatorSpace L D.sourceOrbit z ≤ D.sourceOrbit ⊓ I.pCoreIn 2 ∧
      (¬ commutatorSpace L D.sourceOrbit z ≤ U) ∧
      ¬ (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
  let B := W ⊓ I.pCoreIn 2
  obtain ⟨hrU,hTU,_⟩ := D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many
    h hmany hV hq hnon a E hE hg hAT
  have hUne : U ≠ ⊥ := by
    intro he
    change rank U = 3 at hrU
    rw [he,Representation.BinaryOffender.rank_bot] at hrU
    contradiction
  have hz2 : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) z.property)
    (fun he => hne (Subtype.ext he))
  obtain ⟨_,_,_,_,_,_,_,_,_,hOmega,hcard⟩ :=
    D.sourceOrbit_m24_cocode_block_structure h hmany hV hq hnon a E hE
  have hfix : W ⊓ centralizer (T : Set G) = zpowers (z : G) := by
    apply Eq.symm
    have hzle : zpowers (z : G) ≤ W ⊓ centralizer (T : Set G) :=
      zpowers_le.mpr ⟨z.property,hz⟩
    apply eq_of_le_of_card_ge hzle
    rw [Nat.card_zpowers,hz2,←hOmega,hcard]
  have hzU : (z : G) ∈ U := involution_mem_of_invariant_of_fixed_line
    (T : Subgroup G) U W z hz2 T.isPGroup'
    ((IsElementaryAbelian.isPGroup 2 W).to_le inf_le_left) hTU hUne inf_le_left hfix
  obtain ⟨q,F,hqsur,hqker,hF,hplane,hpair⟩ :=
    D.selected_pair_coordinates h hmany hV hq hnon a E hE hg hAT s hUZ
  obtain ⟨X,hX⟩ := D.marked_central_sextet q hqsur F hF z hz hne
  have hpoint := MathieuSextet.marked_point_commutator_coordinates W L
    (show D.sourceOrbit ≤ L from hV ▸ D.le_component) D.sourceOrbit_component_normalizes q hqsur hqker F hF z X hX
  have hXB := MathieuTrio.sextet_pair_le_of_vector_mem_plane X
    (hX ▸ (hplane z).mp hzU)
  have hVzB : commutatorSpace L W z ≤ B := by
    intro w hw
    let v : W := ⟨w,commutatorSpace_le L W z D.sourceOrbit_component_normalizes hw⟩
    exact (hpair v).mpr (hXB ((hpoint v).mp hw))
  have hUcard : Nat.card U = 8 := by
    obtain ⟨k,hk⟩ := ((IsElementaryAbelian.isPGroup 2 W).to_le
      (show U ≤ W from inf_le_left)).exists_card_eq
    change rank U = 3 at hrU
    rw [rank,hk,Nat.log_pow Nat.one_lt_two] at hrU
    simpa [hrU] using hk
  have hWcard := (D.sourceOrbit_m24_centralizer_commutator_series h hmany hV hq hnon a E hE z hz hne).1
  have hnot : ¬ commutatorSpace L W z ≤ U := by
    intro hh
    have hc := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    rw [hUcard,hWcard] at hc
    omega
  let A := W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let QM := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨_,_,_,hker,_⟩ := selected_core_actor_data s D.sourceOrbit_weakClosure_setup
  have hAU : A ⊓ centralizer (W : Set G) = U := hker.trans hUZ.symm
  have hcap : A ⊓ QM = U := le_antisymm
    ((inf_le_inf_left A (show QM ≤ centralizer (D.sourceOrbit : Set G) from hV ▸ D.core_centralizes)).trans hAU.le)
    (le_inf (hAU.ge.trans inf_le_left) (inf_le_left.trans (show D.sourceOrbit ≤ QM from hV ▸ D.le_core)))
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro u hu x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hu)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hconj : (commutatorSpace L W z).map (MulAut.conj i.val⁻¹).toMonoidHom ≤ A := by
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨mem_map_of_mem _ (hVzB hv).1,
      (mem_normalizer_iff.mp (hIP (I.inv_mem i.property)) v).mp (hVzB hv).2⟩
  exact ⟨hzU,hVzB,hnot,sourceClosure_not_le_of_crossing L W U A QM z i.val⁻¹
    z.property hzU D.sourceOrbit_component_normalizes (hIC (I.inv_mem i.property)) hcap hconj hnot⟩

/-- The marked original cocode constructs its selected-pair crossing;
no crossing, incidence or point-core containment is an extra premise. -/
theorem sourceOrbit_m24_centralizer_closure_crossing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ¬ (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨g,hg,hAT,rest⟩ := D.sourceOrbit_m24_exists_normalized_pair h hmany hV hq hnon a E hE
  obtain ⟨H,I,i,S,_,_,_,_,s,_,_,_,hUZ,_⟩ := rest
  exact (D.sourceOrbit_m24_selected_point_crossing h hmany hV hq hnon a E hE
    hg hAT s hUZ z hz hne).2.2.2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource Chapter8.Section02.Centralizer
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- Crossing fills the full local core modulo O₂(LT), retaining the full
original core in the denominator. -/
theorem sourceOrbit_m24_centralizer_closure_join_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  exact point_closure_join_core L D.sourceOrbit T z
    (D.sourceOrbit_m24_le_centralizer_residual h hmany hV hq hnon a E hE z hz hne).2.2
    (hV ▸ D.le_core)
    (D.sourceOrbit_m24_centralizer_closure_local_containment h hmany hV hq hnon a E hE z hz hne).2
    (D.sourceOrbit_m24_centralizer_closure_crossing h hmany hV hq hnon a E hE z hz hne)
    (D.sourceOrbit_m24_centralizer_core_interval h hmany hV hq hnon a E hE z hz hne)

/-- The two full cores commute modulo the original involution line on
O₂(L_z); their intersections with the original V are exactly V_z. -/
theorem sourceOrbit_m24_centralizer_module_core_intersections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ (centralizer ({(z : G)} : Set G)).pCoreIn 2,
      localTwoCore L z⁆ ≤ zpowers (z : G) ∧
      D.sourceOrbit ⊓ (centralizer ({(z : G)} : Set G)).pCoreIn 2 =
        commutatorSpace L D.sourceOrbit z ∧
      D.sourceOrbit ⊓ (sourceClosure L D.sourceOrbit z).map
        (centralizer ({(z : G)} : Set G)).subtype = commutatorSpace L D.sourceOrbit z := by
  obtain ⟨_,_,_,_,_,_,_,_,hQM,_⟩ :=
    D.sourceOrbit_m24_cocode_block_structure h hmany hV hq hnon a E hE
  obtain ⟨hEc,hcomm,_⟩ :=
    D.sourceOrbit_m24_centralizer_closure_core h hmany hV hq hnon a E hE z hz hne
  have hjoin := D.sourceOrbit_m24_centralizer_closure_join_core h hmany hV hq hnon a E hE z hz hne
  have hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) :=
    fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  have hc := point_core_intersection_commutator L D.sourceOrbit T z hTC hQM hcomm hjoin
  have hEcore : (sourceClosure L D.sourceOrbit z).map (centralizer ({(z : G)} : Set G)).subtype ≤
      (centralizer ({(z : G)} : Set G)).pCoreIn 2 := map_mono hEc
  exact ⟨hc,point_module_core_intersections L D.sourceOrbit T z D.sourceOrbit_component_normalizes
    (hV ▸ D.le_core) hEcore hc
    (D.sourceOrbit_m24_centralizer_fixed_modulo_line h hmany hV hq hnon a E hE z hz hne)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
