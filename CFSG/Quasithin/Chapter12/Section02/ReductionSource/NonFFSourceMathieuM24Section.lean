module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Recognition
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrioMarking
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairSection
-- Continue the original component/plane marking without widening its API.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Component

/-!
# The actual M24 cocode pair's faithful joint section

For the same original offender U and selected pair I, native trio geometry
identifies B/U, where B=V∩O₂(I), with two natural three-dimensional modules.
The exact residual kernel O₂(R) then extends to P/U. The literal joint
conjugation action has kernel O₂(RI)=P O₂(R), and its faithful quotient is
the marked product of R/O₂(R) and I/P, namely GL₃(2) and PSL₂(4).

Selection, native markings and section kernels are proved inputs here;
no additional kernel callback remains. The concrete-factor application
uses the same selected pair supplied by the preceding canonical theorem. The four-copy residual action, joint
centralizer, T-normalization, other Mathieu rows and ambient J4 recognition
remain with qt-d-1222-nonff-mathieu. In particular no dimensionally invalid
tensor product with the whole six-dimensional B/U is asserted.
Source: Aschbacher--Smith H.15.6(3), 8.2.8(4), printed pp.401,718--719,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped MatrixGroups commutatorElement IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The same selected M24 pair has the literal two-natural-summand action
on B/U, with exact residual kernel O₂(R). -/
theorem sourceOrbit_m24_pair_section_natural
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
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    let R := localResidual L U
    let B := D.sourceOrbit ⊓ I.pCoreIn 2
    letI := IsElementaryAbelian.of_le (p := 2) (show B ≤ D.sourceOrbit from inf_le_left)
    (∀ r : R, (∀ b : B, ⁅(r : G),(b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R) ∧
      ∃ hRB : R ≤ normalizer (B : Set G), ∃ hRU : R ≤ normalizer (U : Set G),
        ∃ hUN : (U.subgroupOf B).Normal, letI := hUN
          ∃ (e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] (Vector × Vector))
            (π : R →* BinaryLinear.GL Vector),
            Function.Surjective π ∧ (sectionAction R B U hRB hRU).ker = pCore 2 R ∧
            ∀ (r : R) (z : B ⧸ U.subgroupOf B),
              e (Additive.ofMul (sectionAction R B U hRB hRU r z)) =
                (π r (e (Additive.ofMul z)).1,π r (e (Additive.ofMul z)).2) := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
  let R := localResidual L U
  let B := W ⊓ I.pCoreIn 2
  have hRL : R ≤ L := (localResidual_le L U).trans inf_le_left
  have hRU : R ≤ normalizer (U : Set G) := (localResidual_le L U).trans inf_le_right
  have hRW : R ≤ normalizer (W : Set G) := hRL.trans D.sourceOrbit_component_normalizes
  let : Group.IsPerfect R := Group.IsPerfect.map _
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hz)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  obtain ⟨_,hcore,_,_,hn,hcomm,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  have hRI : R ≤ normalizer (I : Set G) := by
    rw [←s.generate]
    exact normalizes_twoConjugate R W i.val hRW
      (hn (Subgroup.centralizer_le_normalizer _ (hIC i.property)))
  have hRP : R ≤ normalizer (I.pCoreIn 2 : Set G) :=
    hRI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hRB : R ≤ normalizer (B : Set G) := (le_inf hRW hRP).trans inf_normalizer_le_normalizer_inf
  have hWB : ⁅R,W⁆ ≤ B := MathieuPair.residual_commutator_le_pair_factor R I W
    (s.generate ▸ le_sup_left) hRI ((hIC.trans (Subgroup.centralizer_le_normalizer _)).trans hn)
    hRW ((commutator_mono le_rfl hIC).trans hcomm)
  have hdim : rank B = 9 := MathieuPair.selected_two_intersection_rank s
    ((Chapter7.log_card_eq_finrank W).trans (E.finrank_eq.trans MathieuCode.finrank_cocode))
  obtain ⟨q,F,hqsur,_,hF,hplane⟩ := D.fixedPlane_marking h hmany hV hq hnon a E hE hg
  obtain ⟨f,hf,hfmark⟩ := MathieuTrio.plane_residual_marking W L U
    D.sourceOrbit_component_normalizes inf_le_left q hqsur F hF hplane
  have hFR (r : R) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom ⟨r,hRW r.property⟩ w)) =
        cocodeRepresentation (f r).val (F (Additive.ofMul w)) := by
    rw [hfmark]
    exact hF (inclusion hRL r) w
  have hpair := MathieuTrio.pair_space_marking W R B inf_le_left hRW hWB hdim F f hf hFR
  have hk := MathieuTrio.marked_pair_section_kernel W B U R inf_le_left inf_le_left hRB hRW
    hcore F f hFR hpair hplane
  obtain ⟨hUN,e,π,hπ,hker,_,he⟩ := MathieuTrio.marked_pair_section_natural W B U R
    inf_le_left inf_le_left hRB hRW hRU hcore F f hf hFR hpair hplane
  exact ⟨hk,hRB,hRU,hUN,e,π,hπ,hker,he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- On the original compatible pair, the full joint section kernel is
O₂(RI)=O₂(I)O₂(R), and the faithful quotient is the marked product of the
original two-core quotients. No section-kernel premise remains. -/
theorem sourceOrbit_m24_pair_joint_section
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
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    let R := localResidual L U
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
          f.ker = pCore 2 Y ∧ Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
          (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
          (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
          ∃ e : (Y ⧸ pCore 2 Y) ≃* (R ⧸ pCore 2 R) × (I ⧸ pCore 2 I),
            ∀ (r : R) (a : I), e (QuotientGroup.mk' (pCore 2 Y)
              (inclusion le_sup_left r * inclusion le_sup_right a)) =
              (QuotientGroup.mk' (pCore 2 R) r, QuotientGroup.mk' (pCore 2 I) a) := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
  let R := localResidual L U
  have hRU : R ≤ normalizer (U : Set G) := (localResidual_le L U).trans inf_le_right
  have hRW : R ≤ normalizer (W : Set G) :=
    ((localResidual_le L U).trans inf_le_left).trans D.sourceOrbit_component_normalizes
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hz)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  obtain ⟨_,_,_,_,hn,hcomm,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  have hRI : R ≤ normalizer (I : Set G) := by
    rw [←s.generate]
    exact normalizes_twoConjugate R W i.val hRW
      (hn (Subgroup.centralizer_le_normalizer _ (hIC i.property)))
  have hk := (D.sourceOrbit_m24_pair_section_natural h hmany hV hq hnon a E hE hg hAT s hUZ).1
  exact MathieuPair.selected_two_joint_section s R U hUZ hRI hRU hIC
    ((commutator_mono le_rfl hIC).trans hcomm) hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The faithful joint section on the original H-star pair, with both
concrete factors and their original quotient maps. Apply this to the pair
constructed by `sourceOrbit_m24_exists_canonical_component`. -/
theorem sourceOrbit_m24_pair_joint_section_concrete
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
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    let R := localResidual L U
    let Y := R ⊔ I
    ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : Y ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
          f.ker = pCore 2 Y ∧ Y.pCoreIn 2 = I.pCoreIn 2 ⊔ R.pCoreIn 2 ∧
          (f.comp (inclusion le_sup_left)).ker = pCore 2 R ∧
          (f.comp (inclusion le_sup_right)).ker = pCore 2 I ∧
          ∃ (eR : (R ⧸ pCore 2 R) ≃* BinaryLinear.GL Vector)
            (eI : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2))
            (e : (Y ⧸ pCore 2 Y) ≃* BinaryLinear.GL Vector × PSL2 (BinaryGaloisField 2)),
            ∀ (r : R) (b : I), e (QuotientGroup.mk' (pCore 2 Y)
              (inclusion le_sup_left r * inclusion le_sup_right b)) =
              (eR (QuotientGroup.mk' (pCore 2 R) r),eI (QuotientGroup.mk' (pCore 2 I) b)) := by
  obtain ⟨_,_,hquot,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  obtain ⟨eI⟩ := MathieuPair.selected_two_quotient s
  obtain ⟨hYP,hYU,hUP,hker,hcore,hR,hI,e,he⟩ :=
    D.sourceOrbit_m24_pair_joint_section h hmany hV hq hnon a E hE hg hAT s hUZ
  obtain ⟨eR⟩ := hquot
  refine ⟨hYP,hYU,hUP,hker,hcore,hR,hI,
    eR,eI,e.trans (eR.prodCongr eI),?_⟩
  intro r b
  change (eR.prodCongr eI) (e _) = _
  rw [he]
  rfl

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
