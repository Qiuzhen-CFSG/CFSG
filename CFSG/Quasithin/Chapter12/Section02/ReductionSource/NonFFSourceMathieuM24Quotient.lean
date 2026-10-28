module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Section
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuParabolicQuotient
public import Theory.GroupTheory.PResidual.PerfectImage
public import GorensteinWalter.PSL2PerfectOfCard
-- Continue the original native marking without changing its public boundary.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Component

/-!
# Marking the original M24 pair in H/O₂(H)

For the same Sylow-positioned offender and compatible selected pair, the
native trio commutators generate B=V∩O₂(I). This identifies the full kernel
of I in H/O₂(H) as O₂(I), proves |V⁺|=4, and marks I⁺ as PSL₂(4).
Perfectness then places I⁺ in the actual O²(H/O₂(H)). These are the two
source inputs required by the unitary Sylow-center placement; neither
is assumed in the chosen-module application.

The pair is supplied by sourceOrbit_m24_exists_canonical_component.
The quotient sieve, T-normalization, other Mathieu rows and ambient J4
recognition remain with qt-d-1222-nonff-mathieu. Source: Aschbacher--Smith,
8.2.9, cocode paragraph, printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original pair factor is exactly the residual displacement of the original orbit. -/
theorem sourceOrbit_m24_pair_factor_commutator
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
    B = ⁅R,D.sourceOrbit⁆ := by
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
  exact MathieuTrio.pair_factor_eq_commutator W R B inf_le_left hRW hWB hdim F f hf hFR

/-- The original pair embeds into the original H quotient with the exact core kernel. -/
theorem sourceOrbit_m24_pair_parabolic_quotient
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
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    D.sourceOrbit ⊓ I.pCoreIn 2 = D.sourceOrbit ⊓ H.pCoreIn 2 ∧
      Nat.card ((D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 4 ∧
      I.pCoreIn 2 = I ⊓ H.pCoreIn 2 ∧
      ∃ e : (I ⧸ pCore 2 I) ≃*
        ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))),
        ∀ x : I, (e (QuotientGroup.mk' (pCore 2 I) x)).val =
          QuotientGroup.mk' (pCore 2 H) (inclusion s.family.le_ambient x) := by
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hz)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  obtain ⟨_,_,_,_,hn,hcomm,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  obtain ⟨_,hTU,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many h hmany hV hq hnon a E hE hg hAT
  have hspan := D.sourceOrbit_m24_pair_factor_commutator h hmany hV hq hnon a E hE hg hAT s hUZ
  obtain ⟨hinter,hfour,hcore⟩ := MathieuPair.selected_two_hstar_core_intersection s hH hIC
    D.sylow_normalizes_component hTU hcomm hspan
  exact ⟨hinter,hfour,hcore,MathieuPair.selected_two_pair_core_quotient s
    (hinter ▸ inf_le_right)⟩


/-- The literal pair image is PSL₂(4) and lies in the literal two-residual. -/
theorem sourceOrbit_m24_pair_parabolic_residual
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
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Nonempty (((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≃*
      BenderSuzuki.Converse.PSL2 (BenderSuzuki.PFAppendixIII.BinaryGaloisField 2)) ∧
      (I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ≤
        pResidual 2 (H ⧸ pCore 2 H) := by
  obtain ⟨_,_,_,e,_⟩ := D.sourceOrbit_m24_pair_parabolic_quotient
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  obtain ⟨eI⟩ := MathieuPair.selected_two_quotient s
  let b := e.symm.trans eI
  let Q := (I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  let : Group.IsPerfect (BenderSuzuki.Converse.PSL2
      (BenderSuzuki.PFAppendixIII.BinaryGaloisField 2)) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by
      rw [show Nat.card (BenderSuzuki.PFAppendixIII.BinaryGaloisField 2) = 4 from
        GaloisField.card 2 2 (by decide)]
      decide)
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have hr := map_pResidual_le 2 Q.subtype
  rw [pResidual_eq_top_of_isPerfect,←MonoidHom.range_eq_map,range_subtype] at hr
  exact ⟨⟨b⟩,hr⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
