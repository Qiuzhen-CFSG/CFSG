module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Component
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneComponents

/-!
# The actual normal component at the M24 cocode three-space

For the original offender plane U, set R = N_L(U)^∞. Its two-core quotient
is GL3(2), and source 1.2.4 supplies a containing normal C-component K of
N_G(U). Every original outside H-star group has generation parameter two,
hence is nonsolvable. The radical argument therefore makes K/O2(K)
quasisimple. The full action of R on U identifies K with R, and the source
commutator argument gives [R,C_G(U)] ≤ O2(R).

The final theorem retains the same Sylow-positioned offender and compatible
pair inside the original H-star group. The recognized residual normalizes
that pair and its literal two-core, preserving its center U, elementary
central quotient of order 2^12 and full core of order 2^15.

This proves the cocode instance of 8.2.6--7 and 8.2.8(1,2), with the pair
normalization used in (4). It does not assert the tensor or full section
kernel of (4,5), the other Mathieu rows, or the ambient J4 isomorphism;
these remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith, printed pp.717--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original M24 cocode residual is the normal C-component of N_G(U),
with its full action, exact two-core, and centralizer commutator retained. -/
theorem sourceOrbit_m24_fixedPlane_component_recognition
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
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    let R := localResidual L U
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      R.pCoreIn 2 = R ⊓ centralizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* BinaryLinear.GL Vector) ∧
      (R.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
      normalizer (U : Set G) ≤ normalizer (R : Set G) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      SmallOvergroups.actionImage R U = ⊤ := by
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  let N := normalizer (U : Set G)
  let R := localResidual L U
  let H := L ⊓ N
  let R₀ := solvableResidual H
  let b : R₀ ≃* R := R₀.equivMapOfInjective H.subtype H.subtype_injective
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨hs,_,K,hKN,hK,hRK,hNK⟩ := D.sourceOrbit_m24_fixedPlane_containing_component
    h hmany hV hq hnon a E hE hg hAT
  obtain ⟨hker,hR⟩ := D.sourceOrbit_m24_fixedPlane_residual_core h hmany hV hq hnon a E hE hg
  obtain ⟨hu,hTU,_⟩ := D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many
    h hmany hV hq hnon a E hE hg hAT
  obtain ⟨_,_,_,_,hgen,_⟩ := D.sourceOrbit_m24_cocode_geometry_of_many
    h hmany hV hq hnon a E hE hg
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 3 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hK.subgroupOf_of_le le_sup_left (sup_le hKN hTU),?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · exact ne_bot_of_le_ne_bot hUne
        (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
          ((show U ≤ D.sourceOrbit from inf_le_left).trans
            (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right))
          (sup_le hKN hTU))
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (BinaryLinear.GL Vector) :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.isSimpleGroup
  let : IsSimpleGroup (R ⧸ pCore 2 R) := hR.some.isSimpleGroup
  have hTR := normalizes_localResidual L U T D.sylow_normalizes_component hTU
  have hMR := normalizes_localResidual L U
    (normalizer (L : Set G) ⊓ N) inf_le_left inf_le_right
  have hquasi : IsQuasisimple (K ⧸ pCore 2 K) :=
    MathieuTrio.containing_component_quasisimple T (normalizer (L : Set G)) N R K
      hlocal (Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2)
      (hTU.trans hNK) hTR hRK hKN hMR (by
        intro J hJ hj
        let := hj
        have hn := hgen J hJ
        have hb := generationParameter_le_one_of_solvable (G := J)
        omega)
  let := hquasi
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKN).toMonoidHom) (subgroupOfEquivOfLe hKN).surjective
  have hnontriv : ¬ R ≤ centralizer (U : Set G) := by
    intro hc
    have he : R.pCoreIn 2 = R := hker.trans (inf_eq_left.mpr hc)
    have ht : pCore 2 R = ⊤ := by
      apply map_injective R.subtype_injective
      simpa only [pCoreIn,←MonoidHom.range_eq_map,range_subtype] using he
    have hp : IsPGroup 2 R := (ht ▸ (pCore_isPGroup (p := 2) (G := R))).of_equiv topEquiv
    let : Group.IsNilpotent R := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable (R ⧸ pCore 2 R) inferInstance
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
      ((hTU.trans hNK).trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hcomm := localResidual_centralizer_commutator L K U (T : Subgroup G)
    hRK hKN hNK hnontriv hQT D.sylow_normalizes_component hTU
  obtain ⟨_,e,π,_,hπ,_,_,ha,_⟩ := D.sourceOrbit_m24_fixedPlane_normalizer_action_of_many
    h hmany hV hq hnon a E hE hg
  let r : R →* BinaryLinear.GL Vector := (π.comp R₀.subtype).comp b.symm.toMonoidHom
  have hr : Function.Surjective r := hπ.comp b.symm.surjective
  have hRN : R ≤ N := (localResidual_le L U).trans inf_le_right
  have hact (x : R) (u : U) :
      (e (U.normalizerMonoidHom ⟨x,hRN x.property⟩ u)).toAdd = r x (e u).toAdd := by
    have hx : ((b.symm x).val : G) = x.val := congrArg Subtype.val (b.apply_symm_apply x)
    have hxe : (⟨((b.symm x).val : G),(b.symm x).val.property.2⟩ : N) =
      ⟨x,hRN x.property⟩ := Subtype.ext hx
    have hh := ha (b.symm x).val u
    rw [hxe] at hh
    exact hh
  have hfull := MathieuTrio.full_actionImage_of_linear_action R U hRN e r hr hact
  have heq := SmallOvergroups.localResidual_eq_of_quasisimple_actionImage L K U
    (T : Subgroup G) hRK hKN hQT D.sylow_normalizes_component hTU hnontriv
    (by rw [hfull]; exact le_top)
  exact ⟨hs,hker,hR,heq.symm ▸ hK,heq.symm ▸ hNK,hcomm,hfull⟩

/-- Construct the compatible canonical pair and the recognized normal
component on the same original Sylow-positioned fixed plane. -/
theorem sourceOrbit_m24_exists_canonical_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v))
    : ∃ g : G, IsWOffenderAt D.sourceOrbit (T : Subgroup G) g ∧
      offenderNormalizer D.sourceOrbit g ≤ T ∧
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    let R := localResidual L U
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      R.pCoreIn 2 = R ⊓ centralizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* BinaryLinear.GL Vector) ∧
      (R.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
      normalizer (U : Set G) ≤ normalizer (R : Set G) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      SmallOvergroups.actionImage R U = ⊤ ∧
    ∃ (H I : Subgroup G) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
      H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      generationParameter H = 2 ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S ∧
      I ⊔ (T : Subgroup G) = H ∧ I ≤ centralizer (U : Set G) ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      IsWOffenderAt D.sourceOrbit (T : Subgroup G) i.val⁻¹ ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ =
        D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2)) ∧
      I.pCoreIn 2 = (D.sourceOrbit ⊓ I.pCoreIn 2) ⊔
        (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) ∧
      (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U ∧
      (∃ _hU : (U.subgroupOf I).Normal,
        centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I) ∧
      ∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
        IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
        Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^12 ∧
        Nat.card (I.pCoreIn 2) = 2^15 := by
  obtain ⟨g,hg,hAT,hpair⟩ := D.sourceOrbit_m24_exists_canonical_core h hmany hV hq hnon a E hE
  obtain ⟨hs,hcore,hquot,hcomp,hn,hcomm,hfull⟩ :=
    D.sourceOrbit_m24_fixedPlane_component_recognition h hmany hV hq hnon a E hE hg hAT
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  let R := localResidual L U
  obtain ⟨H,I,i,S,hH,hHC,hHN,hrH,hgen,s,hIT,hIC,ho,ha,ht,hUZ,hUF,hIQ,hP,hZ,hCK,hsec⟩ := hpair
  have hRI : R ≤ normalizer (I : Set G) := by
    rw [←s.generate]
    exact normalizes_twoConjugate R D.sourceOrbit i.val
      (((localResidual_le L U).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
      (hn (Subgroup.centralizer_le_normalizer _ (hIC i.property)))
  have hRP : R ≤ normalizer (I.pCoreIn 2 : Set G) :=
    hRI.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  exact ⟨g,hg,hAT,hs,hcore,hquot,hcomp,hn,hcomm,hfull,H,I,i,S,
    hH,hHC,hHN,hrH,hgen,s,hIT,hIC,hRI,hRP,ho,ha,ht,hUZ,hUF,hIQ,hP,hZ,hCK,hsec⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
