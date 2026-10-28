module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeParabolic
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeRotation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeNatural

/-!
# The actual quintic tensor action of the original M24-code pair

Natural hexacode recovery and the full product kernel are constructed on
one original selected pair. Its core quotient is the sum of two hexacode
copies, so commuting with the residual action gives the faithful F₄
multiplicity plane. Strong quasithinness of the literal four-space
normalizer excludes the cubic quotient and selects D10. The original
parabolic and containing-component data are retained on the same pair.
Actual quintic and residual cubic actors are constructed through the
full two-core kernels, with fixed-point-free action on the same P/U.

Source: Aschbacher--Smith 8.2.8(3--6), printed pp.718--719,
refs/quasithin.pdf. Native code attribution: LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.ParabolicReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_m24_code_tensor_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let R := localResidual L U
      let P := I.pCoreIn 2
      let B := D.sourceOrbit ⊓ P
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 6 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧ H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      ⁅(pResidual 2 H).map H.subtype,R⁆ ≤ R.pCoreIn 2 ∧
      R.pCoreIn 2 ⊔ U ≤ H.pCoreIn 2 ∧
      primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 ∧ generationParameter H ≤ 2 ∧
      (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U ∧
      B ⊔ A = P ∧ B ⊓ A = U ∧
      B.map (MulAut.conj i.val⁻¹).toMonoidHom = A ∧
      U.map (MulAut.conj i.val⁻¹).toMonoidHom = U ∧
      (∃ _hU : (U.subgroupOf I).Normal,
        centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I) ∧
      (∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
        IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
        Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^12 ∧
        Nat.card (I.pCoreIn 2) = 2^16 ∧
        let q := QuotientGroup.mk' (U.subgroupOf P)
        (B.subgroupOf P).map q ⊔ (A.subgroupOf P).map q = ⊤ ∧
        (B.subgroupOf P).map q ⊓ (A.subgroupOf P).map q = ⊥ ∧
        rank ((B.subgroupOf P).map q) = 6 ∧
        rank ((A.subgroupOf P).map q) = 6) ∧
      CodePairProductAction R I D.sourceOrbit U ∧
      CodePairNaturalAction R I D.sourceOrbit U i ∧
      CodePairMultiplicityAction R I D.sourceOrbit U i ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5) ∧
      (∃ hYP : R ⊔ I ≤ normalizer (P : Set G),
        ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
          ∃ hUP : (U.subgroupOf P).Normal, letI := hUP
            ∃ x : I, orderOf x = 5 ∧
              orderOf (QuotientGroup.mk' (pCore 2 I) x) = 5 ∧
              ∀ w, Chapter8.Section02.Normalizer.SmallOvergroups.sectionAction (R ⊔ I) P U hYP hYU
                (inclusion le_sup_right x) w = w → w = 1) ∧
      (∃ hYP : R ⊔ I ≤ normalizer (P : Set G),
        ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
          ∃ hUP : (U.subgroupOf P).Normal, letI := hUP
            ∃ (eR : (R ⧸ pCore 2 R) ≃* Atlas.Codes.HexEvenAutomorphisms) (z : R),
              orderOf z = 3 ∧
              eR (QuotientGroup.mk' (pCore 2 R) z) = Atlas.Codes.hexEvenZ ∧
              QuotientGroup.mk' (pCore 2 R) z ∈ center (R ⧸ pCore 2 R) ∧
              (∀ w, Chapter8.Section02.Normalizer.SmallOvergroups.sectionAction (R ⊔ I) P U hYP hYU
                (inclusion le_sup_left z) w = w → w = 1) ∧
              ∀ b : I, Commute
                (Chapter8.Section02.Normalizer.SmallOvergroups.sectionAction (R ⊔ I) P U hYP hYU
                  (inclusion le_sup_left z))
                (Chapter8.Section02.Normalizer.SmallOvergroups.sectionAction (R ⊔ I) P U hYP hYU
                  (inclusion le_sup_right b))) ∧
      ∃ hHR : H ≤ normalizer (R : Set G),
        pResidual 2 H ≤ ((pCoreJoinAction 2 hHR).comp (inclusion le_sup_right)).ker ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
          normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
          R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
          R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hu,hUT,hTU,hmodel,hcomm,hRI,hRP,
    hgen,hHN,hres,hresR,hcore,h3,h5,hn,hcenter,hjoin,hmeet,hBA,hUU,hIK,hsec,hrest⟩ :=
    D.sourceOrbit_m24_code_core_pair_of_many h hmany hV hq hnon a E hE hH
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let U := W ⊓ centralizer (A : Set G)
  let R := localResidual L U
  obtain ⟨c,hRB,hRU,hBU,eB,heB,eR,heR,hk⟩ :=
    D.sourceOrbit_m24_code_natural_section h hmany hV hq hnon a E hE s hw hfix hr hu
  let := hBU
  have hA := (selected_offender_of_parameter_bound s D.sourceOrbit_weakClosure_setup
    (by rw [hw]; rfl)).2.2.1
  change A = W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 at hA
  have hc : ⁅R,I⁆ ≤ R.pCoreIn 2 :=
    (commutator_mono le_rfl hIC).trans hcomm
  have hp : CodePairProductAction R I W U :=
    selected_code_full_product_action s hfix hIC (hA ▸ hr) hu hRI hRU hc hRB hBU hk
  have hnat : CodeNaturalSectionAction R (W ⊓ I.pCoreIn 2) U :=
    ⟨hRB,hRU,hBU,eB,eR,heR⟩
  have hpair : CodePairNaturalAction R I W U i :=
    selected_code_natural_pair_action s hp hnat hc
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 W).to_le inf_le_left,rfl⟩
  have hYN : R ⊔ I ≤ normalizer (U : Set G) :=
    sup_le hRU (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hY3 : primeRank 3 (R ⊔ I : Subgroup G) ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hYN)
      (inclusion_injective hYN)).trans
      ((h.simpleQTKE.twoLocal_sqtk hlocal).stronglyQuasithin 3 (by decide) (by decide))
  obtain ⟨hm,hD⟩ := selected_code_multiplicity_quintic s hp hpair hc hY3
  exact ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hu,hUT,hTU,hmodel,hcomm,hRI,hRP,
    hgen,hHN,hres,hresR,hcore,h3,h5,hn,hcenter,hjoin,hmeet,hBA,hUU,hIK,hsec,
    hp,hpair,hm,hD,code_pair_quintic_rotation hm hD,code_pair_cubic_actor hp hpair,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
