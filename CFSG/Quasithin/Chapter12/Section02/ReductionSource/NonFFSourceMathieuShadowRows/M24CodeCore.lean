module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeParabolic
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CoreFactors

/-!
# The original M24-code core section

The actual selected degree-one pair has a rank-six offender and the
same four-dimensional fixed subgroup U. Transport E.2's two-conjugate
geometry to P = O₂(I): P/U is elementary of order 2^12, P has order 2^16,
and its centre is exactly U. The images of B = V ∩ P and the original
offender A are complementary rank-six factors, conjugate by the same
selected inverse conjugator. The action of I on this literal quotient
has full kernel O₂(I). All parabolic and containing-component data are
retained on that same pair for the later code tensor argument.

Source: Aschbacher--Smith E.2.10, E.2.13 and 8.2.8, printed
pp.222--225,718--719, refs/quasithin.pdf.
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

/-- The original M24-code pair has a rank-twelve elementary core section
with two complementary rank-six factors, core order 2^16, centre U,
and full two-core action kernel. -/
theorem sourceOrbit_m24_code_core_pair_of_many
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
      ∃ hHR : H ≤ normalizer (R : Set G),
        pResidual 2 H ≤ ((pCoreJoinAction 2 hHR).comp (inclusion le_sup_right)).ker ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
          normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
          R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
          R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hU,hUT,hTU,hmodel,hcomm,hRI,hRP,
    hgen,hHN,hres,hresR,hcore,h3,h5,hn,hrest⟩ :=
    D.sourceOrbit_m24_code_parabolic_pair_of_many h hmany hV hq hnon a E hE hH
  have hA := (selected_offender_of_parameter_bound s D.sourceOrbit_weakClosure_setup
    (by rw [hw]; rfl)).2.2.1
  change offenderNormalizer D.sourceOrbit i.val⁻¹ =
    D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 at hA
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
  have hcenter := selected_core_center_of_fixed s U hfix (by rw [←hA])
  obtain ⟨hjoin,hmeet,hBA,hUU⟩ := selected_core_factor_geometry s U hfix
  rw [←hA] at hjoin hmeet hBA
  obtain ⟨hUN,hel,hcard,hPcard⟩ :=
    selected_core_section_of_ranks s U hfix hIC 6 4 (hA ▸ hr) hU
  let := hUN
  have hfactors := selected_core_quotient_factors s U hfix 6 (hA ▸ hr)
  dsimp only at hfactors
  rw [←hA] at hfactors
  exact ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hU,hUT,hTU,hmodel,hcomm,hRI,hRP,
    hgen,hHN,hres,hresR,hcore,h3,h5,hn,hcenter,
    hjoin,hmeet,hBA,hUU,selected_core_action_kernel s U hfix,
    ⟨hUN,hel,hcard,hPcard,hfactors⟩,hrest⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
