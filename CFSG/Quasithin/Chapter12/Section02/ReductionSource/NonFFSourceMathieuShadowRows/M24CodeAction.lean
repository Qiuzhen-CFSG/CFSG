module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeCore
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.Actions
public import Theory.ElementaryAbelian.Quotient

/-!
# The original M24-code pair as an actual binary quotient action

For the selected degree-one pair, conjugation by Y = L_U I acts on the
literal P/U, where P = O₂(I). The restriction to I has kernel O₂(I), and
the original B/U embeds equivariantly for L_U. The actual inverse selected
conjugator supplies bijective two-copy coordinates on P/U. The dimensions
are twelve and six; no native module marking or tensor action is assumed.

Source: Aschbacher--Smith, E.2.10, E.2.14 and 8.2.8(4--5), printed
pp.222--226,718--719, refs/quasithin.pdf. This constructs the actions used
in the later code exclusion on the same original orbit and selected pair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.TensorRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Original-pair conjugation, its full I-kernel, and the literal two summands. -/
theorem sourceOrbit_m24_code_action_pair_of_many
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
      let Y := R ⊔ I
      letI : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le
        (show B ≤ D.sourceOrbit from inf_le_left)
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      I ≤ centralizer (U : Set G) ∧
      rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      ⁅R,I⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧ primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 ∧
      ∃ (hUN : (U.subgroupOf P).Normal)
        (hel : IsElementaryAbelian 2 (P ⧸ U.subgroupOf P))
        (hYP : Y ≤ normalizer (P : Set G))
        (hYU : Y ≤ normalizer (U : Set G))
        (hRB : R ≤ normalizer (B : Set G)),
        letI := hUN
        letI := hel
        let ρ := sectionRepresentation Y P U hYP hYU
        let σ := sectionRepresentation R B U hRB ((localResidual_le L U).trans inf_le_right)
        ((ρ.comp (inclusion (show I ≤ Y from le_sup_right))).ker = pCore 2 I) ∧
        Function.Bijective (codePairMap I D.sourceOrbit U ρ
          (inclusion (show I ≤ Y from le_sup_right) i⁻¹)) ∧
        (∀ r b, intersectionInclusion I D.sourceOrbit U (σ r b) =
          ρ (inclusion (show R ≤ Y from le_sup_left) r)
            (intersectionInclusion I D.sourceOrbit U b)) ∧
        Module.finrank (ZMod 2) (CoreSection I U) = 12 ∧
        Module.finrank (ZMod 2) (IntersectionSection I D.sourceOrbit U) = 6 ∧
        Nat.card P = 2^16 := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hu,hUT,hTU,hmodel,hcomm,hRI,hRP,
    hgen,hHN,hres,hresR,hcore,h3,h5,hn,hcenter,hjoin,hmeet,hBA,hUU,hIker,
    ⟨hUN,hel,hcard,hPcard,hfactors⟩,hrest⟩ :=
    D.sourceOrbit_m24_code_core_pair_of_many h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let P := I.pCoreIn 2
  let B := D.sourceOrbit ⊓ P
  let Y := R ⊔ I
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le
    (show B ≤ D.sourceOrbit from inf_le_left)
  let := hUN
  let := hel
  have hIP : I ≤ normalizer (P : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hYP : Y ≤ normalizer (P : Set G) := sup_le hRP hIP
  have hRU : R ≤ normalizer (U : Set G) := (localResidual_le L U).trans inf_le_right
  have hYU : Y ≤ normalizer (U : Set G) :=
    sup_le hRU (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hRB : R ≤ normalizer (B : Set G) :=
    (le_inf ((localResidual_le L U).trans inf_le_left |>.trans
      D.sourceOrbit_component_normalizes) hRP).trans inf_normalizer_le_normalizer_inf
  have hA := (selected_offender_of_parameter_bound s D.sourceOrbit_weakClosure_setup
    (by rw [hw]; rfl)).2.2.1
  change A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ P at hA
  have hBcard := selected_intersection_quotient_card s U hfix 6 (hA ▸ hr)
  have hdimP : Module.finrank (ZMod 2) (CoreSection I U) = 12 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := CoreSection I U)
    rw [Nat.card_zmod] at hh
    change Nat.card (P ⧸ U.subgroupOf P) = _ at hh
    rw [hcard] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hh).symm
  have hdimB : Module.finrank (ZMod 2) (IntersectionSection I D.sourceOrbit U) = 6 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := IntersectionSection I D.sourceOrbit U)
    rw [Nat.card_zmod] at hh
    change Nat.card (B ⧸ U.subgroupOf B) = _ at hh
    rw [hBcard] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hh).symm
  refine ⟨I,i,S,s,hfix,hIC,hu,hTU,hmodel,
    (commutator_mono (le_refl R) hIC).trans hcomm,hRI,hgen,h3,h5,
    hUN,hel,hYP,hYU,hRB,
    selected_sectionRepresentation_kernel s U Y hfix hYP hYU le_sup_right,
    selected_codePairMap_bijective s U Y hfix hIC hYP hYU le_sup_right,
    ?_,hdimP,hdimB,hPcard⟩
  intro r b
  change quotientInclusion P B U inf_le_right
    (sectionRepresentation R B U hRB hRU r b) =
      (sectionRepresentation Y P U hYP hYU).comp (inclusion le_sup_left) r
        (quotientInclusion P B U inf_le_right b)
  rw [sectionRepresentation_comp]
  exact quotientInclusion_equivariant R P B U inf_le_right
    (le_sup_left.trans hYP) hRB (le_sup_left.trans hYU) r b

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
