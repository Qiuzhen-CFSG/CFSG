module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeNormalizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetFactors
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.Representation.HexacodeAction.ThreeRank
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Component

/-!
# The containing component of the original M24-code normalizer

The relative normalizer residual retains its full triple-A6 quotient and
acts nontrivially on the same original fixed four-space. Its three-rank is
at least two. The nonquasisimple C-component alternatives have three-rank
at most one, so the containing component has quasisimple two-core quotient.
The resulting centralizer commutator bound makes the original residual,
and the containing component's two-core, normalize the same pair and core.

The original whole-code marking and H-star inputs construct every local
actor here; no component or normalizer conclusion is an added premise.
Source: Aschbacher--Smith 8.2.6--8, printed pp.717--719, and A.3.6,
refs/quasithin.pdf. This module proves the code-row instance of 8.2.7 and
the normalization deductions of 8.2.8(2), not the later tensor exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem code_residual_moves
    (U : Subgroup G)
    (f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* sextetStabilizer standardSextet)
    (r : localResidual L U →* sextetStabilizer standardSextet)
    (hp : ((sextetPartPerm standardSextet).comp f).ker =
      (centralizer (U : Set G)).subgroupOf (L ⊓ normalizer (U : Set G)))
    (hr : r.range = solvableResidual (sextetStabilizer standardSextet))
    (hv : ∀ x, r x = f (inclusion (localResidual_le L U) x)) :
    ¬ localResidual L U ≤ centralizer (U : Set G) := by
  let : IsSimpleGroup (alternatingGroup (SextetPart standardSextet)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, card_sextetPart]; decide)
  obtain ⟨g,hg⟩ := exists_ne (1 : alternatingGroup (SextetPart standardSextet))
  obtain ⟨x,hx,hxg⟩ := MathieuSextet.residual_covers_even_parts standardSextet g
  obtain ⟨y,rfl⟩ := (show x ∈ r.range from hr.symm ▸ hx)
  intro hcentral
  have hk : inclusion (localResidual_le L U) y ∈
      ((sextetPartPerm standardSextet).comp f).ker := by
    rw [hp]
    exact hcentral y.property
  have he : sextetPartPerm standardSextet (r y) = 1 := by
    rw [hv]
    exact hk
  exact hg (Subtype.ext (hxg.symm.trans he))

private theorem code_overcomponent_quasisimple
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUne : U ≠ ⊥) (K : Subgroup G) (hKN : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hRK : localResidual L U ≤ K)
    (e : (localResidual L U ⧸ pCore 2 (localResidual L U)) ≃* Atlas.Codes.HexEvenAutomorphisms) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let N := normalizer (U : Set G)
  let C := K.subgroupOf N
  let k : C ≃* K := subgroupOfEquivOfLe hKN
  have hr : 2 ≤ primeRank 3 (localResidual L U) := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 (localResidual L U)) pCore_isPGroup,primeRank_congr 3 e]
    exact Hexacode.two_le_primeRank_even
  have hc : 2 ≤ primeRank 3 C := by
    rw [primeRank_congr 3 k]
    exact hr.trans (primeRank_mono 3 hRK)
  have hNH : N ∈ Chapter1.H G := ne_bot_of_le_ne_bot hUne
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U) U.le_normalizer le_rfl)
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  let b := cComponentTwoCoreQuotientEquiv hK
  have hb : 2 ≤ primeRank 3 (C.map (QuotientGroup.mk' (pCore 2 N))) := by
    rw [←primeRank_congr 3 b, primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 C) pCore_isPGroup]
    exact hc
  have hbar := ChapterA.Section03.cComponent_quasisimple_of_three_rank
    (Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hNH)
    (pCore_quotient_pCore_eq_bot 2) (hK.map_quotient (pCore 2 N)) hb
  let c : (C ⧸ pCore 2 C) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  exact hbar.of_mulEquiv (b.symm.trans c)

/-- The same original M24-code pair supplies a normal containing component
with quasisimple two-core quotient. Its actual relative normalizer residual
normalizes the pair and its core, and centralizes C_G(U) modulo its two-core. -/
theorem sourceOrbit_m24_code_component_pair_of_many
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
      ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
        (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
        normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hcentral,hr,hU,hUT,hTU,hloc,hchar,
    hcomponent,⟨e⟩,c,f,r,hc,hspace,hf,hfk,hval,hpoint,hrange,hrker,hrcore,hrval⟩ :=
    D.sourceOrbit_m24_code_normalizer_pair_of_many h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hU
    rw [hz,Representation.BinaryOffender.rank_bot] at hU
    omega
  obtain ⟨K,hKN,hK,hRK,hNK⟩ := D.fixed_overcomponent h.toHypothesis1221 U
    inf_le_left hUne hTU hcomponent
  have hquasi := code_overcomponent_quasisimple h.toHypothesis1221 U hUne K hKN hK hRK e
  let := hquasi
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKN).toMonoidHom) (subgroupOfEquivOfLe hKN).surjective
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
      ((hTU.trans hNK).trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hcomm := localResidual_centralizer_commutator L K U (T : Subgroup G)
    hRK hKN hNK (code_residual_moves U f r hpoint hrange hrval)
    hQT D.sylow_normalizes_component hTU
  obtain ⟨hpair,hcore⟩ := local_factor_normalizes_pair_and_core L K U I D.sourceOrbit
    (T : Subgroup G) i.val i.property s.generate hcentral hNK hQT
    D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes hcomm
  exact ⟨I,i,S,s,hw,hOff,hfix,hker,hcentral,hr,hU,hUT,hTU,⟨e⟩,hcomm,
    le_sup_left.trans hpair,le_sup_left.trans hcore,K,hKN,hK,hRK,hNK,hquasi,hQT,hpair,hcore⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
