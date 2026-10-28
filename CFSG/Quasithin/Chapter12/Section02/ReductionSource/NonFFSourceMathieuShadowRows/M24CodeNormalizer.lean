module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeRanks
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.CodeNormalizer
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The normalizer of the original M24-code fixed four-space

The same rank-six offender and selected pair give a four-dimensional fixed
subgroup U. Conjugated whole-code coordinates mark U by the native sextet
space. Restricting the original component action identifies its literal
relative normalizer and both distinct kernels, including the cubic factor
in the pointwise kernel. Its residual has the full quotient 3.A6.

All marking, kernel and local characteristic-two inputs are constructed from
the original Chapter12 hypotheses and the already selected rank-six pair.
Source: Aschbacher--Smith 8.2.5--6, printed pp.716--717, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter7.NormalizedSource.MathieuShadowRows
open Chapter8.Section02.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Transport the original code fixed subgroup to its native sextet space
and identify both kernels of its literal component normalizer. -/
theorem sourceOrbit_m24_code_normalizer_of_sextet
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    (A : Subgroup G) (hAN : A ≤ normalizer (D.sourceOrbit : Set G))
    (c : M24) (hc : ((inducedAutomizer D.sourceOrbit A).map a.toMonoidHom).map
      (MulAut.conj c).toMonoidHom = SextetCore.core) :
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let N := L ⊓ normalizer (U : Set G)
    (∀ w : D.sourceOrbit, (w : G) ∈ U ↔
      codeRepresentation c (E (Additive.ofMul w)) ∈ CodeFlags.sextetCodeSpace standardSextet) ∧
    ∃ f : N →* sextetStabilizer standardSextet,
      Function.Surjective f ∧
      f.ker = (pCore 2 L).comap (inclusion (show N ≤ L from inf_le_left)) ∧
      (∀ l, (f l).val = c * a (D.mathieuComponentAutomizer ⟨l,l.property.1⟩) * c⁻¹) ∧
      ((sextetPartPerm standardSextet).comp f).ker =
        (centralizer (U : Set G)).subgroupOf N := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (A : Set G)
  let B := inducedAutomizer W A
  let F := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (codeRepresentation.asGroupHom c))
  let p : Automizer W →* M24 := (MulAut.conj c).toMonoidHom.comp a.toMonoidHom
  have hF (b : Automizer W) (v : Additive W) :
      F (automizerRepresentation W b v) = codeRepresentation (p b) (F v) := by
    change codeRepresentation c (E (automizerRepresentation W b v)) =
      codeRepresentation (c * a b * c⁻¹) (codeRepresentation c (E v))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hfix : (fixedSpace (automizerRepresentation W) B).map F.toLinearMap =
      CodeFlags.sextetCodeSpace standardSextet := by
    rw [fixedSpace_map_equivariant _ _ p F hF]
    change fixedSpace codeRepresentation (B.map ((MulAut.conj c).toMonoidHom.comp a.toMonoidHom)) = _
    rw [←map_map,hc]
    exact CodeFlags.sextetCore_fixedSpace standardSextet
  have hspace (w : W) : (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ CodeFlags.sextetCodeSpace standardSextet := by
    rw [←hfix]
    constructor
    · intro hw
      exact ⟨Additive.ofMul w,(mem_fixedSpace_inducedAutomizer W A hAN _).mpr hw.2,rfl⟩
    · rintro ⟨v,hv,he⟩
      have hvw : v = Additive.ofMul w := F.injective he
      rw [hvw] at hv
      exact ⟨w.property,(mem_fixedSpace_inducedAutomizer W A hAN _).mp hv⟩
  let q : L →* M24 := p.comp D.mathieuComponentAutomizer
  have hqsur : Function.Surjective q := (MulAut.conj c).surjective.comp
    (a.surjective.comp (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inr hq)))
  have hqker : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ ((MulAut.conj c).injective.comp a.injective)]
    exact D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq)
  obtain ⟨f,hf,hk,hval,hpoint⟩ := CodeNormalizer.marked_normalizer_action W L U
    D.sourceOrbit_component_normalizes inf_le_left q hqsur F
    (fun l w => hF (D.mathieuComponentAutomizer l) (Additive.ofMul w)) standardSextet hspace
  rw [hqker] at hk
  exact ⟨hspace,f,hf,hk,hval,hpoint⟩

/-- The original rank-six pair constructs the code four-space two-local
and its component residual with the full triple-A6 quotient. -/
theorem sourceOrbit_m24_code_normalizer_pair_of_many
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
      let N := L ⊓ normalizer (U : Set G)
      let R := localResidual L U
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 6 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsTwoLocal (normalizer (U : Set G)) ∧ HasCharacteristicTwo (normalizer (U : Set G)) ∧
      (R.subgroupOf (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      ∃ (c : M24) (f : N →* sextetStabilizer standardSextet)
        (r : R →* sextetStabilizer standardSextet),
        ((inducedAutomizer D.sourceOrbit A).map a.toMonoidHom).map
          (MulAut.conj c).toMonoidHom = SextetCore.core ∧
        (∀ w : D.sourceOrbit, (w : G) ∈ U ↔
          codeRepresentation c (E (Additive.ofMul w)) ∈ CodeFlags.sextetCodeSpace standardSextet) ∧
        Function.Surjective f ∧
        f.ker = (pCore 2 L).comap (inclusion (show N ≤ L from inf_le_left)) ∧
        (∀ l, (f l).val = c * a (D.mathieuComponentAutomizer ⟨l,l.property.1⟩) * c⁻¹) ∧
        ((sextetPartPerm standardSextet).comp f).ker = (centralizer (U : Set G)).subgroupOf N ∧
        r.range = solvableResidual (sextetStabilizer standardSextet) ∧ IsPGroup 2 r.ker ∧
        (pCore 2 R).map r = (SextetLayers.CoordinateTransport.nativeQuotient standardSextet).ker ∧
        ∀ x, r x = f (inclusion (localResidual_le L U) x) := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hcentral,hr,hU,hcor,hUT,hTU,c,hc⟩ :=
    D.sourceOrbit_m24_code_rank_six_pair_of_many h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let N := L ⊓ normalizer (U : Set G)
  obtain ⟨hspace,f,hf,hfk,hval,hpoint⟩ :=
    D.sourceOrbit_m24_code_normalizer_of_sextet h hmany hV hq hnon a E hE A inf_le_right c hc
  have hk : IsPGroup 2 f.ker := by
    rw [hfk]
    exact (pCore_isPGroup (p := 2)).comap_of_injective _ (inclusion_injective _)
  obtain ⟨e⟩ := CodeNormalizer.marked_residual_quotient L U standardSextet f hf hk
  have hcomponent := CodeNormalizer.marked_residual_component L U e
  obtain ⟨r,hrange,hrker,hrcore,hrval⟩ :=
    CodeNormalizer.marked_residual_core_action L U standardSextet f hf hk
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hU
    rw [hz,Representation.BinaryOffender.rank_bot] at hU
    omega
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le inf_le_left,rfl⟩
  have hlocalOver : normalizer (U : Set G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hlocal,hTU⟩
  have hchar : HasCharacteristicTwo (normalizer (U : Set G)) :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h.simpleQTKE.evenCharacteristic T) hlocalOver)
  exact ⟨I,i,S,s,hw,hOff,hfix,hker,hcentral,hr,hU,hUT,hTU,hlocal,hchar,
    hcomponent,⟨e⟩,c,f,r,hc,hspace,hf,hfk,hval,hpoint,hrange,hrker,hrcore,hrval⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
