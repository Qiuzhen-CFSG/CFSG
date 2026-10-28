module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeNormalizer
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeNatural
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# Natural hexacode coordinates on the original M24-code pair

The same selected rank-six offender marks the original four-space U and
its even intersection B in one set of whole-code coordinates. Recovery
identifies the literal B/U with the hexacode and intertwines the original
residual action with the genuine 3.A6 action. Its full kernel is O₂(R),
so the cubic centre is retained.

The internal import permits reduction of the original component-action
map when comparing representatives; no private name occurs in the public
statements. Source: Aschbacher--Smith H.16.1(3) and 8.2.8(4--5), printed
pp.402,718--719, refs/quasithin.pdf. Native code attribution is retained
in the imported recovery modules, see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open MathieuCode.SextetLayers.CoordinateTransport
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Natural hexacode recovery on a supplied original selected pair.
The rank-six offender and rank-four fixed subgroup are kept on that pair. -/
theorem sourceOrbit_m24_code_natural_section
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hw : globalW D.sourceOrbit (T : Subgroup G) = 1)
    (hfix : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hr : rank (inducedAutomizer D.sourceOrbit
      (offenderNormalizer D.sourceOrbit i.val⁻¹)) = 6)
    (hu : rank (D.sourceOrbit ⊓ centralizer
      (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) = 4) :
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let R := localResidual L U
      let B := D.sourceOrbit ⊓ I.pCoreIn 2
      ∃ (c : M24) (hRB : R ≤ normalizer (B : Set G))
        (hRU : R ≤ normalizer (U : Set G)) (hBU : (U.subgroupOf B).Normal),
        letI := hBU
        ∃ eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative hexacode,
          (∀ b : B, eB (QuotientGroup.mk' (U.subgroupOf B) b) =
            Multiplicative.ofAdd (NormalizedShadowRows.CodeSection.recover standardSextet
              (codeRepresentation c (E (Additive.ofMul ⟨b,b.property.1⟩))))) ∧
          ∃ eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms,
            (∀ (x : R) (b : B ⧸ U.subgroupOf B),
              eB (sectionAction R B U hRB hRU x b) =
                Multiplicative.ofAdd (hexAction
                  (eR (QuotientGroup.mk' (pCore 2 R) x)).val (eB b).toAdd)) ∧
            (sectionAction R B U hRB hRU).ker = pCore 2 R := by
  let A₀ := offenderNormalizer D.sourceOrbit i.val⁻¹
  let Abar := inducedAutomizer D.sourceOrbit A₀
  let : IsElementaryAbelian 2 Abar := offender_inducedAutomizer_elementary D.sourceOrbit i.val⁻¹
  let : IsElementaryAbelian 2 (Abar.map a.toMonoidHom) := IsElementaryAbelian.map _
  have hc0 := fixedCodim_inducedAutomizer D.sourceOrbit A₀
    (show A₀ ≤ normalizer (D.sourceOrbit : Set G) from inf_le_right)
  have ht := fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit)
    codeRepresentation a.toMonoidHom E hE Abar
  have hm := rank_map_injective a.toMonoidHom a.injective Abar
  have hv : rank D.sourceOrbit = 11 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans (E.finrank_eq.trans finrank_code)
  have hsum := offender_corank_add (W := D.sourceOrbit)
    (A := D.sourceOrbit ⊓ centralizer (A₀ : Set G)) (B := ⊥) bot_le inf_le_left
  have hsum' : rank D.sourceOrbit =
      subgroupCorank D.sourceOrbit (D.sourceOrbit ⊓ centralizer (A₀ : Set G)) +
        rank (D.sourceOrbit ⊓ centralizer (A₀ : Set G)) := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hsum
  change rank (D.sourceOrbit ⊓ centralizer (A₀ : Set G)) = 4 at hu
  have hcor : subgroupCorank D.sourceOrbit (D.sourceOrbit ⊓ centralizer (A₀ : Set G)) = 7 := by
    omega
  obtain ⟨c,hc⟩ := NormalizedShadowRows.CodeRank.sextet_marking (Abar.map a.toMonoidHom)
    (hm.trans hr) (by rw [←ht,hc0,hcor])
  obtain ⟨hspace,f,hf,hfk,hval,hpoint⟩ :=
    D.sourceOrbit_m24_code_normalizer_of_sextet h hmany hV hq hnon a E hE A₀ inf_le_right c hc
  have hkf : IsPGroup 2 f.ker := by
    rw [hfk]
    exact (pCore_isPGroup (p := 2)).comap_of_injective _ (inclusion_injective _)
  obtain ⟨r,hrange,hrker,hrcore,hrval⟩ :=
    Chapter7.NormalizedSource.MathieuShadowRows.CodeNormalizer.marked_residual_core_action L
      (D.sourceOrbit ⊓ centralizer (A₀ : Set G)) standardSextet f hf hkf
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let U := W ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let B := W ⊓ I.pCoreIn 2
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
  have hA := (selected_offender_of_parameter_bound s D.sourceOrbit_weakClosure_setup
    (by rw [hw]; rfl)).2.2.1
  change A = W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 at hA
  have hc' : (inducedAutomizer W
      (W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)).map p = SextetCore.core := by
    rw [←hA]
    simpa only [Subgroup.map_map] using hc
  have hfix' : W ⊓ centralizer
      (W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) =
      W ⊓ W.map (MulAut.conj i.val⁻¹).toMonoidHom := by
    change W ⊓ centralizer
      ((W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Subgroup G) : Set G) = _
    rw [←hA]
    exact hfix
  obtain ⟨hU,hB⟩ := selected_code_section_coordinates s F p hF
    (hA ▸ (show A ≤ normalizer (W : Set G) from inf_le_right)) hfix' hc'
  change ∀ v : Additive W, (v.toMul : G) ∈ W ⊓ centralizer
    ((W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Subgroup G) : Set G) ↔
    F v ∈ CodeFlags.sextetCodeSpace standardSextet at hU
  rw [←hA] at hU
  have hRL : R ≤ L := (localResidual_le L U).trans inf_le_left
  have hRV : R ≤ normalizer (W : Set G) := hRL.trans D.sourceOrbit_component_normalizes
  have hRU : R ≤ normalizer (U : Set G) := (localResidual_le L U).trans inf_le_right
  have hFr (x : R) (v : Additive W) :
      F (automizerRepresentation W
        (W.normalizerMonoidHom.rangeRestrict (inclusion hRV x)) v) =
        codeRepresentation (r x).val (F v) := by
    rw [hF,hrval,hval]
    rfl
  have hRB : R ≤ normalizer (B : Set G) :=
    marked_code_even_normalizes W B R inf_le_left hRV F standardSextet r hFr hB
  obtain ⟨hBU,eB,heB,eR,heR,hequiv,hk⟩ :=
    marked_code_section_residual W B U R inf_le_left hRV hRB hRU F standardSextet r
      hFr hU hB hrange hrker hrcore
  exact ⟨c,hRB,hRU,hBU,eB,heB,eR,hequiv,hk⟩


/-- Select the original code pair and mark its literal natural hexacode section. -/
theorem sourceOrbit_m24_code_natural_pair_of_many
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
      let B := D.sourceOrbit ⊓ I.pCoreIn 2
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 6 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ∃ (c : M24) (hRB : R ≤ normalizer (B : Set G))
        (hRU : R ≤ normalizer (U : Set G)) (hBU : (U.subgroupOf B).Normal),
        letI := hBU
        ∃ eB : (B ⧸ U.subgroupOf B) ≃* Multiplicative hexacode,
          (∀ b : B, eB (QuotientGroup.mk' (U.subgroupOf B) b) =
            Multiplicative.ofAdd (NormalizedShadowRows.CodeSection.recover standardSextet
              (codeRepresentation c (E (Additive.ofMul ⟨b,b.property.1⟩))))) ∧
          ∃ eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms,
            (∀ (x : R) (b : B ⧸ U.subgroupOf B),
              eB (sectionAction R B U hRB hRU x b) =
                Multiplicative.ofAdd (hexAction
                  (eR (QuotientGroup.mk' (pCore 2 R) x)).val (eB b).toAdd)) ∧
            (sectionAction R B U hRB hRU).ker = pCore 2 R := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hu,_,hUT,hTU,_⟩ :=
    D.sourceOrbit_m24_code_rank_six_pair_of_many h hmany hV hq hnon a E hE hH
  obtain ⟨c,hRB,hRU,hBU,eB,heB,eR,hequiv,hk⟩ :=
    D.sourceOrbit_m24_code_natural_section h hmany hV hq hnon a E hE s hw hfix hr hu
  exact ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hu,hUT,hTU,c,hRB,hRU,hBU,
    eB,heB,eR,hequiv,hk⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
