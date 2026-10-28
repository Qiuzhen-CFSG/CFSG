module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCenterless
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeSixCover

/-!
# The original M22-code component reduces to M₁₁ or Held

Restrict the same original Sylow and point residual to their containing
component. The actual embedding removes the covering center in either
higher binary-linear model, so the full A₆-section exclusions apply.
The M₁₁ alternative likewise supplies the full original residual quotient
A₆, without replacing the residual or quotient map.

The final theorem retains the original involution, Xi complement,
containing component, normality, residual inclusion and full two-core.
Held remains explicit, with its possible smaller covering center. The
M₁₁ terminal contradiction is supplied next by M22CodeHeldReduction.
Held exclusion, removal of hcore and later M22-code exclusion are still
needed for unconditional M24-cocode selection.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, refs/quasithin.pdf.
-/

public noncomputable section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.MathieuShadowRows Chapter1 Chapter1.XiEmbedding
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original projective A₆ residual excludes either higher binary-linear containing component, with its full Sylow and covering kernel retained. -/
theorem sourceOrbit_m22_code_not_binary_containing_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    {K : Subgroup G} (hK : K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)))
    (hRK : localResidual L z ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (XiQuotient K) n 2) : False := by
  let C := centralizer ({(z : G)} : Set G)
  let M := normalizer (L : Set G) ⊓ C
  let R := localResidual L z
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hRM : R ≤ M := (localResidual_le L z).trans (inf_le_inf_right _ L.le_normalizer)
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hz t ht)
  have hRTM : R ⊔ (T : Subgroup G) ≤ M := sup_le hRM
    (le_inf D.sylow_normalizes_component hTC)
  obtain ⟨hR,_⟩ := D.sourceOrbit_m22_code_centralizer_component h d z hz hne
  have hl : R ∈ ChapterA.Section03.localCComponents (T : Subgroup G) :=
    hR.subgroupOf_of_le le_sup_left hRTM
  let S := T.subtype hTC
  have hlC : R.subgroupOf C ∈ ChapterA.Section03.localCComponents (S : Subgroup C) :=
    ChapterA.Section03.SourceEmbeddings.local_restrict hl hRC
  obtain ⟨hqR,⟨eR⟩⟩ := D.sourceOrbit_m22_code_centralizer_projective h d z hz hne
  let := hqR
  let a : R.subgroupOf C ≃* R := subgroupOfEquivOfLe hRC
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let az := QuotientGroup.congr _ _ aq (FixedElementary.map_center aq)
  let : IsQuasisimple (R.subgroupOf C ⧸ pCore 2 (R.subgroupOf C)) :=
    IsQuasisimple.of_mulEquiv aq.symm
  let b : K.subgroupOf C ≃* K := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact not_binary_containing_projective_six S hlC hK.2 (comap_mono hRK)
    (az.trans eR) hn (hm.of_mulEquiv bq)

/-- On the same original involution and component, the two binary higher-linear rows are excluded. The M11 row now has the full A₆ two-core quotient; the Held covering alternative remains explicit. -/
theorem sourceOrbit_m22_code_inside_core_m11_or_held
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    let X := (pResidual 2 H).map H.subtype
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      ∃ P K : Subgroup G,
        LocalInput 3 (T : Subgroup G) X P (centralizer ({(z : G)} : Set G)) ∧
        K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)) ∧
        localResidual L z ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (XiQuotient K) ∧ center (XiQuotient K) = ⊥ ∧
        X ≤ K ∧ Nonempty (P ≃* Plane 3) ∧
        ((Nonempty (XiQuotient K ≃* M11) ∧
          Nonempty ((localResidual L z ⧸ pCore 2 (localResidual L z)) ≃*
            alternatingGroup (Fin 6))) ∨ Nonempty (XiQuotient K ≃* Held.He)) := by
  obtain ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,hm⟩ :=
    D.sourceOrbit_m22_code_inside_core_centerless_component h hmany hV hnon d hH hcore
  have hz : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hHC (hH.1.1.2 ht))
  refine ⟨z,hne,ho,hHC,P,K,hin,hK,hRK,hnK,hq,hzK,hXK,hP,?_⟩
  rcases hm with hm | hm
  · rcases hm with hm | hm | hm
    · obtain ⟨hqR,⟨eR⟩⟩ := D.sourceOrbit_m22_code_centralizer_projective h.toHypothesis1221 d z hz hne
      let := hqR
      exact Or.inl ⟨hm,projective_six_core_equiv_of_exceptional_embedding eR
        (inclusion hRK) (inclusion_injective hRK) (Or.inl hm)⟩
    · exact (D.sourceOrbit_m22_code_not_binary_containing_component h.toHypothesis1221 d z hz hne
        hK hRK (Or.inl rfl) hm).elim
    · exact (D.sourceOrbit_m22_code_not_binary_containing_component h.toHypothesis1221 d z hz hne
        hK hRK (Or.inr rfl) hm).elim
  · exact Or.inr hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
