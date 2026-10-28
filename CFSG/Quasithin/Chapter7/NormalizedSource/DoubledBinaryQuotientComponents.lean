module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryHyperplane
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import Theory.GroupTheory.CComponent.ResidualLifting

/-!
# Lifting the escaping component through the original centralizer quotient

The source SQTK generation theorem applies to the literal preimage of a
quotient component. Its C-components generate its solvable residual, so
one maps onto the given ordinary component. This works for the full action
kernel; it does not assume that kernel solvable.

If the kernel lies in M and the full component preimage escapes M, the
lift itself escapes. The lift has at most two ambient conjugates and is
normalized by the original two-perfect residual. The actual chosen-module
application is NonFFSourceDoubledBinaryQuotientComponents. Its two-core
quotient structure and subsequent C.2 exclusions remain with the final
assembly owner qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of Proposition 7.7.3, printed p.707;
1.2.1(1),(3), printed pp.503–504, and A.3.9(1), printed p.46.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryQuotientComponents

private theorem sqtk_twoCore_quotient {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
  refine ⟨?_,hH.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hH.stronglyQuasithin p hp ho)

private theorem sqtk_generation {H : Type*} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    cComponentLayer H = solvableResidual H := by
  exact Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
    (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
      (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
      (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
        (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO) (sqtk_twoCore_quotient hH)

/-- Every ordinary component of a quotient of the actual SQTK group lifts
to a C-component, using source generation in the full component preimage. -/
theorem quotient_component_lift
    {H A : Type*} [Group H] [Finite H] [Group A]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (q : H →* A) (hq : Function.Surjective q)
    (K : Subgroup A) (hK : IsComponent A K) :
    ∃ C : Subgroup H, C.IsCComponent ∧ C.map q = K := by
  exact exists_cComponent_map_eq_of_preimage_layer q hq hK.isCComponent
    (sqtk_generation (hH.subgroup (K.comap q)))

/-- An escaping full preimage lifts to an escaping C-component whenever
the original quotient kernel is contained in M. No solvability of that
kernel, and no ordinary-component assertion about the lift, is assumed. -/
theorem escaping_quotient_component_lift
    {H A : Type*} [Group H] [Finite H] [Group A]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (q : H →* A) (hq : Function.Surjective q) (M : Subgroup H)
    (hker : q.ker ≤ M) (K : Subgroup A) (hK : IsComponent A K)
    (hout : ¬ K.comap q ≤ M) :
    ∃ C : Subgroup H, C.IsCComponent ∧ C.map q = K ∧
      C ⊔ q.ker = K.comap q ∧ ¬ C ≤ M := by
  obtain ⟨C,hC,he⟩ := quotient_component_lift hH q hq K hK
  have hpre : C ⊔ q.ker = K.comap q := by rw [← he,comap_map_eq]
  exact ⟨C,hC,he,hpre,fun hc => hout (hpre.symm ▸ sup_le hc hker)⟩

/-- The lifted source component has at most two ambient conjugates and is
normalized by the original two-perfect residual. -/
theorem escaping_quotient_component_lift_normalized
    {H A : Type*} [Group H] [Finite H] [Group A]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (q : H →* A) (hq : Function.Surjective q) (M R : Subgroup H)
    (hR : IsPPerfect 2 R) (hker : q.ker ≤ M)
    (K : Subgroup A) (hK : IsComponent A K) (hout : ¬ K.comap q ≤ M) :
    ∃ C : Subgroup H, C.IsCComponent ∧ C.map q = K ∧
      C ⊔ q.ker = K.comap q ∧ ¬ C ≤ M ∧
      R ≤ normalizer (C : Set H) ∧
      (C.Normal ∨ (normalizer (C : Set H)).index = 2) := by
  obtain ⟨C,hC,he,hpre,hout⟩ := escaping_quotient_component_lift hH q hq M hker K hK hout
  have hQ := sqtk_twoCore_quotient hH
  exact ⟨C,hC,he,hpre,hout,
    Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ hC hR,
    Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hC⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryQuotientComponents
