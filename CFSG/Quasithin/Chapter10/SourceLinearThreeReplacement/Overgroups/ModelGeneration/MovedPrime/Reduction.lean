module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Parabolic
public import CFSG.Quasithin.ChapterE.Section01.MinimalParabolicGeneration
public import Theory.GroupTheory.CComponent.QuasisimpleImage

/-!
# Generation from the selected moved-prime cover

Each selected solvable or genuine minimal-parabolic row has generation bound
one. Intrinsic generation and the Sylow normalizer then generate the ambient
group. Passing through the actual two-core preserves the marked component,
its nonnormality, and its full Sylow supplement. Thus the core-free cover is
sufficient for the original moved-prime contract. The cover construction is
still an explicit premise, owned by this task's automizer calculation.

Source: Aschbacher--Smith E.1.12--14 and 10.3.3, pp.214 and 756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The selected rows, rather than all parabolics, suffice for generation. -/
theorem isEGenerated_of_primeParabolicCover
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (S : Sylow 2 H)
    (hcover : HasPrimeParabolicCover S) : ChapterE.IsEGenerated 1 H := by
  obtain ⟨Δ, hrows, hgen⟩ := hcover
  apply ChapterE.IsEGeneratedAt.isEGenerated (T := S)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChapterE.ChiefOrbit.generationTarget 1 S Ω
  rw [← hgen]
  apply sup_le
  · apply sSup_le
    intro P hP
    obtain ⟨hSP, hsol | ⟨hmin, L, hL, hq, hLS, p, hp, ho, hp7, hm⟩⟩ := hrows P hP
    · let := hsol
      exact ChapterE.ChiefOrbit.solvable_overgroup_le_generationTarget
        (by decide) S P hSP hΩ
    · let := hq
      exact ChapterE.ChiefOrbit.overgroup_le_generationTarget S P hSP hΩ
        (isEGenerated_of_minimalParabolic_odd_component (hH.subgroup P)
          (S.subtype hSP) hmin L hL hLS hp ho hp7 hm)
  · exact (SubgroupFamily.normalizer_le_span_normalizer
      (fun A hA g => hΩ.2 g A hA) (S : Subgroup H)).trans le_sup_right

/-- Remove the actual two-core and apply the core-free structural cover.
All maps and the marked PSL₂ quotient are those of the original component. -/
theorem movedOddPrimeGeneration_of_coreFreeCover
    (hcover : CoreFreeMovedPrimeCover.{u}) : MovedOddPrimeGeneration.{u} := by
  intro H _ _ hH S K hK hn hq hgen p hp ho hp7 hm
  let := hq
  have hs : IsSimpleGroup (K ⧸ pCore 2 K) := by
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact e.isSimpleGroup
  let := hs
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let e : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let : IsSimpleGroup B := e.symm.isSimpleGroup
  have hB : IsComponent (H ⧸ pCore 2 H) B :=
    ⟨hK.subnormal.map (QuotientGroup.mk'_surjective _), IsQuasisimple.of_mulEquiv e⟩
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  have hBn : ¬ B.Normal := fun h => hn
    (cComponent_normal_of_quotient_normal hK (pCore 2 H) h)
  have hBS : B ⊔ (R : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    change K.map q ⊔ (S : Subgroup H).map q = ⊤
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hquot := sqtk_quotient_of_two_kernel hH (pCore 2 H) pCore_isPGroup
  apply ChapterE.IsEGenerated.of_normal_two_subgroup (pCore 2 H) pCore_isPGroup
  exact isEGenerated_of_primeParabolicCover hquot R
    (hcover (H ⧸ pCore 2 H) hquot (pCore_quotient_pCore_eq_bot 2) R B hB
      inferInstance hBn hBS p hp ho hp7 (hm.of_mulEquiv e.symm))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
