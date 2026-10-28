module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryReduction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSylow

/-!
# The actual reduced generic amalgam in Chapter12

Apply the reduction to the prepared whole-residual pair, with the original
S = O₂(N_G(L) ∩ H) and the reduced Sylow T ∩ L kept distinct. The reduced
parabolics are exactly the two-residuals of the old parabolics. In ordinary
rows S already is that common Sylow. In the degree-two unitary row both
reduced parabolics have index two and their actual inclusion amalgam is
isomorphic to the ordinary unitary amalgam, in either original orientation.
The overlap is the whole intersection, so both odd Cartans are retained.

This discharges the unitary replacement immediately before 5.2.7. Exhaustive
F.1.12 comparison, the 5.2.8 right-maximality alternative and ambient completion
recognition remain with the generic/global owner. Original uniqueness remains
explicit, with producer qt-d-1222-rankone-global-uniqueness.
Source: Aschbacher–Smith 5.2.6–7, printed pp.650–651, and the Chapter12
application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Reduce the actual pair, retaining its full overlap and every catalogue row.
The unitary branch supplies ordinary compatible maps and both exact indices. -/
theorem rankOne_global_reduced_geometry_of_concrete_comparisons
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcomparison : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R → Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))) :
    ∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      (∀ i : Fin 2, ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i =
        (pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i)).map
          (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).subtype) ∧
      (Global.sourceS L H = (T : Subgroup G) ⊓ L ∨
        ∃ (m : ℕ) (hm : 1 < m),
          (∀ i : Fin 2,
            (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i).relIndex
              (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i) = 2) ∧
          (Nonempty (RankTwoAmalgam.Iso
              (Global.sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L))
              (ChapterF.GreenBook.LieModels.UnitaryFour.amalgam m hm.le)) ∨
            Nonempty (RankTwoAmalgam.Iso
              (Global.sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L))
              (ChapterF.GreenBook.LieModels.UnitaryFour.amalgam m hm.le).reverse))) := by
  obtain ⟨A,B,d,hp⟩ := D.rankOne_global_residual_preparation_of_concrete_comparisons
    h hmany hn hpsl hH hpar hthree hN hunique hcomparison
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hc := hcomparison A B (residual H) d hp
  refine ⟨A,B,d,d.reduced_source_parabolics hi hH.1.1.2 hp hc,?_⟩
  rcases d.sourceS_le_factors_or_unitaryExtension hi hH.1.1.2 hp hc with hs | ⟨m,hm,he⟩
  · exact Or.inl ((inf_eq_left.mpr (hs 0)).symm.trans d.left_intersection)
  · exact Or.inr ⟨m,hm,d.unitaryExtension_reduced_index hi hH.1.1.2 hp m hm he,
      d.unitaryExtension_reduced_amalgam hi hH.1.1.2 hp m hm he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
