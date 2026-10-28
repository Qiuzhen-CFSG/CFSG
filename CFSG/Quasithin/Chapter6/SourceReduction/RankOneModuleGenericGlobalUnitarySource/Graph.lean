module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourGraph
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The graph-fixed source pair in the original ambient Sylow

The compatible degree-two comparison constructs a graph involution with its
symplectic fixed local diagram. Conjugation inside the original whole overlap
places it in the actual sourceS, hence in the original ambient T. The proved
solvable-residual markings show that it lies outside both L and O²(H).
Both commuting squares and the marked central graph factor survive this
conjugation. The strict exponent m>1 and n=2m come from the original
nonsolvable local factors, so q=4 remains included in either orientation.

This supplies the native graph-fixed pair for the prepared F.4.37 argument
(Aschbacher–Smith, printed p.293 of `refs/quasithin.pdf`). The parabolics here
are the actual source parabolics. Full-normalizer realization, placement of
C_T(f) as a Sylow subgroup of C_G(f), and transfer remain further obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The prepared degree-two row supplies an actual outer involution in the
original T, with its symplectic fixed local diagram and whole fixed overlap.
This does not assert that C_T(f) is Sylow in C_G(f). -/
theorem Preparation.unitary_graph_fixed_amalgam
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    1 < m ∧ n = 2*m ∧
      ∃ f : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        f.val ∈ sourceS L H ∧ f.val ∈ (T : Subgroup G) ∧ orderOf f.val = 2 ∧
        f.val ∉ L ∧ f.val ∉ residual H ∧
        ((∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m),
            e.middle (centralPoint f) = (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator)) ∨
         (∃ e : RankTwoAmalgam.Iso
          (centralizerDiagram (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) f)
          (ChapterF.UnitarySource.FourGraph.fixedDiagram m).reverse,
            e.middle (centralPoint f) = (1,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.generator))) := by
  have hm' := d.unitaryExtension_local_structure h hH.1.1.2 hp m hm hc
  refine ⟨hm'.1,hm'.2.1,?_⟩
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let B := P 0 ⊓ P 1
  let α := sourceParabolicAmalgam ![L,residual H] (sourceS L H)
  have hs : ∃ U : Sylow 2 B, (U : Subgroup B).map B.subtype = sourceS L H := by
    change ∃ U : Sylow 2 (P 0 ⊓ P 1 : Subgroup G),
      (U : Subgroup (P 0 ⊓ P 1 : Subgroup G)).map (P 0 ⊓ P 1).subtype = sourceS L H
    have hf := d.hypothesisF11 h hH.1.1.2
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  refine hs.elim fun U hU => ?_
  have hres (i : Fin 2) : (![L,residual H] i).subgroupOf (P i) = solvableResidual (P i) := by
    rw [←d.parabolic_residuals h hH.1.1.2 hp i]
    exact comap_map_eq_self_of_injective (P i).subtype_injective _
  refine (ChapterF.UnitarySource.FourGraph.comparison_graph_sylow m hm α U hc).elim fun f hf => ?_
  have hfS : f.val ∈ sourceS L H := hU.le (mem_map_of_mem B.subtype hf.1)
  refine ⟨f,hfS,sourceS_le_sylow h.sylow_normalizes hH.1.1.2 hfS,
    (Subgroup.orderOf_coe f).trans hf.2.1,?_,?_,hf.2.2.2.2⟩
  · intro hfL
    have hh : α.left f ∈ solvableResidual (P 0) := (hres 0) ▸ hfL
    exact hf.2.2.1 hh
  · intro hfR
    have hh : α.right f ∈ solvableResidual (P 1) := (hres 1) ▸ hfR
    exact hf.2.2.2.1 hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
