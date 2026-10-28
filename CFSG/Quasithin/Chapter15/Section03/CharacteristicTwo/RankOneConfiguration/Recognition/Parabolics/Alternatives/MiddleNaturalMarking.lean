module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Interfaces
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces

/-!
# The actual middle flag in the natural module coordinates

The simultaneous eight-point marking identifies the even pair stabilizer
with the middle A₃ parabolic. Its basis cuts have dimensions one and three.
Transport those literal subspaces to the projective-linear model, retaining
the component intersection. This supplies the flag input used to exclude
the natural-plus-dual and repeated-natural module alternatives in15.3.32.

Source: Aschbacher–Smith15.3.28(3),15.3.32(1), pp.1131–1133.
-/
public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
open Chapter2.ComponentRefinement.LieType.Binary
open BinaryLinear.InvariantNodeActions
open EightGeometry.NaturalModule.Recognition
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
variable {G : Type*} [Group G]

private def middleFlag (b : BinaryLinear.InvariantNodeActions.Basis 3) : Flag 4 := by
  classical
  exact {
  spaces := {cutSpace b 0,cutSpace b 2}
  nonempty := by simp
  proper := by
    intro W hW
    simp only [Finset.mem_insert,Finset.mem_singleton] at hW
    rcases hW with rfl | rfl <;> exact ⟨cutSpace_ne_bot _ _,cutSpace_ne_top _ _⟩
  chain := by
    intro W hW W' hW'
    simp only [Finset.mem_insert,Finset.mem_singleton] at hW hW'
    rcases hW with rfl | rfl <;> rcases hW' with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl (cutSpace_mono b (by decide : (0 : Fin 3) ≤ 2))
    · exact Or.inr (cutSpace_mono b (by decide : (0 : Fin 3) ≤ 2))
    · exact Or.inl le_rfl }

private theorem middleFlag_types (b : BinaryLinear.InvariantNodeActions.Basis 3) :
    (middleFlag b).types = {1,3} := by
  classical
  simp [Flag.types,middleFlag,cutSpace_finrank]

/-- The source marking supplies the exact projective flag required by the
natural-module recognition theorem. -/
theorem MiddleNodeFlagMarking.naturalMarking
    {d : LocalData G} {I L : Subgroup G} (mark : MiddleNodeFlagMarking d I L) :
    Nonempty (Models.MiddleNodeMarking (d.starImage I L) (d.starImage I (d.M ⊓ L))) := by
  classical
  let A := d.starImage I L
  let P := d.starImage I (d.M ⊓ L)
  have hPA : P ≤ A := map_mono (comap_mono inf_le_right)
  let e : A ≃* alternatingGroup (Fin 8) :=
    (mark.equiv.subgroupMap A).trans (MulEquiv.subgroupCongr mark.component)
  have hPe : (P.subgroupOf A).map e.toMonoidHom =
      pairStabilizer.subgroupOf (alternatingGroup (Fin 8)) := by
    apply map_injective (alternatingGroup (Fin 8)).subtype_injective
    rw [map_map,subgroupOf_map_subtype]
    change (P.subgroupOf A).map (mark.equiv.toMonoidHom.comp A.subtype) = _
    rw [←map_map,map_subgroupOf_eq_of_le hPA]
    exact mark.component_intersection
  let f := e.trans mark.comparison.equiv
  have hPf : (P.subgroupOf A).map f.toMonoidHom =
      minimalParabolic mark.comparison.basis 1 := by
    change (P.subgroupOf A).map (mark.comparison.equiv.toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map,hPe,mark.comparison.middle]
  let model := f.trans (pslEquivLinear 4).symm
  let flag := middleFlag mark.comparison.basis
  have hmem (a : A) : a ∈ P.subgroupOf A ↔ a ∈ flagStabilizer model flag := by
    have hm : a ∈ P.subgroupOf A ↔ f a ∈ minimalParabolic mark.comparison.basis 1 := by
      rw [←hPf]
      exact (mem_map_iff_mem f.injective).symm
    rw [hm,mem_flagStabilizer]
    rw [minimalParabolic,mem_cutStabilizer]
    have hmodel : linearModel model a = f a := (pslEquivLinear 4).apply_symm_apply _
    rw [hmodel]
    change _ ↔ ∀ W ∈ ({cutSpace mark.comparison.basis 0,
      cutSpace mark.comparison.basis 2} : Finset _), ∀ v, f a v ∈ W ↔ v ∈ W
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro h W hW
      rcases hW with rfl | rfl
      · exact h 0 (by decide)
      · exact h 2 (by decide)
    · intro h i hi
      have hi' : i = 0 ∨ i = 2 := by fin_cases i <;> simp_all
      rcases hi' with rfl | rfl
      · exact h _ (Or.inl rfl)
      · exact h _ (Or.inr rfl)
  refine ⟨⟨model,flag,middleFlag_types _,?_⟩⟩
  change P = (flagStabilizer model flag).map A.subtype
  rw [←Subgroup.ext hmem,map_subgroupOf_eq_of_le hPA]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
