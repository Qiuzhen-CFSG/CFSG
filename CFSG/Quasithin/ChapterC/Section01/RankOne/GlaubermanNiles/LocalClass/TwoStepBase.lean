module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.BlockRecognition.Escape
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSelection.Seed

/-!
# Block recognition from central involutory commutators in the common base

If the commutators of a Baumann-fixed two-group B are central involutions,
every actual C.1.17 group marked by B has the block alternative. The
marked Sylow subgroup cannot lie in the two-core. Its commutators with
that core lie in the mapped omega-center, hence in Campbell's F. The
proved noncore-commutator recognition theorem therefore applies.

This supplies the second-block recognition implication in 10.2.3(4),
once the preceding common Sylow geometry establishes the indicated
commutator containment. It does not infer that containment from a special
subgroup of B alone.
Source: Aschbacher--Smith C.1.18 and 10.2.3(4), pp.126,747;
Campbell, Pushing up in Finite Groups, II.8, p.38.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

/-- A marked common base with central involutory commutators forces a block. -/
theorem InLocalClass.blockAlternative_of_commutator_le_omegaCenter
    (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hcomm : commutator B ≤ omegaCenter B) : BlockAlternative H := by
  obtain ⟨T,he,hP⟩ := h.sylow
  have hnot : ¬ e.range ≤ pCore 2 H := by
    intro hle
    have hEq : (T : Subgroup H) = pCore 2 H :=
      le_antisymm (he ▸ hle) (pCore_isPGroup.le_sylow_of_normal T)
    have hn : (T : Subgroup H).Normal := hEq ▸ inferInstance
    exact ((ChapterB.isMinimalParabolicOver_top_iff T).mp hP).2 hn
  apply h.blockAlternative_of_noncore_commutator hB e.range le_rfl hnot
  apply (commutator_mono le_rfl (he.symm ▸ pCore_isPGroup.le_sylow_of_normal T)).trans
  rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def]
  exact (map_mono hcomm).trans h.omegaCenter_map_le_F

end CFSG.Quasithin.ChapterC.GlaubermanNiles
