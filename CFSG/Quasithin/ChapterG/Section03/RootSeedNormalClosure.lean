module

public import CFSG.Quasithin.ChapterG.Section03.SpanningBlockModels
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# A nontrivial original root subgroup normally generates the block product

In a spanning G.3 decomposition, every marked block is the full binary
linear group in dimension at least three, hence simple. The normal closure
of a nontrivial subgroup of one root group contains its entire block.
Conjugacy of the blocks then gives the whole generated group. Conversely,
that generated group is normal in the original actor and contains the seed.

The normal closure is taken in the supplied actor. This does not identify
normal closures taken in a larger ambient group.

Source application: Aschbacher--Smith, 12.7.16, printed p.844, using G.3.1.
The imported higher-rank PSL simplicity is the attributed ATLAS result.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem binary_linear_simple (hn : 3 ≤ Module.finrank (ZMod 2) V) :
    IsSimpleGroup (BinaryLinear.GL V) := by
  let n := Module.finrank (ZMod 2) V
  let c : V ≃ₗ[ZMod 2] OuterCyclic.Space n := LinearEquiv.ofFinrankEq _ _ (by
    simp only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin]
    rfl)
  let e : BinaryLinear.GL V ≃* OuterCyclic.LinearGroup n :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv c).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (OuterCyclic.Space n)))
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    Atlas.psl_simple_high_rank n hn
  let : IsSimpleGroup (OuterCyclic.LinearGroup n) :=
    (OuterCyclic.projectiveEquivLinear (by omega : 0 < n)).symm.isSimpleGroup
  exact e.isSimpleGroup

/-- The root-generated group is the normal closure, in the same original
actor, of any nontrivial subgroup of the specified root group. -/
theorem root_seed_normal_closure
    {H : Subgroup (BinaryLinear.GL V)} [Finite H] (x : V)
    (hf : FullAction H (MulAction.orbit H x))
    (hd : Decomposition H (MulAction.orbit H x))
    (hl : LocalStructure H (MulAction.orbit H x))
    (hspan : Submodule.span (ZMod 2) (MulAction.orbit H x) = ⊤)
    (A : Subgroup (BinaryLinear.GL V)) (hA : A ≤ rootGroup H x) (hne : A ≠ ⊥) :
    conjugateSpanBy A H = generated H (MulAction.orbit H x) := by
  let Δ := MulAction.orbit H x
  let K := conjugateSpanBy A H
  have hx : x ∈ Δ := MulAction.mem_orbit_self x
  have hnormK : H ≤ normalizer (K : Set (BinaryLinear.GL V)) :=
    le_normalizer_conjugateSpanBy A H
  have hnormal : ((generated H Δ).subgroupOf H).Normal :=
    generated_normal H Δ (by
      intro g hg y hy
      obtain ⟨b, rfl⟩ := MulAction.mem_orbit_iff.mp hy
      exact MulAction.mem_orbit_iff.mpr ⟨(⟨g, hg⟩ : H) * b, rfl⟩)
  have hKgen : K ≤ generated H Δ := conjugateSpanBy_le
    (hA.trans (rootGroup_le_generated H hx))
    ((normal_subgroupOf_iff_le_normalizer (generated_le H Δ)).mp hnormal)
  obtain ⟨e, _, _, _⟩ := spanning_block_models hf hd hspan
  let i : OrbitBlock H Δ := ⟨MulAction.orbit (generated H Δ) x, x, hx, rfl⟩
  have hxi : x ∈ i.val := MulAction.mem_orbit_self x
  have hAi : A ≤ blockGroup H Δ i := hA.trans (rootGroup_le_generated H hxi)
  have hKi : blockGroup H Δ i ≤ K := by
    let : IsSimpleGroup (BinaryLinear.GL (blockSpace H Δ i)) :=
      binary_linear_simple (hl.dimension_ge_three i)
    let : IsSimpleGroup (blockGroup H Δ i) := (e i).isSimpleGroup
    let M := K.subgroupOf (blockGroup H Δ i)
    let : M.Normal := normal_subgroupOf_of_le_normalizer
      ((generated_le H i.val).trans hnormK)
    have hMne : M ≠ ⊥ := by
      intro he
      obtain ⟨a, ha, hane⟩ := A.bot_or_exists_ne_one.resolve_left hne
      have hm : (⟨a, hAi ha⟩ : blockGroup H Δ i) ∈ M := le_conjugateSpanBy A H ha
      rw [he] at hm
      exact hane (congrArg Subtype.val (mem_bot.mp hm))
    have hMtop : M = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal M inferInstance).resolve_left hMne
    intro g hg
    exact show (⟨g, hg⟩ : blockGroup H Δ i) ∈ M from hMtop.symm ▸ mem_top _
  have hall (j : OrbitBlock H Δ) : blockGroup H Δ j ≤ K := by
    obtain ⟨g, hg, he⟩ := hd.groups_conjugate i j
    rw [← he]
    rintro _ ⟨a, ha, rfl⟩
    exact le_normalizer_iff.mp hnormK g hg a (hKi ha)
  exact le_antisymm hKgen (by
    rw [← hd.group_join]
    exact iSup_le hall)

end CFSG.Quasithin.ChapterG.Section03
