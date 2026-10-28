module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Faithfulness
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Quadrangle
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Basic

/-!
# Faithful action on the original 27 plane cosets

Fixing every plane coset fixes every point-parabolic coset: each has two
distinct incident planes, whose common neighbor is unique by girth eight.
The already proved common-cover vertex faithfulness then kills the kernel.
This retains the literal point action used in the U₄(2) case of F.4.24.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph.QuadrangleCollinearity
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

theorem point_action_injective (hc : Nat.card G = 25920) :
    Function.Injective (MulAction.toPermHom G c.Point) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  apply c.vertex_action_injective
  apply Equiv.Perm.ext
  intro v
  change g • v = (1 : G) • v
  rw [one_smul]
  have hfix (x : c.Point) : g • x.val = x.val :=
    congrArg Subtype.val (Equiv.Perm.ext_iff.mp hg x)
  cases hv : v.type
  · obtain ⟨a, ha, _⟩ := c.hasTwoNeighbors v v
    obtain ⟨b, hb, hba⟩ := c.hasTwoNeighbors v a
    have hta : a.type = true := by simpa [hv] using c.adjacency_flip ha
    have htb : b.type = true := by simpa [hv] using c.adjacency_flip hb
    have hga := hfix ⟨a, hta⟩
    have hgb := hfix ⟨b, htb⟩
    exact common_vertex_unique (c.quadrangle_metric hc).1 hba.symm
      (by simpa only [hga] using c.graphAction.map_adj g ha.symm)
      (by simpa only [hgb] using c.graphAction.map_adj g hb.symm) ha.symm hb.symm
  · exact hfix ⟨v, hv⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Completion
