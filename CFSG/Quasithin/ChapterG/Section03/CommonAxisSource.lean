module

public import CFSG.Quasithin.ChapterG.Section03.CommonCenterSource
public import Theory.Representation.BinaryTransvectionGroups.Duality

/-!
# Dual G.3.1 from an actual hyperplane fixer

Over the binary field, a linear automorphism fixing a hyperplane pointwise
also acts trivially on its quotient. Thus a subgroup of order greater than
two fixing that hyperplane supplies common-center transvections on the
actual dual module. The original trivial-two-core condition is transported
through the faithful contragredient action.

Source application: Aschbacher--Smith12.7.18, printed p.845.
-/

public section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A genuine large hyperplane fixer supplies the dual G.3.1 conclusions. -/
theorem source_conclusions_of_common_axis
    {H : Subgroup (BinaryLinear.GL V)} [Finite H] (hcore : pCore 2 H = ⊥)
    (f : DualSpace V) (hf : f ≠ 0)
    (A : Subgroup (BinaryLinear.GL V)) (hAH : A ≤ H) (hc : 2 < Nat.card A)
    (hfix : ∀ g ∈ A, ∀ v ∈ f.ker, g v = v) :
    FullAction (dualGroup H) (MulAction.orbit (dualGroup H) f) ∧
      Decomposition (dualGroup H) (MulAction.orbit (dualGroup H) f) ∧
      LocalStructure (dualGroup H) (MulAction.orbit (dualGroup H) f) := by
  have hform (g : BinaryLinear.GL V) (hg : g ∈ A) (v : V) : f (g v) = f v := by
    by_cases hv : f v = 0
    · rw [hfix g hg v hv]
    · have hgv : f (g v) ≠ 0 := by
        intro hh
        have he := hfix g⁻¹ (A.inv_mem hg) (g v) hh
        change g.symm (g v) = g v at he
        have hev : v = g v := (g.symm_apply_apply v).symm.trans he
        exact hv (congrArg f hev |>.trans hh)
      have hbit : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rw [(hbit (f (g v))).resolve_left hgv,(hbit (f v)).resolve_left hv]
  have hroot (g : BinaryLinear.GL V) (hg : g ∈ A) :
      contragredient g ∈ rootGroup (dualGroup H) f := by
    apply (contragredient_mem_axisRoot_iff H f g).mpr
    refine ⟨hAH hg,hfix g hg,?_⟩
    intro v
    change f (g v - v) = 0
    rw [map_sub,hform g hg v,sub_self]
  apply source_conclusions_of_common_center (dualGroup_twoCore_eq_bot hcore) f hf
    (A.map contragredient) (map_mono hAH) ?_ ?_ ?_
  · rw [card_map_of_injective contragredient_injective]
    exact hc
  · rintro _ ⟨g,hg,rfl⟩
    exact (hroot g hg).2.1 f (Submodule.mem_span_singleton_self f)
  · rintro _ ⟨g,hg,rfl⟩ v
    exact (hroot g hg).2.2 v

end CFSG.Quasithin.ChapterG.Section03
