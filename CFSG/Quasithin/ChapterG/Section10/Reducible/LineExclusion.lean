module
public import CFSG.Quasithin.ChapterG.Section10.Axis
public import CFSG.Quasithin.ChapterG.Section10.TwoCore
public import Theory.Representation.BinaryTwoLayerFaithfulness
public import Theory.Representation.BinaryParabolicNatural.Basic
public import Theory.Representation.SubspaceQuotient

/-!
# Excluding invariant lines in G.10.4

The rank equality forces ambient degree two if there is an invariant line.
Both factors are then binary lines, so the action has two-group kernel.
The zero two-core makes the whole action trivial, contradicting the orbit
span. This completes the small-degree branch without a group classification.
-/

public section
open Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

theorem finrank_ne_one_of_proper_submodule (U : Subrepresentation ρ)
    (hU0 : U.toSubmodule ≠ ⊥) (hUt : U.toSubmodule ≠ ⊤) :
    finrank (ZMod 2) U.toSubmodule ≠ 1 := by
  intro hdU
  have he := (h.full_axis_on_submodule U hU0 hUt).2.1
  have hb := h.dimension_bound.1
  have hlt := Submodule.finrank_lt hUt
  have hd : finrank (ZMod 2) V = 2 := by omega
  have hdq : finrank (ZMod 2) (V ⧸ U.toSubmodule) = 1 := by
    have he := U.toSubmodule.finrank_quotient_add_finrank
    omega
  have hqu (g : G) (z : V ⧸ U.toSubmodule) : U.quotientRepresentation g z = z := by
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv (U.quotientRepresentation.asGroupHom g)
    exact congrArg (fun t : (V ⧸ U.toSubmodule) ≃ₗ[ZMod 2] (V ⧸ U.toSubmodule) => t z)
      (BinaryParabolicNatural.linear_one_trivial hdq e)
  have hdisp (g : G) (w : V) : ρ g w - w ∈ U := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change U.toSubmodule.mkQ (ρ g w-w) = 0
    rw [map_sub,←U.quotientRepresentation_mk,hqu,sub_self]
  have hfaith := two_layer_restriction_faithful ρ U h.faithful hdisp h.twoCore_eq_bot
  have hone (g : G) : g = 1 := by
    apply hfaith
    apply LinearMap.ext
    intro u
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv (U.toRepresentation.asGroupHom g)
    rw [map_one,Module.End.one_apply]
    exact congrArg (fun t : U.toSubmodule ≃ₗ[ZMod 2] U.toSubmodule => t u)
        (BinaryParabolicNatural.linear_one_trivial hdU e)
  have hspan : Submodule.span (ZMod 2) {v} = ⊤ := by
    apply top_unique
    rw [←h.orbit_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,rfl⟩
    rw [hone g,map_one,Module.End.one_apply]
    exact Submodule.mem_span_singleton_self v
  have he := finrank_span_singleton (K := ZMod 2) h.point_ne_zero
  rw [hspan,finrank_top,hd] at he
  omega

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
