module
public import Theory.Representation.BinaryOffender.SmallDualOffender
public import Theory.Representation.BinaryOffender.DualFixedSupplement
public import Theory.Representation.BinaryOffender.Replacement
/-!
# Dual FF modules of dimension at most nine

An offender of fixed codimension at most two supplies an involution with
the required bound. Otherwise a quadratic offender has rank at least three,
and its moved space lies in its fixed space, of dimension at most six.
The numerical dual bound follows without any group classification.

This handles the small irreducible rows in Aschbacher–Smith B.5.13,
printed pp.110–111, after fixed summands have been removed.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
/-- A binary dual FF module of dimension at most nine has quadratic ratio at most two. -/
theorem quadraticRatio_le_two_of_small_dualFF
    (hff : IsFFModule ρ.dual) (hdim : Module.finrank (ZMod 2) V ≤ 9) :
    quadraticRatio ρ ≤ 2 := by
  obtain ⟨A,hA,hq⟩ := (quadraticRatio_le_one_iff ρ.dual).mp
    ((isFFModule_iff_quadraticRatio_le_one ρ.dual).mp hff)
  by_cases hc : fixedCodim ρ.dual A ≤ 2
  · exact quadraticRatio_le_two_of_dual_fixedCodim_le_two ρ hA.1 hc
  have hm : subspaceCommutator ρ.dual ⊤ A ≤ fixedSpace ρ.dual A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩ b
    exact hq b b.property a ha v
  have hmrank := Submodule.finrank_mono hm
  have htotal := fixedCodim_add_finrank ρ.dual A
  rw [Subspace.dual_finrank_eq] at htotal
  have he : fixedCodim ρ A = Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) := by
    rw [subspaceCommutator_top_eq_coinvariants]
    exact Representation.finrank_quotient_invariants_eq_dual_commutator (ρ.comp A.subtype)
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨A,hA.1,(isQuadratic_dual_iff ρ A).mp hq,?_⟩
  have ho := hA.2
  omega

/-- The same bound stated with the FF action as the original input. -/
theorem dual_quadraticRatio_le_two_of_small_FF
    (hff : IsFFModule ρ) (hdim : Module.finrank (ZMod 2) V ≤ 9) :
    quadraticRatio ρ.dual ≤ 2 := by
  have hact (g : G) (v : V) : Module.evalEquiv (ZMod 2) V (ρ g v) =
      ρ.dual.dual g (Module.evalEquiv (ZMod 2) V v) := by
    apply LinearMap.ext
    intro f
    change f (ρ g v) = f (ρ (g⁻¹)⁻¹ v)
    rw [inv_inv]
  have hf := hff.map_equivariant ρ ρ.dual.dual (MonoidHom.id G)
    Function.injective_id (Module.evalEquiv (ZMod 2) V) hact
  apply quadraticRatio_le_two_of_small_dualFF ρ.dual hf
  rwa [Subspace.dual_finrank_eq]
end Representation.BinaryOffender
