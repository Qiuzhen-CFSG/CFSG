module

public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.LinearAlgebra.IntersectionCodimension

/-!+# Fixed-space codimension and generation

Fixed spaces turn generated subgroups into intersections. The codimension
bound for intersections shows that a subgroup of a generated group with
codimension at least the sum of the generating subgroups' codimensions has
exactly the same fixed space as the generated group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma B.2.17, pp. 79–80. The argument works over any field.
-/

namespace Representation

variable {F G V ι : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  (ρ : Representation F G V)

/-- Fixed vectors of a generated subgroup are fixed by each generator subgroup. -/
public theorem invariants_comp_iSup (X : ι → Subgroup G) :
    invariants (ρ.comp (⨆ i, X i).subtype) =
      ⨅ i, invariants (ρ.comp (X i).subtype) := by
  apply le_antisymm
  · exact le_iInf fun i => ρ.invariants_comp_subtype_antitone (le_iSup X i)
  · intro v hv
    have hv' : ∀ i, v ∈ invariants (ρ.comp (X i).subtype) := by
      simpa only [Submodule.mem_iInf] using hv
    let D : Subgroup G := {
      carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change ρ a⁻¹ v = v
        calc
          ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := congrArg (ρ a⁻¹) ha.symm
          _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel]; simp }
    have hD : (⨆ i, X i) ≤ D := iSup_le fun i g hg => hv' i ⟨g, hg⟩
    intro g
    exact hD g.property

/-- Thompson's dimension argument: a reverse codimension bound forces equality
of fixed spaces and equality in the dimension bound. -/
public theorem invariants_eq_and_codimension_eq_of_sum_le
    [FiniteDimensional F V] [Fintype ι] (X : ι → Subgroup G) (L : Subgroup G)
    (hL : L ≤ ⨆ i, X i)
    (hdim : (∑ i, Module.finrank F (V ⧸ invariants (ρ.comp (X i).subtype))) ≤
      Module.finrank F (V ⧸ invariants (ρ.comp L.subtype))) :
    invariants (ρ.comp L.subtype) = invariants (ρ.comp (⨆ i, X i).subtype) ∧
      Module.finrank F (V ⧸ invariants (ρ.comp L.subtype)) =
        ∑ i, Module.finrank F (V ⧸ invariants (ρ.comp (X i).subtype)) := by
  have hle := ρ.invariants_comp_subtype_antitone hL
  rw [ρ.invariants_comp_iSup] at hle ⊢
  exact Submodule.eq_iInf_of_sum_quotient_finrank_le _ _ hle hdim

end Representation
