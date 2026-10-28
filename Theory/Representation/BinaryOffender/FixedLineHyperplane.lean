module
public import Theory.Representation.BinaryOffender.CommonCenterBound
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Cubic actions through a hyperplane and a fixed line

An elementary binary actor whose displacements send the whole module to
an invariant hyperplane, and that hyperplane to a fixed line, acts cubically.
The common-center displacement map bounds the fixed codimension on the
hyperplane by the actor rank, with one further dimension lost in the ambient
module. No chosen subspace of the hyperplane is assumed pointwise fixed.

The application is the literal opposite action in Aschbacher--Smith 5.1.23,
printed p.645: the cross-commutator bound into the original four-plane gives
this filtration after quotienting by the original point.
-/

public noncomputable section
open Submodule Module
open Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace Representation.BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
variable {G : Type*} [Group G] [Finite G]
/-- A hyperplane with a common fixed displacement line gives a cubic actor of codimension at most rank plus one. -/
theorem cubic_bound_of_fixed_line_hyperplane
    (ρ : Representation (ZMod 2) G V) (E : Subgroup G) (he : IsElementaryTwo E)
    (W Z : Submodule (ZMod 2) V)
    (hZ : finrank (ZMod 2) Z = 1) (hW : finrank (ZMod 2) W + 1 = finrank (ZMod 2) V)
    (hfirst : ∀ a ∈ E, ∀ v, displacement ρ a v ∈ W)
    (hsecond : ∀ a ∈ E, ∀ v ∈ W, displacement ρ a v ∈ Z)
    (hfixed : Z ≤ fixedSpace ρ E) :
    IsCubic ρ E ∧ fixedCodim ρ E ≤ rank E + 1 := by
  let := he.2
  let τ := ρ.comp E.subtype
  let W' : Subrepresentation τ := {
    toSubmodule := W
    apply_mem_toSubmodule a v hv := by
      have hh := hfirst a a.property v
      change ρ (a:G) v - v ∈ W at hh
      change ρ (a:G) v ∈ W
      simpa using W.add_mem hh hv }
  have hbound := CommonCenter.fixedCodim_top_le_rank_add_codim τ W' Z hZ.le
    (fun a v hv => hsecond a a.property v hv)
    (fun a z hz => hfixed hz a)
  have hcodim : finrank (ZMod 2) (V ⧸ W) = 1 := by
    have hh := W.finrank_quotient_add_finrank
    omega
  refine ⟨?_,?_⟩
  · intro a ha b hb c hc v
    exact sub_eq_zero.mpr (hfixed (hsecond b hb _ (hfirst c hc v)) ⟨a,ha⟩)
  · change fixedCodim τ ⊤ ≤ Nat.log 2 (Nat.card E) + finrank (ZMod 2) (V ⧸ W) at hbound
    rw [hcodim] at hbound
    change finrank (ZMod 2) (V ⧸ fixedSpace (ρ.comp E.subtype) ⊤) ≤ rank E + 1 at hbound
    rw [fixedSpace_comp_map,← MonoidHom.range_eq_map,E.range_subtype] at hbound
    exact hbound
end Representation.BinaryOffender
