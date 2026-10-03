module
public import Theory.Character.ClassFunction
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The negative eigenspace character of a central involution

The kernel of `ρ(z) + 1` is an invariant subspace. The projection
`(1 - ρ(z))/2`, together with cyclicity of trace, computes its character
as `(χ(g) - χ(zg))/2`. A choice of complex basis gives an actual character
on the standard coordinate space; no realization over the rationals is used.

Source: the central-involution decomposition in ABG III.8 Lemma 2, p.114.
-/

namespace Representation
noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]

@[expose] public def centralInvolutionMinus (ρ : Representation ℂ G V) (z : G)
    (hz : z ∈ Subgroup.center G) : Subrepresentation ρ where
  toSubmodule := (ρ z + 1).ker
  apply_mem_toSubmodule g := by
    intro v hv
    change ρ z v + v = 0 at hv
    change ρ z (ρ g v) + ρ g v = 0
    have hzg : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
    have heq : ρ z (ρ g v) = ρ g (ρ z v) := by
      change (ρ z * ρ g) v = (ρ g * ρ z) v
      rw [← map_mul, ← map_mul, hzg]
    rw [heq, ← map_add, hv, map_zero]

public theorem centralInvolutionMinus_character (ρ : Representation ℂ G V) (z : G)
    (hz : z ∈ Subgroup.center G) (hzsq : z ^ 2 = 1) (g : G) :
    (centralInvolutionMinus ρ z hz).toRepresentation.character g =
      (ρ.character g - ρ.character (z * g)) / 2 := by
  let W := centralInvolutionMinus ρ z hz
  have hsq (v : V) : ρ z (ρ z v) = v := by
    change (ρ z * ρ z) v = v
    rw [← map_mul, ← pow_two, hzsq, map_one]
    rfl
  let π : V →ₗ[ℂ] W.toSubmodule :=
    (((2 : ℂ)⁻¹ • (1 - ρ z) : Module.End ℂ V)).codRestrict W.toSubmodule (by
      intro v
      change ρ z ((2 : ℂ)⁻¹ • (v - ρ z v)) + (2 : ℂ)⁻¹ • (v - ρ z v) = 0
      rw [map_smul, map_sub, hsq, ← smul_add]
      simp)
  have hπ (w : W.toSubmodule) : π w = w := by
    apply Subtype.ext
    have hw : ρ z w.val + w.val = 0 := w.property
    have hw' : ρ z w.val = -w.val := eq_neg_of_add_eq_zero_left hw
    change (2 : ℂ)⁻¹ • (w.val - ρ z w.val) = w.val
    rw [hw', sub_neg_eq_add, ← two_smul ℂ, smul_smul]
    norm_num
  have hrep : W.toRepresentation g = π ∘ₗ (ρ g ∘ₗ W.toSubmodule.subtype) := by
    ext w
    exact (congrArg Subtype.val (hπ (W.toRepresentation g w))).symm
  change LinearMap.trace ℂ W.toSubmodule (W.toRepresentation g) = _
  rw [hrep, LinearMap.trace_comp_comm']
  have hmap : (ρ g ∘ₗ W.toSubmodule.subtype) ∘ₗ π =
      (2 : ℂ)⁻¹ • (ρ g - ρ (z * g)) := by
    ext v
    change ρ g ((2 : ℂ)⁻¹ • (v - ρ z v)) =
      (2 : ℂ)⁻¹ • (ρ g v - ρ (z * g) v)
    rw [map_smul, map_sub]
    congr 2
    change (ρ g * ρ z) v = ρ (z * g) v
    rw [← map_mul, Subgroup.mem_center_iff.mp hz g]
  rw [hmap, map_smul, map_sub]
  change (2 : ℂ)⁻¹ * (ρ.character g - ρ.character (z * g)) = _
  ring

/-- The negative eigenspace character is an actual complex character. -/
public theorem isCharacter_centralInvolutionMinus (ρ : Representation ℂ G V) (z : G)
    (hz : z ∈ Subgroup.center G) (hzsq : z ^ 2 = 1) :
    IsCharacter (fun g => (ρ.character g - ρ.character (z * g)) / 2) := by
  let W := centralInvolutionMinus ρ z hz
  let e := (Module.finBasis ℂ W.toSubmodule).equivFun
  let τ : Representation ℂ G (Fin (Module.finrank ℂ W.toSubmodule) → ℂ) :=
    (e.conjAlgEquiv ℂ).toMonoidHom.comp W.toRepresentation
  refine ⟨_, τ, ?_⟩
  funext g
  rw [← centralInvolutionMinus_character ρ z hz hzsq g]
  exact (LinearMap.trace_conj' (W.toRepresentation g) e).symm

end
end Representation
