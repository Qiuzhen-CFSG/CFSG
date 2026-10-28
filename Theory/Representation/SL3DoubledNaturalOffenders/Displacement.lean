module

public import Theory.Representation.SL3DoubledNaturalOffenders.Model
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Models

/-!
# Displacement from nontrivial multiplicity transvections

If the multiplicity factor is an upper transvection with nonzero parameter,
the first coordinate of a fixed vector determines the second. This remains
true with any simultaneous natural SL₃ factor. Evaluating the first coordinate
therefore injects the common fixed space into one natural copy, giving binary
codimension at least 3m when the field has order 2^m.

This is the displacement half of the doubled-natural offender estimate in
Aschbacher–Smith, B.5.10(2), printed p.109 of the 1 March 2004 manuscript.
It does not supply normalizer coverage or exclude the maximal actor-rank case.
-/

public section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix BinaryOffender
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- The literal first-coordinate formula for a mixed natural/multiplicity actor. -/
theorem tensor_upper_first (g : SL F) (t : F) (v : Space F) :
    tensorRepresentation F (g, SpecialLinearGroup.transvection (i := 0) (j := 1)
      zero_ne_one t) v 0 = g.val.mulVec (v 0 + t • v 1) := by
  change g.val.mulVec (multiplicity F
    (SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one t).val v 0) = _
  simp [multiplicity, SpecialLinearGroup.transvection_coe, Matrix.one_apply]

/-- Fixed vectors of a mixed actor with nontrivial upper multiplicity factor
are determined by their first natural coordinate. No involution premise is needed. -/
theorem upper_fixed_first_injective (g : SL F) {t : F} (ht : t ≠ 0)
    {v w : Space F}
    (hv : tensorRepresentation F (g, SpecialLinearGroup.transvection (i := 0) (j := 1)
      zero_ne_one t) v = v)
    (hw : tensorRepresentation F (g, SpecialLinearGroup.transvection (i := 0) (j := 1)
      zero_ne_one t) w = w)
    (hvw : v 0 = w 0) : v = w := by
  have hv0 := congrFun hv 0
  have hw0 := congrFun hw 0
  rw [tensor_upper_first] at hv0 hw0
  have hsum : v 0 + t • v 1 = w 0 + t • w 1 := by
    apply (SpecialLinearGroup.toLin' g).injective
    exact hv0.trans (hvw.trans hw0.symm)
  rw [hvw] at hsum
  have h1 : v 1 = w 1 := by
    have hs := add_left_cancel hsum
    funext j
    exact mul_left_cancel₀ ht (congrFun hs j)
  funext i
  fin_cases i <;> assumption

variable [Finite F]

/-- The binary dimension of the natural copy under the specified field algebra. -/
theorem finrank_natural {m : ℕ} (hF : Nat.card F = 2 ^ m) :
    Module.finrank (ZMod 2) (Natural F) = 3 * m := by
  simp [Natural, Module.finrank_pi_fintype, NaturalTensor.finrank_field F hF]

/-- The binary dimension of the two identically marked copies. -/
theorem finrank_space {m : ℕ} (hF : Nat.card F = 2 ^ m) :
    Module.finrank (ZMod 2) (Space F) = 6 * m := by
  simp [Space, Module.finrank_pi_fintype, finrank_natural hF]
  omega

/-- An actual ambient subgroup containing the specified mixed actor has
fixed codimension at least three times the field degree. -/
theorem fixedCodim_ge_three_mul_of_upper {m : ℕ} (hF : Nat.card F = 2 ^ m)
    {A : Subgroup (Ambient F)} (g : SL F) {t : F} (ht : t ≠ 0)
    (ha : (tensorRepresentation F).asGroupHom
      (g, SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one t) ∈ A) :
    3 * m ≤ fixedCodim (action F) A := by
  let f : fixedSpace (action F) A →ₗ[ZMod 2] Natural F :=
    (LinearMap.proj 0).comp (fixedSpace (action F) A).subtype
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact upper_fixed_first_injective g ht
      (v.property ⟨_, ha⟩) (w.property ⟨_, ha⟩) hvw
  have hb := LinearMap.finrank_le_finrank_of_injective hf
  rw [finrank_natural hF] at hb
  have hd := fixedCodim_add_finrank (action F) A
  rw [finrank_space hF] at hd
  omega

/-- In particular such a mixed actor excludes every offender of rank below 3m. -/
theorem not_offender_of_upper_of_rank_lt {m : ℕ} (hF : Nat.card F = 2 ^ m)
    {A : Subgroup (Ambient F)} (g : SL F) {t : F} (ht : t ≠ 0)
    (ha : (tensorRepresentation F).asGroupHom
      (g, SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one t) ∈ A)
    (hr : rank A < 3 * m) : ¬ IsOffender (action F) A := by
  intro hA
  exact (not_lt_of_ge ((fixedCodim_ge_three_mul_of_upper hF g ht ha).trans hA.2)) hr

end Representation.SL3DoubledNaturalOffenders
