module

public import Theory.Representation.SL3DoubledNaturalOffenders.Displacement
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Common fixed spaces and changes of multiplicity coordinates

An actual special linear change of the two multiplicity coordinates preserves
the natural SL₃ marking and transports the displacement bound. If the subgroup
contains both a nontrivial pure multiplicity transvection and a nonidentity
pure natural actor, projection to the first natural copy is injective but
cannot be onto. Thus the common fixed space has dimension strictly below 3m.
Keeping the common fixed space is essential in the maximal-rank case.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
-/

public section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix BinaryOffender
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

/-- Conjugating by a literal multiplicity actor leaves the natural marking unchanged. -/
theorem tensor_conjugate_multiplicity (g : SL F) (c d : MultiplicitySL F) :
    (MulAut.conj ((tensorRepresentation F).asGroupHom (1, c)))
      ((tensorRepresentation F).asGroupHom (g, d)) =
        (tensorRepresentation F).asGroupHom (g, c * d * c⁻¹) := by
  change (tensorRepresentation F).asGroupHom (1, c) *
    (tensorRepresentation F).asGroupHom (g, d) *
      ((tensorRepresentation F).asGroupHom (1, c))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (by simp) (by simp)

variable [Finite F]

/-- A nontrivial pure natural actor makes the common-fixed-space estimate strict
when a nontrivial pure upper multiplicity actor is present. -/
theorem fixedCodim_gt_three_mul_of_pure_upper {m : ℕ} (hF : Nat.card F = 2 ^ m)
    {A : Subgroup (Ambient F)} {g : SL F} (hg : g ≠ 1) {t : F} (ht : t ≠ 0)
    (ha : (tensorRepresentation F).asGroupHom
      (1, SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one t) ∈ A)
    (hb : (tensorRepresentation F).asGroupHom (g, 1) ∈ A) :
    3 * m < fixedCodim (action F) A := by
  let f : fixedSpace (action F) A →ₗ[ZMod 2] Natural F :=
    (LinearMap.proj 0).comp (fixedSpace (action F) A).subtype
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    exact upper_fixed_first_injective 1 ht
      (v.property ⟨_, ha⟩) (w.property ⟨_, ha⟩) hvw
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  have hd := fixedCodim_add_finrank (action F) A
  rw [finrank_space hF] at hd
  rw [finrank_natural hF] at hle
  by_contra hnot
  have hdim : Module.finrank (ZMod 2) (fixedSpace (action F) A) =
      Module.finrank (ZMod 2) (Natural F) := by
    rw [finrank_natural hF]
    omega
  let e := LinearEquiv.ofInjectiveOfFinrankEq f hf hdim
  have hs : Function.Surjective f := e.surjective
  apply hg
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  obtain ⟨w,hw⟩ := hs v
  have hbfix := w.property ⟨_,hb⟩
  change representation F g (multiplicityRepresentation F 1 w.val) = w.val at hbfix
  rw [map_one, Module.End.one_apply] at hbfix
  have h0 := congrFun hbfix 0
  change g.val.mulVec (f w) = f w at h0
  simpa only [hw, SpecialLinearGroup.coe_one, Matrix.one_mulVec] using h0

/-- The mixed-actor displacement bound after an actual multiplicity coordinate change. -/
theorem fixedCodim_ge_three_mul_of_conjugate_upper {m : ℕ}
    (hF : Nat.card F = 2 ^ m) {A : Subgroup (Ambient F)} (g : SL F)
    (c d : MultiplicitySL F) {t : F} (ht : t ≠ 0)
    (hc : c * d * c⁻¹ = SpecialLinearGroup.transvection (i := 0) (j := 1)
      zero_ne_one t)
    (ha : (tensorRepresentation F).asGroupHom (g, d) ∈ A) :
    3 * m ≤ fixedCodim (action F) A := by
  let b := (tensorRepresentation F).asGroupHom (1, c)
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom ha
  change (MulAut.conj ((tensorRepresentation F).asGroupHom (1, c)))
    ((tensorRepresentation F).asGroupHom (g, d)) ∈ _ at hmem
  rw [tensor_conjugate_multiplicity, hc] at hmem
  have h := fixedCodim_ge_three_mul_of_upper hF g ht hmem
  rwa [fixedCodim_map_conj] at h

/-- The strict common-fixed-space bound after a multiplicity coordinate change. -/
theorem fixedCodim_gt_three_mul_of_conjugate_pure {m : ℕ}
    (hF : Nat.card F = 2 ^ m) {A : Subgroup (Ambient F)} {g : SL F} (hg : g ≠ 1)
    (c d : MultiplicitySL F) {t : F} (ht : t ≠ 0)
    (hc : c * d * c⁻¹ = SpecialLinearGroup.transvection (i := 0) (j := 1)
      zero_ne_one t)
    (ha : (tensorRepresentation F).asGroupHom (1, d) ∈ A)
    (hb : (tensorRepresentation F).asGroupHom (g, 1) ∈ A) :
    3 * m < fixedCodim (action F) A := by
  let b := (tensorRepresentation F).asGroupHom (1, c)
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom ha
  change (MulAut.conj ((tensorRepresentation F).asGroupHom (1, c)))
    ((tensorRepresentation F).asGroupHom (1, d)) ∈ _ at hmem
  rw [tensor_conjugate_multiplicity, hc] at hmem
  have hmem' := Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hb
  change (MulAut.conj ((tensorRepresentation F).asGroupHom (1, c)))
    ((tensorRepresentation F).asGroupHom (g, 1)) ∈ _ at hmem'
  rw [tensor_conjugate_multiplicity] at hmem'
  simp only [mul_one, mul_inv_cancel] at hmem'
  have h := fixedCodim_gt_three_mul_of_pure_upper hF hg ht hmem hmem'
  rwa [fixedCodim_map_conj] at h

end Representation.SL3DoubledNaturalOffenders
