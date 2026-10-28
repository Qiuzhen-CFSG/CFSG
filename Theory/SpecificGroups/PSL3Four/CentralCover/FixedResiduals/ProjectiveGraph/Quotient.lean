module

public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Theory.GroupAction.CentralKernelFixedResidual
import Mathlib.Tactic.Group

/-!
# Projective fixed representatives for the graph automorphism of PSL₃

The actual center of SL₃ consists of scalar matrices of exponent dividing
three. For a projective graph fixed point represented by x, its displacement
k = x⁻¹γ(x) belongs to that center. Involutivity gives γ(k) = k⁻¹, so xk² is
a fixed representative of the same projective point. A central fixed matrix
is both its own inverse and of exponent three, hence trivial. Thus the
canonical central quotient induces an isomorphism on fixed subgroups.

This argument works over every field. It supplies the projective step for
the graph fixed-group calculation in Aschbacher--Smith 15.3.38, combined
manuscript of 1 March 2004, printed pp.1136–1137. The displacement argument
also appears for the related field and unitary actions in `ProjectiveField`
and `Theory.SpecificGroups.SU3.ProjectiveGraphFixed`.
-/

namespace Matrix.PSL3Four.GraphFixed
variable (K : Type*) [Field K]
private abbrev SL3 := SpecialLinearGroup (Fin 3) K

private theorem graphSL_involutive (x : SL3 K) :
    PSL3.OuterSolvable.graphSL K (PSL3.OuterSolvable.graphSL K x) = x :=
  (PSL3.OuterSolvable.graphSL K).left_inv x

private theorem central_cube (g : SL3 K) (hg : g ∈ Subgroup.center (SL3 K)) :
    g ^ 3 = 1 := by
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  have hr' : r ^ 3 = 1 := hr
  apply Subtype.ext
  change g.val ^ 3 = (1 : Matrix (Fin 3) (Fin 3) K)
  rw [← he]
  change (Matrix.diagonal (fun _ : Fin 3 => r)) ^ 3 = _
  simp only [Matrix.diagonal_pow]
  congr 1
  funext i
  exact hr'

private theorem central_transpose (g : SL3 K) (hg : g ∈ Subgroup.center (SL3 K)) :
    SpecialLinearGroup.transpose g = g := by
  obtain ⟨r, _, he⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  apply Subtype.ext
  change g.val.transpose = g.val
  rw [← he]
  exact Matrix.diagonal_transpose _

private def fixedProjection : (PSL3.OuterSolvable.graphSL K).fixedSubgroup →*
    (PSL3.OuterSolvable.graph K).fixedSubgroup :=
  MulAut.fixedSubgroupMap _ _ (QuotientGroup.mk' (Subgroup.center (SL3 K))) (fun _ => rfl)

/-- Every fixed class in SL₃/Z(SL₃) has an inverse-transpose fixed representative. -/
public theorem projectiveGraph_fixed_representative
    (b : (PSL3.OuterSolvable.graph K).fixedSubgroup) :
    ∃ x : (PSL3.OuterSolvable.graphSL K).fixedSubgroup,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 3) K)) x.val = b.val := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SL3 K)) b.val
  let a := PSL3.OuterSolvable.graphSL K
  let k := x⁻¹ * a x
  have hk : (QuotientGroup.mk' (Subgroup.center (SL3 K))) k = 1 := by
    dsimp only [k]
    rw [map_mul, map_inv]
    change (QuotientGroup.mk' _ x)⁻¹ * PSL3.OuterSolvable.graph K (QuotientGroup.mk' _ x) = 1
    rw [hx, (MulAut.mem_fixedSubgroup _ _).mp b.property, inv_mul_cancel]
  have hk3 : k ^ 3 = 1 := central_cube K k ((QuotientGroup.eq_one_iff k).mp hk)
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hck : a k = k⁻¹ := by
    simp [k, a, map_mul, map_inv, graphSL_involutive]
  have hcx : a x = x * k := by simp [k]
  have hz : a (x * k ^ 2) = x * k ^ 2 := by
    rw [map_mul, map_pow, hck, hcx]
    calc
      x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
      _ = x * k ^ 2 := by rw [hki]
  exact ⟨⟨x * k ^ 2, (MulAut.mem_fixedSubgroup _ _).mpr hz⟩,
    by simp [map_mul, map_pow, hk, hx]⟩

private theorem fixedProjection_injective : Function.Injective (fixedProjection K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : x.val ∈ Subgroup.center (SL3 K) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun z : (PSL3.OuterSolvable.graph K).fixedSubgroup => z.val) hx
  have hfix : x.val⁻¹ = x.val := by
    have h := (MulAut.mem_fixedSubgroup _ _).mp x.property
    change (SpecialLinearGroup.transpose x.val)⁻¹ = x.val at h
    rwa [central_transpose K x.val hx'] at h
  have hx2 : x.val * x.val = 1 := by
    calc
      _ = x.val⁻¹ * x.val := by rw [hfix]
      _ = 1 := inv_mul_cancel _
  have hx1 : x.val = 1 := by
    calc
      x.val = x.val ^ 3 := by rw [pow_succ', pow_two, hx2, mul_one]
      _ = 1 := central_cube K x.val hx'
  exact Subgroup.mem_bot.mpr (Subtype.ext hx1)

/-- Projectivization is an isomorphism on the inverse-transpose fixed subgroups. -/
public noncomputable def projectiveGraphFixedEquivSpecial :
    (PSL3.OuterSolvable.graph K).fixedSubgroup ≃*
      (PSL3.OuterSolvable.graphSL K).fixedSubgroup :=
  (MulEquiv.ofBijective (fixedProjection K) ⟨fixedProjection_injective K, by
    intro b
    obtain ⟨x, hx⟩ := projectiveGraph_fixed_representative K b
    exact ⟨x, Subtype.ext hx⟩⟩).symm

end Matrix.PSL3Four.GraphFixed
