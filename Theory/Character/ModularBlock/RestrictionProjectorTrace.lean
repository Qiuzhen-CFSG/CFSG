module

public import Theory.Character.ModularBlock.MixedConjugationTrace
public import Theory.Character.ModularBlock.ProjectorTrace

/-!
# Restriction projections from mixed traces

An equality of mixed traces on the ambient group algebra determines the local
principal-block projection of every restricted ambient irreducible character.
The local and ambient principal congruence block data can be chosen independently;
the mixed-trace equality is the only compatibility hypothesis.

Weighting a left-right trace by a character and summing over the right factor
recovers the trace in that representation. For the local projector, complete
character expansion and the central-idempotent action identify this trace with
the local projection. For the ambient projector, character orthogonality extracts
the desired block coefficient. The scalar product is linear in its first argument.

Sources: the ordinary character orthogonality calculation in
`Theory.Character.Orthogonality`, the projector action in `PrincipalSelector`,
and the mixed block trace formula in `MixedConjugationTrace`.
-/

public section
noncomputable section
open scoped BigOperators
open ModularBlock PrincipalBlockConstruction BlockOrthogonality MixedConjugationTrace
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.RestrictionProjectorTrace
variable {G : Type*} [Group G] [Finite G]

private theorem trace_left_right (c : MonoidAlgebra ℂ G) (g : G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      ((LinearMap.mulLeft ℂ c).comp
        (LinearMap.mulRight ℂ (MonoidAlgebra.of ℂ G g⁻¹))) =
      ∑ x : G, c.coeff (x * g * x⁻¹) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  change (c * (MonoidAlgebra.single x 1 * MonoidAlgebra.single g⁻¹ 1)).coeff x = _
  simp [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_mul_single_apply, mul_assoc]

private theorem weighted_trace_left_right
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (c : MonoidAlgebra ℂ G) :
    (∑ g : G, LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      ((LinearMap.mulLeft ℂ c).comp
        (LinearMap.mulRight ℂ (MonoidAlgebra.of ℂ G g⁻¹))) * rho.character g) =
      (Nat.card G : ℂ) * LinearMap.trace ℂ V (rho.asAlgebraHom c) := by
  classical
  simp_rw [trace_left_right, Finset.sum_mul]
  rw [Finset.sum_comm, groupAlgebra_trace]
  have hsum (x : G) :
      (∑ g : G, c.coeff (x * g * x⁻¹) * rho.character g) =
        ∑ g : G, c.coeff g * rho.character g := by
    apply Fintype.sum_equiv (MulAut.conj x).toEquiv
    intro g
    simp [MulAut.conj_apply, Representation.char_conj]
  simp_rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card]

omit [Finite G] in
private theorem asAlgebraHom_subtype
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) (H : Subgroup G) (c : MonoidAlgebra ℂ H) :
    rho.asAlgebraHom (MonoidAlgebra.mapDomainRingHom ℂ H.subtype c) =
      Representation.asAlgebraHom (rho.comp H.subtype) c := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add c e hc he => rw [map_add, map_add, hc, he, map_add]
  | single h r =>
    rw [show (MonoidAlgebra.single h r : MonoidAlgebra ℂ H) =
      r • MonoidAlgebra.single h 1 by simp]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidHom.comp_apply]

private theorem trace_principal_projection
    (b : PrincipalCongruenceBlockData G)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (a : G) :
    LinearMap.trace ℂ V (rho a * rho.asAlgebraHom (principalBlockElement b)) =
      ∑ j ∈ b.block, classFunctionInner (characterClassFunction rho) (b.chi j) *
        b.chi j (ConjClasses.mk a) := by
  classical
  have hchar (g : G) : rho.character g =
      ∑ j : b.I, classFunctionInner (characterClassFunction rho) (b.chi j) *
        b.chi j (ConjClasses.mk g) :=
    completeFamily_apply_eq_sum_inner b.complete (characterClassFunction rho) (ConjClasses.mk g)
  have hproject (j : b.I) :
      (∑ h : G, (principalBlockElement b).coeff h * b.chi j (ConjClasses.mk (a * h))) =
        if j ∈ b.block then b.chi j (ConjClasses.mk a) else 0 := by
    obtain ⟨n, sigma, hsigma⟩ := (b.complete.1 j).1
    have ht := CharacterwiseProjection.trace_left_groupAlgebra_mul sigma a
      (principalBlockElement b)
    rw [principalBlockElement_action b j sigma hsigma] at ht
    rw [hsigma]
    change (∑ h : G, (principalBlockElement b).coeff h * sigma.character (a * h)) = _
    rw [← ht]
    split_ifs <;> simp only [one_smul, zero_smul, mul_one, mul_zero, map_zero]
    rfl
  rw [CharacterwiseProjection.trace_left_groupAlgebra_mul]
  simp_rw [hchar, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : b.I, classFunctionInner (characterClassFunction rho) (b.chi j) *
        (∑ h : G, (principalBlockElement b).coeff h * b.chi j (ConjClasses.mk (a * h))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by simp_rw [hproject]; simp

private theorem weighted_principalBlock
    (d : PrincipalCongruenceBlockData G) (a : G) (i : d.I) :
    (Nat.card G : ℂ)⁻¹ * (∑ g : G,
      LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedLeftRight (principalBlockElement d) a g) *
          d.chi i (ConjClasses.mk g)) =
      if i ∈ d.block then d.chi i (ConjClasses.mk a) else 0 := by
  classical
  simp_rw [principalBlock_leftRight_trace, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ j ∈ d.block, d.chi j (ConjClasses.mk a) *
        classFunctionInner (d.chi i) (d.chi j) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold classFunctionInner
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = _ := by
      simp_rw [completeFamily_orthonormal d.complete]
      simp

/-- Equality of mixed traces extracts the local principal projection of each
restricted ambient irreducible character. -/
theorem restriction_projection_of_mixed_trace
    (d : PrincipalCongruenceBlockData G)
    (H : Subgroup G) (b : PrincipalCongruenceBlockData H) (a : H)
    (htrace : ∀ g : G,
      let B := MonoidAlgebra.mapDomainRingHom ℂ H.subtype (principalBlockElement b)
      LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        ((LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ G (a : G) * B)).comp
          (LinearMap.mulRight ℂ (MonoidAlgebra.of ℂ G g⁻¹))) =
      LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedLeftRight (principalBlockElement d) (a : G) g))
    (i : d.I) :
    (∑ j ∈ b.block,
      scalarProduct H (fun h => d.chi i (ConjClasses.mk (h : G)))
        (fun h => b.chi j (ConjClasses.mk h)) * b.chi j (ConjClasses.mk a)) =
      if i ∈ d.block then d.chi i (ConjClasses.mk (a : G)) else 0 := by
  let : Fintype H := Fintype.ofFinite H
  classical
  obtain ⟨n, rho, hrho⟩ := (d.complete.1 i).1
  let B := MonoidAlgebra.mapDomainRingHom ℂ H.subtype (principalBlockElement b)
  let c := MonoidAlgebra.of ℂ G (a : G) * B
  have hlocal :
      (∑ j ∈ b.block,
        scalarProduct H (fun h => d.chi i (ConjClasses.mk (h : G)))
          (fun h => b.chi j (ConjClasses.mk h)) * b.chi j (ConjClasses.mk a)) =
        LinearMap.trace ℂ (Fin n → ℂ) (rho.asAlgebraHom c) := by
    rw [show rho.asAlgebraHom c =
        rho (a : G) * Representation.asAlgebraHom (rho.comp H.subtype)
          (principalBlockElement b) by
      dsimp [c, B]
      rw [map_mul, asAlgebraHom_subtype, Representation.asAlgebraHom_of]]
    rw [show rho (a : G) = (rho.comp H.subtype) a by rfl,
      trace_principal_projection]
    apply Finset.sum_congr rfl
    intro j _
    rw [hrho]
    rfl
  rw [hlocal]
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  calc
    _ = (Nat.card G : ℂ)⁻¹ * (∑ g : G,
        LinearMap.trace ℂ (MonoidAlgebra ℂ G)
          ((LinearMap.mulLeft ℂ c).comp
            (LinearMap.mulRight ℂ (MonoidAlgebra.of ℂ G g⁻¹))) *
          rho.character g) := by
      rw [weighted_trace_left_right, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    _ = (Nat.card G : ℂ)⁻¹ * (∑ g : G,
        LinearMap.trace ℂ (MonoidAlgebra ℂ G)
          (projectedLeftRight (principalBlockElement d) (a : G) g) *
            d.chi i (ConjClasses.mk g)) := by
      apply congrArg ((Nat.card G : ℂ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro g _
      rw [show LinearMap.trace ℂ (MonoidAlgebra ℂ G)
          ((LinearMap.mulLeft ℂ c).comp
            (LinearMap.mulRight ℂ (MonoidAlgebra.of ℂ G g⁻¹))) = _ from htrace g]
      rw [hrho]
      rfl
    _ = _ := weighted_principalBlock d (a : G) i

end ModularBlock.RestrictionProjectorTrace
