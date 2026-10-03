module

public import Theory.Character.ModularBlock.GroupAlgebraLocalTrace
public import Theory.Character.ModularBlock.IdempotentTrace
public import Theory.Character.ModularBlock.IdempotentRestriction

/-!
# Central Idempotent Support

A central idempotent in the group algebra of a finite group over a
characteristic-zero local domain has zero coefficient at every nontrivial
involution, provided two is a nonunit. Restrict its right-ideal summand to
the involution subgroup. The subgroup algebra is local and the summand is
finite projective, so its trace vanishes at the nonidentity element.
The central-coefficient trace formula then gives the group order times the
involution coefficient as zero; characteristic zero and the domain
hypothesis allow cancellation.

The intermediate interfaces retain explicit projectivity and freeness
hypotheses for reuse. This is the unconditional support calculation used in
weak block orthogonality in the modular proof of Glauberman's Z* theorem.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CentralIdempotentSupport.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

open Module CategoryTheory

namespace ModularBlock.CentralIdempotentSupport

universe u v w

attribute [local instance] Fintype.ofFinite

/-- For an idempotent `e`, the trace on its right-ideal summand equals the
trace of left multiplication followed by the ambient projection `x ↦ x * e`. -/
theorem trace_mulLeft_comp_mulRight_eq_trace_rightIdeal
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    (g : G) :
    LinearMap.trace R (MonoidAlgebra R G)
        ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e)) =
      LinearMap.trace R (rightIdeal R e) (rightIdealAction R e g) := by
  have hp : IsIdempotentElem (LinearMap.mulRight R e) := by
    change (LinearMap.mulRight R e).comp (LinearMap.mulRight R e) =
      LinearMap.mulRight R e
    rw [← LinearMap.mulRight_mul, heidem]
  have hcomm :
      (LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e) =
        (LinearMap.mulRight R e).comp
          (LinearMap.mulLeft R (MonoidAlgebra.of R G g)) := by
    ext x
    simp [LinearMap.comp_apply, mul_assoc]
  simpa only [rightIdeal, rightIdealAction] using
    trace_comp_idempotent_eq_trace_range
      (LinearMap.mulRight R e)
      (LinearMap.mulLeft R (MonoidAlgebra.of R G g)) hp hcomm

/-- The coefficient formula can be read directly from the right-ideal
summand's trace. -/
theorem trace_rightIdealAction_eq_card_mul_coeff
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    (g : G) :
    LinearMap.trace R (rightIdeal R e) (rightIdealAction R e g) =
      (Nat.card G : R) * e.coeff g⁻¹ := by
  rw [← trace_mulLeft_comp_mulRight_eq_trace_rightIdeal e heidem g,
    trace_mulLeft_comp_mulRight e hecenter g]

/-- In a characteristic-zero domain, vanishing of the right-ideal trace
forces the corresponding central-idempotent coefficient to vanish. -/
theorem coeff_inv_eq_zero_of_trace_rightIdealAction_eq_zero
    {R : Type u} {G : Type v} [CommRing R] [IsDomain R] [CharZero R]
    [Group G] [Finite G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    (g : G)
    (htrace : LinearMap.trace R (rightIdeal R e) (rightIdealAction R e g) = 0) :
    e.coeff g⁻¹ = 0 := by
  have hmul : (Nat.card G : R) * e.coeff g⁻¹ = 0 := by
    rw [← trace_rightIdealAction_eq_card_mul_coeff e heidem hecenter g]
    exact htrace
  rcases mul_eq_zero.mp hmul with hcard | hcoeff
  · have hcard' : (Nat.card G : R) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    exact (hcard' hcard).elim
  · exact hcoeff

/-- A central idempotent has zero coefficient at the image of a nonidentity
element whenever its regular summand restricts projectively to a finite
commutative subgroup whose group algebra is local.  This is the precise
projective/free bridge used for an involution subgroup. -/
theorem coeff_inv_eq_zero_of_projective_restriction
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e.coeff (phi c)⁻¹ = 0 := by
  apply coeff_inv_eq_zero_of_trace_rightIdealAction_eq_zero
    e heidem hecenter (phi c)
  simpa [rightIdealRepresentation] using
    trace_representation_of_projective_asModule
      (restrictedRightIdealRepresentation R e phi) c hc

/-- Local-base-ring form of `coeff_inv_eq_zero_of_projective_restriction`.
The freeness of the idempotent summand and its complement over `R` is now a
consequence rather than an input. -/
theorem coeff_inv_eq_zero_of_projective_restriction_of_local
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e.coeff (phi c)⁻¹ = 0 := by
  let p : MonoidAlgebra R G →ₗ[R] MonoidAlgebra R G := LinearMap.mulRight R e
  have hp : IsIdempotentElem p := by
    change (LinearMap.mulRight R e).comp (LinearMap.mulRight R e) =
      LinearMap.mulRight R e
    rw [← LinearMap.mulRight_mul, heidem]
  let : Module.Free R (rightIdeal R e) :=
    free_range_of_isIdempotentElem_of_isLocalRing p hp
  let : Module.Finite R (rightIdeal R e) := inferInstance
  let : Module.Free R (LinearMap.ker (LinearMap.mulRight R e)) :=
    free_ker_of_isIdempotentElem_of_isLocalRing p hp
  let : Module.Finite R (LinearMap.ker (LinearMap.mulRight R e)) := by
    change Module.Finite R (LinearMap.ker p)
    rw [LinearMap.IsIdempotentElem.ker_eq_range hp]
    infer_instance
  exact coeff_inv_eq_zero_of_projective_restriction
    phi c hc e heidem hecenter

/-- Order-two specialization of
`coeff_inv_eq_zero_of_projective_restriction`.  In applications `C` is a
fixed concrete model of the cyclic group of order two and `c` its generator. -/
theorem coeff_involution_eq_zero_of_projective_restriction
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (s : G) (hphi : phi c = s) (hsq : s * s = 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e.coeff s = 0 := by
  have h := coeff_inv_eq_zero_of_projective_restriction
    phi c hc e heidem hecenter
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsq
  simpa [hphi, hs_inv] using h

/-- Fully local order-two form.  Its remaining hypotheses are exactly the two
restriction facts: the cyclic group algebra is local, and the restricted
block-regular summand is finite projective over it. -/
theorem coeff_involution_eq_zero_of_projective_restriction_of_local
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (s : G) (hphi : phi c = s) (hsq : s * s = 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e.coeff s = 0 := by
  have h := coeff_inv_eq_zero_of_projective_restriction_of_local
    phi c hc e heidem hecenter
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsq
  simpa [hphi, hs_inv] using h

/-- A central idempotent over a characteristic-zero local domain in which
`2` is a nonunit has zero coefficient at every nontrivial involution.

This is the unconditional support theorem needed for weak block
orthogonality: the order-two subgroup algebra is local, restriction of the
regular module is projective, and the idempotent right-ideal summand is a
finite split summand. -/
theorem coeff_involution_eq_zero
    {R : Type u} {G : Type v}
    [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [Group G] [Finite G]
    (h2 : ¬ IsUnit (2 : R))
    (s : G) (hsne : s ≠ 1) (hsq : s * s = 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G)) :
    e.coeff s = 0 := by
  have hsord : orderOf s = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two, hsq]
    · exact hsne
  let S : Subgroup G := Subgroup.zpowers s
  have hScard : Nat.card S = 2 := by
    dsimp [S]
    rw [Nat.card_zpowers, hsord]
  let : Finite S := Nat.finite_of_card_ne_zero (by omega)
  let : CommGroup S := IsCyclic.commGroup
  let c : S := ⟨s, Subgroup.mem_zpowers s⟩
  have hc : c ≠ 1 := by
    intro h
    apply hsne
    exact congrArg Subtype.val h
  let : IsLocalRing (MonoidAlgebra R S) :=
    isLocalRing_monoidAlgebra_of_card_two h2 hScard
  let : Module.Projective (MonoidAlgebra R S)
      (restrictedRightIdealRepresentation R e S.subtype).asModule :=
    projective_restrictedRightIdeal_asModule e heidem S
  let : Module.Finite (MonoidAlgebra R S)
      (restrictedRightIdealRepresentation R e S.subtype).asModule :=
    finite_restrictedRightIdeal_asModule e heidem S
  exact coeff_involution_eq_zero_of_projective_restriction_of_local
    (R := R) (C := S) (G := G) S.subtype c hc s rfl hsq
      e heidem hecenter

end ModularBlock.CentralIdempotentSupport

