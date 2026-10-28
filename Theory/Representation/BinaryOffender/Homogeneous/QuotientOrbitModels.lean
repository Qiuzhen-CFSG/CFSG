module
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientTwist
public import Theory.Representation.BinaryOffender.Homogeneous.TwoTypeOrbit
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
/-!
# Characteristic quotient models of a homogeneous orbit

Normalizer conjugation twists a central-image constituent through the induced
actual automorphism of a characteristic quotient. If that quotient model has
two possible twisted types, a moved homogeneous seed has their product as the
model of its central orbit span. Full commutator generation ensures that a
moved original seed remains moved after taking the central image.

Source: Aschbacher–Smith A.1.40–42 and the moved-seed branch of D.3.5,
printed pp. 31–32 and 195–196.
-/
@[expose] public section
open Subgroup
namespace Representation.BinaryOffender.Homogeneous
variable {G V P W : Type*} [Group G] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V)

/-- The translated central seed has the quotient-automorphism twist of its
original model, using the actual normalizer operator. -/
theorem IsIrrPlusWith.centralConjugate_equiv_quotient_twist
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (t : T)
    (N : Subgroup X) [N.Characteristic] (q : (X ⧸ N) ≃* P)
    (τ : Representation (ZMod 2) P W)
    (b : (quotientImage ρ X I hI.invariant).toRepresentation.Equiv
      (τ.comp (q.toMonoidHom.comp (QuotientGroup.mk' N)))) :
    ∃ a : MulAut P, Nonempty
      ((centralConjugate ρ X T hI.normalizes t
        (quotientImage ρ X I hI.invariant)).toRepresentation.Equiv
        ((τ.comp a.toMonoidHom).comp (q.toMonoidHom.comp (QuotientGroup.mk' N)))) := by
  let S := quotientImage ρ X I hI.invariant
  let C := centralConjugate ρ X T hI.normalizes t S
  let θ := normalizerQuotientRepresentation ρ X
  let tN : normalizer (X : Set G) := ⟨t.val,hI.normalizes t.property⟩
  let n := X.normalizerMonoidHom
    ⟨t.val⁻¹,hI.normalizes (T.inv_mem t.property)⟩
  let a := q.symm.trans ((quotientAut N n).trans q)
  let e := (Submodule.equivMapOfInjective (θ tN) (θ.apply_bijective tN).1 S.toSubmodule).trans
    (LinearEquiv.ofEq _ _ (centralConjugate_toSubmodule ρ X T hI.normalizes t S).symm)
  have he (v : S.toSubmodule) : (e v : V ⧸ fixedSpace ρ X) = θ tN v := rfl
  have hcomm (x : X) (v : V ⧸ fixedSpace ρ X) :
      θ tN (fixedQuotientRepresentation ρ X (n x) v) =
        fixedQuotientRepresentation ρ X x (θ tN v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change (fixedSpace ρ X).mkQ (ρ t.val (ρ (n x).val v)) =
        (fixedSpace ρ X).mkQ (ρ x.val (ρ t.val v))
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp only [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left]
  have heq (x : X) (v : S.toSubmodule) :
      e (S.toRepresentation (n x) v) = C.toRepresentation x (e v) := by
    apply Subtype.ext
    change (e (S.toRepresentation (n x) v)).val =
      fixedQuotientRepresentation ρ X x (e v).val
    rw [he,he]
    exact hcomm x v.val
  refine ⟨a,⟨Representation.Equiv.mk (e.symm.trans b.toLinearEquiv) ?_⟩⟩
  intro x
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := e.surjective v
  change b (e.symm (C.toRepresentation x (e w))) =
    τ (a (q (QuotientGroup.mk' N x))) (b (e.symm (e w)))
  rw [←heq,e.symm_apply_apply,e.symm_apply_apply]
  have hb := Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap (n x) w
  trans τ (q (QuotientGroup.mk' N (n x))) (b w)
  · exact hb
  change τ (q (QuotientGroup.mk' N (n x))) (b w) =
    τ (q (quotientAut N n (q.symm (q (QuotientGroup.mk' N x))))) (b w)
  rw [q.symm_apply_apply,quotientAut_apply_mk]

/-- Movement of the original full-commutator seed survives in its central
image orbit; central errors cannot conceal it. -/
theorem IsIrrPlusWith.central_span_ne_of_orbit_ne
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (hmoved : orbitSpan ρ T I ≠ I) :
    (centralTypeAction ρ X T hI.normalizes).span
      (quotientImage ρ X I hI.invariant) ≠ quotientImage ρ X I hI.invariant := by
  intro he
  have himage := congrArg Subrepresentation.toSubmodule he
  rw [centralTypeAction_span] at himage
  change centralOrbitSpan ρ X T hI.normalizes (I.map (fixedSpace ρ X).mkQ) =
    I.map (fixedSpace ρ X).mkQ at himage
  rw [←orbitSpan_quotientImage] at himage
  exact hmoved (le_antisymm (le_of_quotientImage_le ρ
    (orbitSpan_full_commutator ρ hI.normalizes hI.isIrrPlus) hI.invariant himage.le)
    (le_orbitSpan ρ T I))

/-- An original moved homogeneous seed with two quotient-automorphism types
has their actual direct-product model on its central orbit span. -/
theorem IsIrrPlusWith.central_span_equiv_pair
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I)
    (N : Subgroup X) [N.Characteristic] (q : (X ⧸ N) ≃* P)
    {W₁ : Type*} [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (τ₀ : Representation (ZMod 2) P W) (τ₁ : Representation (ZMod 2) P W₁)
    (b : (quotientImage ρ X I hI.invariant).toRepresentation.Equiv
      (τ₀.comp (q.toMonoidHom.comp (QuotientGroup.mk' N))))
    (hmoved : orbitSpan ρ T I ≠ I)
    (htypes : ∀ a : MulAut P, Nonempty (Representation.Equiv (τ₀.comp a.toMonoidHom) τ₀) ∨
      Nonempty (Representation.Equiv (τ₀.comp a.toMonoidHom) τ₁)) :
    Nonempty (((centralTypeAction ρ X T hI.normalizes).span
      (quotientImage ρ X I hI.invariant)).toRepresentation.Equiv
      ((τ₀.prod τ₁).comp (q.toMonoidHom.comp (QuotientGroup.mk' N)))) := by
  let c := centralTypeAction ρ X T hI.normalizes
  let S := quotientImage ρ X I hI.invariant
  let f := q.toMonoidHom.comp (QuotientGroup.mk' N)
  have hh : homogeneousPart S (c.span S).toSubmodule = S.toSubmodule := by
    rw [centralTypeAction_span]
    exact hI.central_homogeneous ρ
  have hmodels : ∀ s : T,
      Nonempty ((c.conjugate s S).toRepresentation.Equiv (τ₀.comp f)) ∨
      Nonempty ((c.conjugate s S).toRepresentation.Equiv (τ₁.comp f)) := by
    intro s
    obtain ⟨a,⟨ea⟩⟩ := hI.centralConjugate_equiv_quotient_twist ρ s N q τ₀ b
    rcases htypes a with h | h
    · obtain ⟨d⟩ := h
      let df : Representation.Equiv ((τ₀.comp a.toMonoidHom).comp f) (τ₀.comp f) :=
        Representation.Equiv.mk d.toLinearEquiv (fun x => by
          apply LinearMap.ext
          intro v
          exact Representation.IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (f x) v)
      exact Or.inl ⟨ea.trans df⟩
    · obtain ⟨d⟩ := h
      let df : Representation.Equiv ((τ₀.comp a.toMonoidHom).comp f) (τ₁.comp f) :=
        Representation.Equiv.mk d.toLinearEquiv (fun x => by
          apply LinearMap.ext
          intro v
          exact Representation.IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (f x) v)
      exact Or.inr ⟨ea.trans df⟩
  exact c.nonempty_span_equiv_prod_of_two_models S
    (quotientImage_irreducible ρ hI.isIrrPlus) hh (τ₀.comp f) (τ₁.comp f) b
    (hI.central_span_ne_of_orbit_ne ρ hmoved) hmodels

end Representation.BinaryOffender.Homogeneous
