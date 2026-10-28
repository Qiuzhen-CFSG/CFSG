module

public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.ClosedSubgroup.VanishingIdeal

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An identity tangent vector of the ambient group comes from a closed
subgroup exactly when it annihilates the subgroup's vanishing ideal. -/
public theorem identityTangent_inclusion_range_iff_vanishingIdeal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (D : IdentityPointDerivation G) :
    D ∈ LinearMap.range (identityTangentMorphismLinearMap H.inclusion) ↔
      ∀ f ∈ H.vanishingIdeal, D f = 0 := by
  constructor
  · rintro ⟨E, rfl⟩ f hf
    rw [identityTangentMorphismLinearMap_apply]
    change E (H.restrictionRingHom f) = 0
    have hzero : H.restrictionRingHom f = 0 := hf
    rw [hzero]
    exact map_zero E
  · intro hvan
    let r : G.PolynomialFunction →ₐ[k]
        H.carrierVariety.PolynomialFunction :=
      H.inclusion.toVariety.pullbackAlgHom
    have hr : Function.Surjective r := H.restrictionRingHom_surjective
    let s : H.carrierVariety.PolynomialFunction → G.PolynomialFunction :=
      Function.surjInv hr
    have hs : Function.RightInverse s r := Function.rightInverse_surjInv hr
    have hDker (a : G.PolynomialFunction) (ha : r a = 0) : D a = 0 := by
      apply hvan a
      change H.restrictionRingHom a = 0
      exact ha
    have hs_eval (b : H.carrierVariety.PolynomialFunction) :
        s b 1 = b 1 := by
      have hb := congrArg
        (fun q : H.carrierVariety.PolynomialFunction => q 1) (hs b)
      change s b (H.inclusion.onPoints 1) = b 1 at hb
      rw [map_one] at hb
      exact hb
    let E : IdentityPointDerivation H.carrierVariety := {
      toLinearMap := {
        toFun := fun b => D (s b)
        map_add' := by
          intro b c
          have hz : r (s (b + c) - (s b + s c)) = 0 := by
            rw [map_sub, map_add, hs (b + c), hs b, hs c, sub_self]
          have hd := hDker _ hz
          rw [map_sub, map_add, sub_eq_zero] at hd
          exact hd
        map_smul' := by
          intro c b
          have hz : r (s (c • b) - c • s b) = 0 := by
            rw [map_sub, map_smul, hs (c • b), hs b, sub_self]
          have hd := hDker _ hz
          rw [map_sub, sub_eq_zero] at hd
          exact hd.trans (D.toLinearMap.map_smul c (s b)) }
      map_one_eq_zero' := by
        have hz : r (s 1 - 1) = 0 := by
          rw [map_sub, hs, map_one, sub_self]
        have hd := hDker _ hz
        rw [map_sub, D.map_one_eq_zero, sub_zero] at hd
        exact hd
      leibniz' := by
        intro b c
        have hz : r (s (b * c) - s b * s c) = 0 := by
          rw [map_sub, map_mul, hs (b * c), hs b, hs c, sub_self]
        have hd := hDker _ hz
        rw [map_sub, sub_eq_zero] at hd
        change D (s (b * c)) = b 1 * D (s c) + c 1 * D (s b)
        rw [hd, D.leibniz]
        change s b 1 * D (s c) + s c 1 * D (s b) =
          b 1 * D (s c) + c 1 * D (s b)
        rw [hs_eval b, hs_eval c] }
    refine ⟨E, ?_⟩
    apply Derivation.ext
    intro a
    change D (s (r a)) = D a
    have hz : r (s (r a) - a) = 0 := by
      rw [map_sub, hs, sub_self]
    have hd := hDker _ hz
    rw [map_sub, sub_eq_zero] at hd
    exact hd

end Theory.AlgebraicGroup.Bor1
