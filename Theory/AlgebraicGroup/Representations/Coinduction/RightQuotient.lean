module

public import Mathlib.RepresentationTheory.Coinduced

universe u v w

/-! Coinduction realized on functions on right cosets. -/

open scoped MonoidAlgebra
open Representation

namespace Theory.AlgebraicGroup

section

@[expose]
public noncomputable def Subgroup.rightCosetCorrection
    {G : Type u} [Group G] (S : Subgroup G) (g : G) : S :=
  ⟨g * (@Quotient.mk' G (QuotientGroup.rightRel S) g).out⁻¹,
    QuotientGroup.rightRel_apply.mp
      (Quotient.eq'.mp (Quotient.out_eq
        (@Quotient.mk' G (QuotientGroup.rightRel S) g)))⟩

public lemma Subgroup.rightCosetCorrection_mul_out
    {G : Type u} [Group G] (S : Subgroup G) (g : G) :
    (Subgroup.rightCosetCorrection S g).1 *
        (@Quotient.mk' G (QuotientGroup.rightRel S) g).out = g := by
  simp [Subgroup.rightCosetCorrection]

@[expose]
public noncomputable def Representation.coindVEquivRightQuotientPi
    {k : Type u} {G : Type v} [Field k] [Group G]
    (S : Subgroup G) (A : Rep.{w} k S) :
    Representation.coindV S.subtype A.ρ ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel S) → A) := by
  classical
  letI := QuotientGroup.rightRel S
  let Q := Quotient (QuotientGroup.rightRel S)
  let i : Q → G := fun q => q.out
  have hi (q : Q) : Quotient.mk' (i q) = q := by
    exact Quotient.out_eq q
  let γ (g : G) : S := Subgroup.rightCosetCorrection S g
  have hmk (s : S) (g : G) : Quotient.mk' (s.1 * g) = Quotient.mk' g :=
    Quotient.eq'.2 (QuotientGroup.rightRel_apply.2 (by simp))
  have hγ (s : S) (g : G) : γ (s.1 * g) = s * γ g := by
    apply Subtype.ext
    have hout := congrArg Quotient.out (hmk s g)
    change s.1 * g * (Quotient.mk' (s.1 * g)).out⁻¹ =
      s.1 * (g * (Quotient.mk' g).out⁻¹)
    rw [hout]
    simp only [mul_assoc]
  let toFun : Representation.coindV S.subtype A.ρ →ₗ[k] (Q → A) :=
    { toFun := fun f q => f.1 (i q)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let invFun : (Q → A) →ₗ[k] Representation.coindV S.subtype A.ρ :=
    { toFun := fun x => ⟨fun g => A.ρ (γ g) (x (Quotient.mk' g)), by
          intro s g
          change A.ρ (γ (s.1 * g)) (x (Quotient.mk' (s.1 * g))) =
            A.ρ s (A.ρ (γ g) (x (Quotient.mk' g)))
          rw [hmk s g, hγ s g]
          simp only [map_mul, Module.End.mul_apply]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext g
        simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        funext g
        simp }
  exact LinearEquiv.ofLinearMap toFun invFun (by
    apply LinearMap.ext
    intro x
    funext q
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    dsimp [toFun, invFun]
    have hqi : Quotient.mk' (i q) = q := hi q
    rw [hqi]
    have hgamma : γ (i q) = 1 := by
      apply Subtype.ext
      have hout := congrArg Quotient.out hqi
      change i q * (Quotient.mk' (i q)).out⁻¹ = 1
      rw [hout]
      simp [i]
    rw [hgamma]
    simp) (by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext g
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    dsimp [toFun, invFun]
    have hgi : (γ g).1 * i (Quotient.mk' g) = g := by
      exact Subgroup.rightCosetCorrection_mul_out S g
    calc
      A.ρ (γ g) (f.1 (i (Quotient.mk' g))) =
          f.1 ((γ g).1 * i (Quotient.mk' g)) := (f.2 (γ g) _).symm
      _ = f.1 g := congrArg f.1 hgi)

@[expose]
public noncomputable def Representation.coindRightQuotient
    {k : Type u} {G : Type v} [Field k] [Group G]
    (S : Subgroup G) (A : Rep.{w} k S) :
    Representation k G (Quotient (QuotientGroup.rightRel S) → A) where
  toFun g := (Representation.coindVEquivRightQuotientPi S A).toLinearMap.comp
    ((Representation.coind S.subtype A.ρ g).comp
      (Representation.coindVEquivRightQuotientPi S A).symm.toLinearMap)
  map_one' := by
    apply LinearMap.ext
    intro x
    change (Representation.coindVEquivRightQuotientPi S A)
      ((Representation.coind S.subtype A.ρ 1)
        ((Representation.coindVEquivRightQuotientPi S A).symm x)) = x
    rw [map_one]
    exact (Representation.coindVEquivRightQuotientPi S A).apply_symm_apply x
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change (Representation.coindVEquivRightQuotientPi S A)
      ((Representation.coind S.subtype A.ρ (g * h))
        ((Representation.coindVEquivRightQuotientPi S A).symm x)) = _
    rw [map_mul]
    change (Representation.coindVEquivRightQuotientPi S A)
      ((Representation.coind S.subtype A.ρ g)
        ((Representation.coind S.subtype A.ρ h)
          ((Representation.coindVEquivRightQuotientPi S A).symm x))) =
      (Representation.coindVEquivRightQuotientPi S A)
        ((Representation.coind S.subtype A.ρ g)
          ((Representation.coindVEquivRightQuotientPi S A).symm
            ((Representation.coindVEquivRightQuotientPi S A)
              ((Representation.coind S.subtype A.ρ h)
                ((Representation.coindVEquivRightQuotientPi S A).symm x)))))
    rw [(Representation.coindVEquivRightQuotientPi S A).symm_apply_apply]

public lemma Representation.coindRightQuotient_apply
    {k : Type u} {G : Type v} [Field k] [Group G]
    (S : Subgroup G) (A : Rep.{w} k S)
    (g : G) (q : Quotient (QuotientGroup.rightRel S))
    (x : Quotient (QuotientGroup.rightRel S) → A) :
    letI := QuotientGroup.rightRel S
    Representation.coindRightQuotient S A g x q =
      A.ρ (Subgroup.rightCosetCorrection S (q.out * g))
        (x (Quotient.mk' (q.out * g))) := by
  classical
  let := QuotientGroup.rightRel S
  change (Representation.coindVEquivRightQuotientPi S A)
      ((Representation.coind S.subtype A.ρ g)
        ((Representation.coindVEquivRightQuotientPi S A).symm x)) q = _
  rfl

end

end Theory.AlgebraicGroup
