module
public import GorensteinWalter.PGL2HomRigidity
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.SpecificGroups.GL2.Semilinear

/-!
# Canonical projective maps on determinant levels

A homomorphism from a determinant two-power level into PGL2 over an odd
finite field is the natural matrix projection whenever it has the prescribed
canonical value on the determinant-one subgroup. Consequently it commutes
with coefficient automorphisms, stated pointwise on actual matrix
representatives so clients can retain their chosen subgroup action instance.
All determinant levels and all odd fields, including three, are allowed;
the homomorphism need not be surjective.

The level-zero subgroup is normal and maps onto the canonical PSL2 range.
Agreement on this subgroup determines a PGL2 homomorphism by normal-core
rigidity. After identifying the map with the actual GL-to-PGL quotient,
coefficient equivariance is the naturality of that quotient.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp27–28.
This identifies the transported original projective map after linear model
recognition, including when the whole constituent is its central layer.
-/

namespace GorensteinWalter
open Matrix.GeneralLinearGroup
public theorem determinantTwoPower_pgl_hom_eq_projection
    (F : Type*) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (m : ℕ) (q : determinantTwoPower F m →* PGL2 F)
    (hcore : ∀ x : determinantTwoPower F 0,
      q ⟨x.val, determinantTwoPower_mono (Nat.zero_le m) x.property⟩ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL
          (sl2ProjectiveProjection F (determinantTwoPowerZeroEquivSL F x))) :
    q = Matrix.ProjGenLinGroup.mk.comp (determinantTwoPower F m).subtype := by
  let D := determinantTwoPower F m
  let N := (determinantTwoPower F 0).subgroupOf D
  let q₀ : D →* PGL2 F := Matrix.ProjGenLinGroup.mk.comp D.subtype
  let e := (Subgroup.subgroupOfEquivOfLe (determinantTwoPower_mono (Nat.zero_le m))).trans
    (determinantTwoPowerZeroEquivSL F)
  have hNcore (x : N) : q x = Matrix.ProjectiveSpecialLinearGroup.toPGL
      (sl2ProjectiveProjection F (e x)) := hcore ⟨x.val.val,x.property⟩
  apply pgl2_hom_eq_of_agree_on_normal_psl2 hF q q₀ N
  · intro x
    rw [hNcore]
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk _ : PSL2 F) = _
    rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      (determinantTwoPowerZeroEquivSL F ⟨x.val.val,x.property⟩)) = _
    rw [determinantTwoPowerZeroEquivSL_toGL]
    rfl
  · ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨sl2ProjectiveProjection F (e ⟨x,hx⟩), (hNcore ⟨x,hx⟩).symm⟩
    · rintro ⟨s,rfl⟩
      obtain ⟨x,hx⟩ := (sl2ProjectiveProjection_surjective F).comp e.surjective s
      exact ⟨x,x.property,(hNcore x).trans (congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hx)⟩

public theorem determinantTwoPower_pgl_hom_coefficient
    (F : Type*) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (m : ℕ) (q : determinantTwoPower F m →* PGL2 F)
    (hcore : ∀ x : determinantTwoPower F 0,
      q ⟨x.val, determinantTwoPower_mono (Nat.zero_le m) x.property⟩ =
        Matrix.ProjectiveSpecialLinearGroup.toPGL
          (sl2ProjectiveProjection F (determinantTwoPowerZeroEquivSL F x)))
    (σ : F ≃+* F) (x y : determinantTwoPower F m)
    (hxy : y.val = coefficientEquiv σ x.val) :
    q y = pgl2FieldAut F σ (q x) := by
  rw [determinantTwoPower_pgl_hom_eq_projection F hF m q hcore]
  change QuotientGroup.mk' _ y.val = pgl2RingEquiv σ (QuotientGroup.mk' _ x.val)
  rw [pgl2RingEquiv_mk, hxy]
  rfl
end GorensteinWalter
