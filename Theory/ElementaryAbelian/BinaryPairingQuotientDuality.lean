module

public import Theory.ElementaryAbelian.BinaryPairingCardinality

/-!
# Duality after removing the radicals of a binary pairing

For a finite elementary abelian two-group A and any group B, a binary pairing
identifies B modulo its right radical with the binary dual of A modulo its
left radical. No commutativity or finiteness of B is needed. We restrict the
right map to its image, which is elementary abelian, and apply finite binary
duality there. The first isomorphism theorem then supplies the actual quotient
isomorphism and its evaluation formula.

This is the linear-algebra step of Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma F.9.7, p.321.
-/

open scoped IsMulCommutative
/-- A quotient of an elementary abelian group is elementary abelian. -/
public instance IsElementaryAbelian.quotient {p : ℕ} {A : Type*} [Group A]
    [IsElementaryAbelian p A] (N : Subgroup A) [N.Normal] :
    IsElementaryAbelian p (A ⧸ N) where
  exponent_dvd_p := MonoidHom.exponent_dvd (f := QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective _) |>.trans
      (IsElementaryAbelian.exponent_dvd_p p A)

namespace MonoidHom
/-- Binary group characters are exactly linear functionals over `ZMod 2`. -/
@[expose] public def binaryCharacterEquivLinearDual {A : Type*} [Group A] [IsElementaryAbelian 2 A] :
    (A →* Multiplicative (ZMod 2)) ≃*
      Multiplicative (Module.Dual (ZMod 2) (Additive A)) where
  toFun f := Multiplicative.ofAdd ((MonoidHom.toAdditiveLeft f).toZModLinearMap 2)
  invFun f := MonoidHom.toAdditiveLeft.symm f.toAdd.toAddMonoidHom
  left_inv _ := rfl
  right_inv f := by apply Multiplicative.toAdd.injective; ext a; rfl
  map_mul' f g := by apply Multiplicative.toAdd.injective; ext a; rfl

/-- Left nondegeneracy gives right surjectivity, without an abelianity assumption
on the right-hand group. -/
public theorem binary_pairing_flip_surjective_general
    {A B : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group B] (f : A →* (B →* Multiplicative (ZMod 2)))
    (hinj : Function.Injective f) : Function.Surjective f.flip := by
  let R := f.flip.range
  let : Finite R := Finite.of_injective
    (fun r : R => fun a : A => r.val a) (by
      intro r s h
      apply Subtype.ext
      exact MonoidHom.ext (congrFun h))
  let : IsElementaryAbelian 2 R := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro r
      apply Subtype.ext
      ext a
      change (r.val a)^2 = 1
      apply Multiplicative.toAdd.injective
      change 2 • (r.val a).toAdd = 0
      simp only [nsmul_eq_mul, Nat.cast_ofNat, show (2 : ZMod 2) = 0 by decide, zero_mul] }
  let pairing : A →* (R →* Multiplicative (ZMod 2)) := {
    toFun a := {
      toFun r := r.val a
      map_one' := rfl
      map_mul' _ _ := rfl }
    map_one' := by ext r; exact r.val.map_one
    map_mul' a b := by ext r; exact r.val.map_mul a b }
  have hpairing : Function.Injective pairing := by
    intro a b hab
    apply hinj
    ext c
    exact congrArg (fun k : R →* Multiplicative (ZMod 2) =>
      k (f.flip.rangeRestrict c)) hab
  intro l
  obtain ⟨r, hr⟩ := binary_pairing_flip_surjective pairing hpairing l
  obtain ⟨b, hb⟩ := f.flip.rangeRestrict_surjective r
  refine ⟨b, ?_⟩
  calc
    f.flip b = r.val := congrArg Subtype.val hb
    _ = l := hr

/-- A binary pairing identifies the right radical quotient with the full dual
of the left radical quotient. The equivalence retains the original pairing. -/
public theorem exists_binary_pairing_quotient_duality
    {A B : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [Group B] (f : A →* (B →* Multiplicative (ZMod 2))) :
    ∃ e : (B ⧸ f.flip.ker) ≃* ((A ⧸ f.ker) →* Multiplicative (ZMod 2)),
      ∀ (a : A) (b : B), e (QuotientGroup.mk' f.flip.ker b)
        (QuotientGroup.mk' f.ker a) = f a b := by
  let Abar := A ⧸ f.ker
  let first := QuotientGroup.kerLift f
  have hsurj : Function.Surjective first.flip :=
    binary_pairing_flip_surjective_general first (QuotientGroup.kerLift_injective f)
  have hker : first.flip.ker = f.flip.ker := by
    ext b
    change first.flip b = 1 ↔ f.flip b = 1
    constructor
    · intro hb
      ext a
      exact congrArg (fun k : Abar →* Multiplicative (ZMod 2) =>
        k (QuotientGroup.mk' f.ker a)) hb
    · intro hb
      apply MonoidHom.ext
      intro a
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective f.ker a
      exact congrArg (fun k : A →* Multiplicative (ZMod 2) => k a) hb
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective first.flip hsurj)
  exact ⟨e, fun _ _ => rfl⟩
end MonoidHom
