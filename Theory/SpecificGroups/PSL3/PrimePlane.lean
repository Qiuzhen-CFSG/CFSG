module

public import Theory.GroupTheory.PGroup.TransitivePlane
public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The transitive elementary plane in prime-field PSL₃

The actual line-local subgroup is the affine group F² ⋊ SL₂(F). Its translation
subgroup is elementary abelian of order p² when |F|=p, and SL₂(F) is transitive
on nonzero columns. The checked affine-to-parabolic equivalence embeds this
subgroup and its conjugating elements into the actual projective matrix group.

This supplies the local subgroup used for the binary degree obstruction in
Aschbacher--Smith K.2, printed p.453, and Guralnick--Malle, Classification of
2F-modules I, Proposition 4.2. It requires no representation catalogue or
Schur-multiplier calculation.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace Matrix.PSL3

private theorem affine_hasTransitiveElementaryPlane
    (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) : HasTransitiveElementaryPlane (Matrix.SL2.Affine F) p := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by simpa only [← Nat.card_eq_fintype_card] using hF)
  let U := Multiplicative (Fin 2 → F)
  let u : U →* Matrix.SL2.Affine F := SemidirectProduct.inl
  let P := u.range
  let e : U ≃* P := MonoidHom.ofInjective SemidirectProduct.inl_injective
  have hu : IsElementaryAbelian p U := by
    constructor
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro v
    apply Multiplicative.toAdd.injective
    ext i
    change p • v.toAdd i = 0
    simp [nsmul_eq_mul]
  let : IsElementaryAbelian p U := hu
  have hP : IsElementaryAbelian p P :=
    IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  refine ⟨P, hP, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fin, hF]
  · intro x y hx hy
    obtain ⟨a, ha⟩ := Matrix.SL2.exists_mulVec_eq F (e.symm x).toAdd (e.symm y).toAdd
      (fun he => hx (e.symm.injective (he.trans e.symm.map_one.symm)))
      (fun he => hy (e.symm.injective (he.trans e.symm.map_one.symm)))
    let g : Matrix.SL2.Affine F := SemidirectProduct.inr a
    have hPn : P.Normal := by
      change u.range.Normal
      rw [Matrix.SL2.range_inl_eq_translations]
      infer_instance
    have hgn : g ∈ normalizer (P : Set (Matrix.SL2.Affine F)) := by
      rw [Subgroup.normalizer_eq_top]
      exact mem_top g
    refine ⟨⟨g, hgn⟩, ?_⟩
    apply Subtype.ext
    change g * (x : Matrix.SL2.Affine F) * g⁻¹ = y
    have hx' : u (e.symm x) = (x : Matrix.SL2.Affine F) :=
      congrArg Subtype.val (e.apply_symm_apply x)
    have hy' : u (e.symm y) = (y : Matrix.SL2.Affine F) :=
      congrArg Subtype.val (e.apply_symm_apply y)
    rw [← hx', ← hy']
    change g * SemidirectProduct.inl (e.symm x) * g⁻¹ = SemidirectProduct.inl (e.symm y)
    rw [Matrix.SL2.conjugate_inl]
    apply congrArg SemidirectProduct.inl
    exact Multiplicative.toAdd.injective ha

/-- The prime-field PSL₃ parabolic contains a transitive elementary plane. -/
theorem prime_hasTransitiveElementaryPlane
    (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) :
    HasTransitiveElementaryPlane (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) p := by
  let e := Matrix.PSL3.LinearThree.lineLocalEquivAffine F
  let f := (Matrix.PSL3.LinearThree.lineLocal F).subtype.comp e.symm.toMonoidHom
  exact (affine_hasTransitiveElementaryPlane F hF).of_injective f
    (Subtype.val_injective.comp e.symm.injective)

end Matrix.PSL3
