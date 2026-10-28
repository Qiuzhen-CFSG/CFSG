module

public import GorensteinWalter.SL2ProjectiveCover
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.GroupTheory.PGroup.UniqueInvolutionAutomorphisms
public import Theory.LinearAlgebra.MatrixTwoCentralizer
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Inner Sylow fixers of odd-field SL₂

Every involution in SL₂ is the scalar minus identity. An abelian Sylow
two-subgroup would therefore be cyclic; Burnside transfer would make it a
nontrivial abelian image of the perfect group. Thus the Sylow is nonabelian.
A nonscalar two-by-two matrix has commutative centralizer, so every matrix
centralizing this Sylow is scalar. Its inner automorphism is trivial.

The prime-field central-cover application is in
`CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PrimeCover`.
Source: Aschbacher--Smith, the SL₂ cover exclusion in the proof of 1.1.5(3),
printed p.503. The proof uses only matrix centralizers and Burnside transfer.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

private theorem sl2_involutions_equal {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (x y : SL(2,F)) (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have hneg (z : SL(2,F)) (hz : orderOf z = 2) : z = -1 := by
    have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
    have hd : (Matrix.SpecialLinearGroup.toGL z).det = 1 := by
      apply Units.ext
      exact z.property
    rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one h2
      (Matrix.SpecialLinearGroup.toGL z) (by rw [← map_pow, hz2, map_one]) hd with he | he
    · have hz1 : z = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using he)
      simp [hz1] at hz
    · exact Subtype.ext (congrArg Units.val he)
  exact (hneg x hx).trans (hneg y hy).symm

/-- The Sylow two-subgroups of perfect odd-field SL₂ are nonabelian. -/
theorem sylow_two_not_isMulCommutative {F : Type*} [Field F] [Finite F]
    [Group.IsPerfect SL(2,F)] (ho : Odd (Nat.card F)) (P : Sylow 2 SL(2,F)) :
    ¬ IsMulCommutative P := by
  intro hcomm
  let : IsMulCommutative P := hcomm
  let : IsCyclic P := P.isPGroup'.isCyclic_of_involutions_eq (fun x y hx hy =>
    Subtype.ext (sl2_involutions_equal (GorensteinWalter.two_ne_zero_of_odd_card F ho)
      x y ((orderOf_injective (P : Subgroup SL(2,F)).subtype Subtype.val_injective x).trans hx)
      ((orderOf_injective (P : Subgroup SL(2,F)).subtype Subtype.val_injective y).trans hy)))
  have heven : 2 ∣ Nat.card SL(2,F) := by
    have hh := (GorensteinWalter.sl2ProjectiveProjection F).ker.card_subgroup_dvd_card
    simpa only [GorensteinWalter.sl2ProjectiveProjection_ker_card F ho] using hh
  have hn : normalizer (P : Set SL(2,F)) ≤ centralizer (P : Set SL(2,F)) :=
    IsCyclic.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr heven)
      (inferInstance : IsCyclic P)
  let f := MonoidHom.transferSylow P hn
  have hb : Function.Bijective (f.domRestrict (P : Subgroup SL(2,F))) :=
    (MonoidHom.transferSylow_domRestrict_eq_pow P hn).symm ▸
      (P.isPGroup'.powEquiv' P.not_dvd_index).bijective
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hb.surjective y
    exact ⟨x, hx⟩
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective hf
  have hc : Nat.card P = 1 := Nat.card_unique
  exact Nat.prime_two.not_dvd_one (hc ▸ P.dvd_card_of_dvd_card heven)

/-- An inner automorphism fixing an SL₂ Sylow two-subgroup pointwise is
trivial, over every finite odd field for which SL₂ is perfect. -/
theorem inner_sylow_fixer_eq_one {F : Type*} [Field F] [Finite F]
    [Group.IsPerfect SL(2,F)] (ho : Odd (Nat.card F)) (P : Sylow 2 SL(2,F))
    (a : MulAut SL(2,F)) (hi : a ∈ (MulAut.conj (G := SL(2,F))).range)
    (hfix : ∀ x ∈ P, a x = x) : a = 1 := by
  obtain ⟨g, rfl⟩ := hi
  have hg (x : P) : g.val * x.val.val = x.val.val * g.val := by
    have hh := hfix x x.property
    change g * x.val * g⁻¹ = x.val at hh
    have hc : g * (x : SL(2,F)) = (x : SL(2,F)) * g :=
      mul_inv_eq_iff_eq_mul.mp hh
    exact congrArg (fun z : SL(2,F) => z.val) hc
  have hscalar : ∃ r : F, g.val = r • 1 := by
    by_contra hn
    apply sylow_two_not_isMulCommutative ho P
    apply IsMulCommutative.of_comm
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.commute_of_commute_nonscalar_two _ _ _ hn (hg x) (hg y)
  obtain ⟨r, hr⟩ := hscalar
  apply MulEquiv.ext
  intro x
  change g * x * g⁻¹ = x
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change g.val * x.val = x.val * g.val
  rw [hr]
  simp

end Matrix.SpecialLinearGroup
