module

public import Theory.SpecificGroups.PSL3.LinearThreeLocalAffine
public import Theory.GroupTheory.QuasithinBasic
public import Theory.SpecificGroups.GL2.OddPrimeRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Odd ranks of the full projective degree-three parabolics

For a point-parabolic matrix `[[a,r],[0,B]]`, the homomorphism `a⁻¹B`
retains the full general linear block, including the torus. It kills scalar
matrices and therefore descends to the actual subgroup of PSL₃(F). In
characteristic two its kernel has exponent two: a kernel representative has
`B = aI`, and its square is scalar. Every odd-primary subgroup consequently
embeds into GL₂(F). The graph automorphism from `LinearThreeLocalAffine`
transfers this bound from the point parabolic to the line parabolic.

The proved odd-prime rank bound for GL₂(F) now bounds both parabolic ranks
by two. It uses the elementary-abelian characterization of prime rank,
so the bound also has the source's elementary-rank meaning. The results
hold for every finite field of characteristic two; the cardinality variants
retain an arbitrary field witness of order 2^f, in particular for f > 1.
No QT, K, E, or rank conclusion is assumed here. In particular, the smaller
affine locals are not substituted for the full projective parabolics.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed p.4, repeated as Theorem 0.1.1(1) on p.482, and the flag models in
F.1.12(I)(1), printed pp.262–264.
-/

open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.MainConverse.LinearThreeRank
open Matrix.PSL3 Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

private def pointScalar : pointParabolicSL F →* F where
  toFun g := g.val.val 0 0
  map_one' := rfl
  map_mul' g h := by
    have hh := (mem_pointParabolicSL_iff F h.val).mp h.property
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hh.1, hh.2]

private def pointBlock : pointParabolicSL F →* Matrix (Fin 2) (Fin 2) F where
  toFun g := g.val.val.submatrix Fin.succ Fin.succ
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    have hg := (mem_pointParabolicSL_iff F g.val).mp g.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
        Fin.sum_univ_two, submatrix, hg.1, hg.2]

private def pointLinearSL : pointParabolicSL F →* GL (Fin 2) F :=
  MonoidHom.toHomUnits {
    toFun g := (pointScalar F g)⁻¹ • pointBlock F g
    map_one' := by simp
    map_mul' := by
      intro g h
      simp only [map_mul, mul_inv, smul_mul_smul_comm] }

private def pointProject : pointParabolicSL F →* pointParabolic F :=
  (projection F).subgroupMap (pointParabolicSL F)

omit [Finite F] in
private theorem pointProject_surjective : Function.Surjective (pointProject F) :=
  (projection F).subgroupMap_surjective (pointParabolicSL F)

private theorem pointProject_ker_le : (pointProject F).ker ≤ (pointLinearSL F).ker := by
  intro g hg
  have hz : g.val ∈ Subgroup.center SL(3, F) := by
    rw [← projection_ker]
    exact congrArg Subtype.val hg
  obtain ⟨r, hr, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hn : r ≠ 0 := by
    intro h
    simp [h] at hr
  apply Units.ext
  change (g.val.val 0 0)⁻¹ • g.val.val.submatrix Fin.succ Fin.succ = 1
  rw [← he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar, hn]

private noncomputable def pointLinear : pointParabolic F →* GL (Fin 2) F :=
  (pointProject F).liftOfSurjective (pointProject_surjective F)
    ⟨pointLinearSL F, pointProject_ker_le F⟩

private theorem pointLinear_project (g : pointParabolicSL F) :
    pointLinear F (pointProject F g) = pointLinearSL F g :=
  MonoidHom.liftOfRightInverse_comp_apply ..

private theorem pointLinearSL_scalar_block (g : pointParabolicSL F)
    (hg : pointLinearSL F g = 1) :
    g.val.val 1 1 = g.val.val 0 0 ∧ g.val.val 1 2 = 0 ∧
    g.val.val 2 1 = 0 ∧ g.val.val 2 2 = g.val.val 0 0 := by
  have hn : g.val.val 0 0 ≠ 0 := ((pointScalar F).toHomUnits g).ne_zero
  have hm := congrArg Units.val hg
  change (g.val.val 0 0)⁻¹ • g.val.val.submatrix Fin.succ Fin.succ = 1 at hm
  have h00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 0) hm
  have h01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 0 1) hm
  have h10 := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 1 0) hm
  have h11 := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m 1 1) hm
  change (g.val.val 0 0)⁻¹ * g.val.val 1 1 = 1 at h00
  change (g.val.val 0 0)⁻¹ * g.val.val 1 2 = 0 at h01
  change (g.val.val 0 0)⁻¹ * g.val.val 2 1 = 0 at h10
  change (g.val.val 0 0)⁻¹ * g.val.val 2 2 = 1 at h11
  exact ⟨((inv_mul_eq_one₀ hn).mp h00).symm,
    (mul_eq_zero.mp h01).resolve_left (inv_ne_zero hn),
    (mul_eq_zero.mp h10).resolve_left (inv_ne_zero hn),
    ((inv_mul_eq_one₀ hn).mp h11).symm⟩

private theorem pointLinear_ker_sq [CharP F 2] (g : pointParabolic F)
    (hg : pointLinear F g = 1) : g ^ 2 = 1 := by
  obtain ⟨x, rfl⟩ := pointProject_surjective F g
  rw [pointLinear_project] at hg
  have hx := (mem_pointParabolicSL_iff F x.val).mp x.property
  obtain ⟨h11, h12, h21, h22⟩ := pointLinearSL_scalar_block F x hg
  have hc : x.val ^ 2 ∈ Subgroup.center SL(3, F) := by
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    have he : (x.val ^ 2).val = Matrix.scalar (Fin 3) (x.val.val 0 0 ^ 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.scalar, hx.1, hx.2, h11, h12, h21, h22]
      all_goals
        rw [mul_comm (x.val.val 0 0), ← two_mul,
          show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]
    refine ⟨x.val.val 0 0 ^ 2, ?_, he.symm⟩
    have hd := (x.val ^ 2).property
    rw [he] at hd
    simpa using hd
  apply Subtype.ext
  change projection F (x.val ^ 2) = 1
  rwa [← projection_ker] at hc

private theorem pointLinear_injective_on_pSubgroup [CharP F 2]
    {p : ℕ} (ho : Odd p) (A : Subgroup (pointParabolic F)) (hA : IsPGroup p A) :
    Function.Injective ((pointLinear F).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (MonoidHom.ker _).eq_bot_iff_forall.mpr
  intro a ha
  have hs : a ^ 2 = 1 := Subtype.ext (pointLinear_ker_sq F a.val ha)
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hA.orderOf_coprime ho.coprime_two_right a)
    dvd_rfl (orderOf_dvd_of_pow_eq_one hs)

private def projectiveFlagDuality : PSL(3, F) ≃* PSL(3, F) :=
  QuotientGroup.congr _ _ (flagDuality F)
    (Subgroup.characteristic_iff_map_eq.mp inferInstance (flagDuality F))

omit [Finite F] in
private theorem projectiveFlagDuality_project (g : SL(3, F)) :
    projectiveFlagDuality F (projection F g) = projection F (flagDuality F g) := rfl

private theorem flagDuality_lineParabolic_mem (g : lineParabolicSL F) :
    flagDuality F g ∈ pointParabolicSL F := by
  have hg := (mem_lineParabolicSL_iff F _).mp ((lineParabolicSL F).inv_mem g.property)
  rw [mem_pointParabolicSL_iff]
  exact ⟨hg.2, hg.1⟩

private def lineToPoint : lineParabolic F →* pointParabolic F :=
  ((projectiveFlagDuality F).toMonoidHom.comp (lineParabolic F).subtype).codRestrict
    (pointParabolic F) (by
      rintro ⟨g, x, hx, rfl⟩
      exact ⟨flagDuality F x, flagDuality_lineParabolic_mem F ⟨x, hx⟩, rfl⟩)

private theorem lineToPoint_injective : Function.Injective (lineToPoint F) := by
  intro x y h
  exact Subtype.ext ((projectiveFlagDuality F).injective (congrArg Subtype.val h))

/-- Odd-primary subgroups of the full projective point parabolic embed in GL₂. -/
public theorem pointParabolic_primeRank_le_linear [CharP F 2] {p : ℕ} (ho : Odd p) :
    primeRank p (pointParabolic F) ≤ primeRank p (GL (Fin 2) F) := by
  apply csSup_le'
  rintro n ⟨A, hp, hc, _, hn⟩
  let := hc
  let j := (pointLinear F).comp A.subtype
  have hj := pointLinear_injective_on_pSubgroup F ho A hp
  have he := Group.rank_congr (MonoidHom.ofInjective hj)
  have hcomm : IsMulCommutative j.range := inferInstance
  exact le_csSup (Theory.GroupTheory.primeRank_bdd p)
    ⟨j.range, hp.of_surjective j.rangeRestrict j.rangeRestrict_surjective,
      hcomm, inferInstance, hn.trans_eq he⟩

/-- The full projective line parabolic has the same odd-prime rank bound. -/
public theorem lineParabolic_primeRank_le_linear [CharP F 2] {p : ℕ} (ho : Odd p) :
    primeRank p (lineParabolic F) ≤ primeRank p (GL (Fin 2) F) :=
  (Theory.GroupTheory.primeRank_le_of_injective p (lineToPoint F)
    (lineToPoint_injective F)).trans (pointParabolic_primeRank_le_linear F ho)

/-- Every odd-prime rank of the full projective point parabolic is at most two. -/
public theorem pointParabolic_primeRank_le_two [CharP F 2]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (pointParabolic F) ≤ 2 :=
  (pointParabolic_primeRank_le_linear F ho).trans
    (Matrix.GeneralLinearGroup.primeRank_le_two_of_odd F ho)

/-- Every odd-prime rank of the full projective line parabolic is at most two. -/
public theorem lineParabolic_primeRank_le_two [CharP F 2]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (lineParabolic F) ≤ 2 :=
  (lineParabolic_primeRank_le_linear F ho).trans
    (Matrix.GeneralLinearGroup.primeRank_le_two_of_odd F ho)

/-- The point-parabolic bound for an arbitrary field witness of order 2^f. -/
public theorem pointParabolic_primeRank_le_two_of_card {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (pointParabolic F) ≤ 2 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact pointParabolic_primeRank_le_two F ho

/-- The line-parabolic bound for an arbitrary field witness of order 2^f. -/
public theorem lineParabolic_primeRank_le_two_of_card {f : ℕ}
    (hF : Nat.card F = 2 ^ f) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (lineParabolic F) ≤ 2 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact lineParabolic_primeRank_le_two F ho

end CFSG.Quasithin.MainConverse.LinearThreeRank
