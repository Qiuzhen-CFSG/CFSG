module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.BlockMaps
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.Marked
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.ResidualContainment

/-!
# The marked projective orthogonal centralizer

An elementary isometry whose scalar-quotient image centralizes the marked left
SL₂ is a right determinant-space SL₂ action together with an isometry of the
actual complementary quadratic form. The right block map is injective before
projectivization. No finiteness or nondegeneracy assumption is needed for these
linear calculations.

Projective commutation lifts on each transvection: the scalar defect is central,
has square one, and is killed by the odd field characteristic. Transvection
generation then gives commutation with all of SL₂, including over F₃. Upstairs,
the left central involution separates the four-space and complement. Four
explicit SL₂ matrices span the matrix algebra, so its linear commutant acts by
right multiplication. Preservation of the determinant forces the right matrix
into SL₂; its inverse gives precisely the convention of `rightIsometry`.

This proves the full-centralizer coverage input to the orthogonal residual
calculation in Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17, printed p.39 of `refs/quasithin.pdf`; see also GLS3 §2.7. The ambient
carrier remains the Siegel-generated elementary group and the quotient is its
literal scalar quotient. Membership of the complementary isometry in Omega
is not asserted: the separate isometry-quotient argument supplies the residual
step to the source-theorem assembly owner.
-/

public noncomputable section
open Matrix
namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks
open FourPlusMatrix Theory.AlgebraicGroup
universe u
variable {F V W : Type u} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

private theorem matrix_commutant (f : Mat (F := F) →ₗ[F] Mat (F := F))
    (hf : ∀ (a : SpecialLinearGroup (Fin 2) F) M, f (a.val * M) = a.val * f M)
    (M : Mat (F := F)) : f M = M * f 1 := by
  let a : SpecialLinearGroup (Fin 2) F := SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) 1
  let b : SpecialLinearGroup (Fin 2) F := SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1
  have hs : M = (M 0 0 - M 0 1 - M 1 0) • (1 : Mat (F := F)) +
      (M 0 1 - M 0 0 + M 1 1) • a.val +
      (M 1 0 - M 0 0 + M 1 1) • b.val +
      (M 0 0 - M 1 1) • (a * b).val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, b, SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.single] <;> ring
  have ha (c : SpecialLinearGroup (Fin 2) F) : f c.val = c.val * f 1 := by
    simpa only [mul_one] using hf c 1
  calc
    f M = f ((M 0 0 - M 0 1 - M 1 0) • (1 : Mat (F := F)) +
      (M 0 1 - M 0 0 + M 1 1) • a.val +
      (M 1 0 - M 0 0 + M 1 1) • b.val +
      (M 0 0 - M 1 1) • (a * b).val) := congrArg f hs
    _ = ((M 0 0 - M 0 1 - M 1 0) • (1 : Mat (F := F)) +
      (M 0 1 - M 0 0 + M 1 1) • a.val +
      (M 1 0 - M 0 0 + M 1 1) • b.val +
      (M 0 0 - M 1 1) • (a * b).val) * f 1 := by
        simp only [map_add, map_smul, ha, add_mul, smul_mul_assoc, one_mul]
    _ = M * f 1 := congrArg (· * f 1) hs.symm

private theorem neg_fixed_zero {X : Type*} [AddCommGroup X] [Module F X]
    (h2 : (2 : F) ≠ 0) (x : X) (hx : -x = x) : x = 0 := by
  have h : (2 : F) • x = 0 := by
    rw [two_smul, ← neg_eq_iff_add_eq_zero]
    exact hx
  exact (smul_eq_zero.mp h).resolve_left h2

private theorem block_commutant (h2 : (2 : F) ≠ 0)
    (f : (Mat (F := F) × V) →ₗ[F] (Mat (F := F) × V))
    (hf : ∀ (a : SpecialLinearGroup (Fin 2) F) M v,
      f (a.val * M, v) = (a.val * (f (M, v)).1, (f (M, v)).2)) :
    ∃ B : Mat (F := F), ∃ h : V →ₗ[F] V, ∀ M v, f (M, v) = (M * B, h v) := by
  have hc M v : f (-M, v) = (-(f (M, v)).1, (f (M, v)).2) := by
    have ht := hf (-1) M v
    change f ((-(1 : Mat (F := F))) * M, v) =
      ((-(1 : Mat (F := F))) * (f (M, v)).1, (f (M, v)).2) at ht
    simpa only [neg_mul, one_mul] using ht
  have hfirst v : (f (0, v)).1 = 0 :=
    neg_fixed_zero h2 _ (by simpa using (congrArg Prod.fst (hc 0 v)).symm)
  have hsecond M : (f (M, 0)).2 = 0 := by
    apply neg_fixed_zero h2
    have ht := congrArg Prod.snd (hc M 0)
    have he : (-M, (0 : V)) = -(M, (0 : V)) := by simp
    simpa only [he, map_neg, Prod.snd_neg] using ht
  let f₁ : Mat (F := F) →ₗ[F] Mat (F := F) :=
    (LinearMap.fst F _ _).comp (f.comp (LinearMap.inl F _ _))
  let f₂ : V →ₗ[F] V := (LinearMap.snd F _ _).comp (f.comp (LinearMap.inr F _ _))
  have hm M : f₁ M = M * f₁ 1 := matrix_commutant f₁
    (fun a N => congrArg Prod.fst (hf a N 0)) M
  refine ⟨f₁ 1, f₂, fun M v => ?_⟩
  have he : (M, v) = (M, (0 : V)) + (0, v) := by simp
  rw [he, map_add]
  exact Prod.ext (by
      simpa only [Prod.fst_add, hfirst, add_zero] using
        (show (f (M, 0)).1 = M * f₁ 1 from hm M))
    (by simp only [Prod.snd_add, hsecond, zero_add]; rfl)

private theorem lift_commute (S : QuadraticForm F W) {p : ℕ} (hp : Odd p)
    (g t : elementarySubgroup S) (ht : t ^ p = 1)
    (hc : Commute (projectiveElementaryMap S g) (projectiveElementaryMap S t)) :
    Commute g t := by
  let z := g * t * g⁻¹ * t⁻¹
  have hz : z ∈ elementaryScalarSubgroup S := by
    apply (projectiveElementaryMap_eq_one_iff S z).mp
    simp only [z, map_mul, map_inv]
    rw [hc.eq]
    group
  have hcomm : Commute (g * t * g⁻¹) t := by
    have h := (show Commute z t from
      (Subgroup.mem_center_iff.mp (elementaryScalarSubgroup_le_center S hz) t).symm).mul_left
      (Commute.refl t)
    simpa only [z, inv_mul_cancel_right] using h
  have hzp : z ^ p = 1 := by
    rw [hcomm.inv_right.mul_pow, conj_pow, ht, inv_pow, ht, inv_one,
      mul_one, mul_one, mul_inv_cancel]
  have hz1 : z = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (elementaryScalar_square S z hz))
      (orderOf_dvd_of_pow_eq_one hzp)
    simpa only [hp.coprime_two_left.gcd_eq_one] using hd
  change g * t = t * g
  have h := congrArg (fun x => x * t * g) hz1
  simpa only [z, inv_mul_cancel_right, mul_assoc, inv_mul_cancel, mul_one, one_mul] using h

/-- Projective commutation with the marked left factor lifts to actual commutation.
Transvection generation includes the nonperfect case SL₂(3). -/
theorem commute_leftCover_of_projective (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((formD 2 F).prod Q).IsometryEquiv S) (g : elementarySubgroup S)
    (hg : projectiveElementaryMap S g ∈
      Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S)))
    (a : SpecialLinearGroup (Fin 2) F) : Commute g (leftCover Q S e a) := by
  apply Matrix.SL2.transvection_induction (fun a => Commute g (leftCover Q S e a)) ?_ ?_ a
  · intro i j hij c
    apply lift_commute S (Nat.Prime.odd_of_ne_two Fact.out hp)
    · have hpow (n : ℕ) : SpecialLinearGroup.transvection hij c ^ n =
          SpecialLinearGroup.transvection hij (n • c) := by
        induction n with
        | zero => simp [SpecialLinearGroup.transvection_coeff_zero]
        | succ n ih =>
          rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]
      rw [← map_pow, hpow]
      simp [nsmul_eq_mul, SpecialLinearGroup.transvection_coeff_zero]
    · exact (Subgroup.mem_centralizer_iff.mp hg _ ⟨_, rfl⟩).symm
  · intro a b ha hb
    simpa only [map_mul] using ha.mul_right hb

/-- The full right block action is faithful before taking the scalar quotient. -/
theorem rightIsometry_injective (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((formD 2 F).prod Q).IsometryEquiv S) :
    Function.Injective (rightIsometry Q S e) := by
  intro g h hgh
  have ht (v : VectorD 2 F × V) :
      ((fourRight g.1).val.val v.1, g.2.val v.2) =
        ((fourRight h.1).val.val v.1, h.2.val v.2) := by
    apply e.injective
    exact (rightIsometry_apply Q S e g v).symm.trans
      ((congrArg (fun k : quadraticIsometrySubgroup S => k.val (e v)) hgh).trans
        (rightIsometry_apply Q S e h v))
  apply Prod.ext
  · apply fourRight_injective
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact congrArg Prod.fst (ht (v, 0))
  · apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact congrArg Prod.snd (ht (0, v))

private theorem matrix_isometry_commutant (h2 : (2 : F) ≠ 0)
    (Q : QuadraticForm F V)
    (f : (Mat (F := F) × V) ≃ₗ[F] (Mat (F := F) × V))
    (hf : ∀ (a : SpecialLinearGroup (Fin 2) F) M v,
      f (a.val * M, v) = (a.val * (f (M, v)).1, (f (M, v)).2))
    (hq : ∀ z, (f z).1.det + Q (f z).2 = z.1.det + Q z.2) :
    ∃ a : SpecialLinearGroup (Fin 2) F, ∃ H : quadraticIsometrySubgroup Q,
      ∀ M v, f (M, v) = (M * a⁻¹.val, H.val v) := by
  obtain ⟨B, h, happly⟩ := block_commutant h2 f.toLinearMap hf
  change ∀ M v, f (M, v) = (M * B, h v) at happly
  have hform M v : (M * B).det + Q (h v) = M.det + Q v := by
    exact (congrArg (fun z : Mat (F := F) × V => z.1.det + Q z.2)
      (happly M v)).symm.trans (hq (M, v))
  have hB : B.det = 1 := by simpa using hform 1 0
  have hh v : Q (h v) = Q v := by simpa using hform 0 v
  have hbij : Function.Bijective h := by
    constructor
    · intro v w hvw
      have heq : f (0, v) = f (0, w) :=
        (happly 0 v).trans ((congrArg (fun x => ((0 : Mat (F := F)) * B, x)) hvw).trans
          (happly 0 w).symm)
      exact congrArg Prod.snd (f.injective heq)
    · intro v
      obtain ⟨⟨M, w⟩, hw⟩ := f.surjective (0, v)
      exact ⟨w, congrArg Prod.snd ((happly M w).symm.trans hw)⟩
  let H : quadraticIsometrySubgroup Q := ⟨LinearEquiv.ofBijective h hbij,
    (mem_quadraticIsometrySubgroup _ _).mpr hh⟩
  let b : SpecialLinearGroup (Fin 2) F := ⟨B, hB⟩
  refine ⟨b⁻¹, H, fun M v => ?_⟩
  exact (happly M v).trans
    (congrArg (fun c : SpecialLinearGroup (Fin 2) F => (M * c.val, H.val v)) (inv_inv b).symm)

/-- The upstairs isometry commutant is covered by the marked right SL₂ factor
and the isometry group of the actual complement. -/
theorem isometry_mem_rightIsometry_of_commute (h2 : (2 : F) ≠ 0)
    (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((formD 2 F).prod Q).IsometryEquiv S) (g : quadraticIsometrySubgroup S)
    (hg : ∀ a, Commute g (leftCover Q S e a).val) :
    ∃ a : SpecialLinearGroup (Fin 2) F, ∃ h : quadraticIsometrySubgroup Q,
      g = rightIsometry Q S e (a, h) := by
  let C : (Mat (F := F) × V) ≃ₗ[F] W :=
    (coordinates.symm.prodCongr (LinearEquiv.refl F V)).trans e.toLinearEquiv
  let f : (Mat (F := F) × V) ≃ₗ[F] (Mat (F := F) × V) :=
    C.trans (g.val.trans C.symm)
  have hC z : C (f z) = g.val (C z) := C.apply_symm_apply _
  have hl (a : SpecialLinearGroup (Fin 2) F) (z : Mat (F := F) × V) :
      (leftCover Q S e a).val.val (C z) = C (a.val * z.1, z.2) := by
    change (leftCover Q S e a).val.val (e (coordinates.symm z.1, z.2)) =
      e (coordinates.symm (a.val * z.1), z.2)
    rw [leftCover_apply]
    apply congrArg e
    refine Prod.ext ?_ rfl
    apply coordinates.injective
    have ht := toOrthogonal_coordinates (a, 1) (coordinates.symm z.1)
    change coordinates ((fourLeft a).val.val (coordinates.symm z.1)) =
      a.val * coordinates (coordinates.symm z.1) * (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val at ht
    rw [inv_one] at ht
    change coordinates ((fourLeft a).val.val (coordinates.symm z.1)) =
      a.val * coordinates (coordinates.symm z.1) * (1 : Mat (F := F)) at ht
    simpa only [mul_one, LinearEquiv.apply_symm_apply] using ht
  have hf (a : SpecialLinearGroup (Fin 2) F) M v :
      f (a.val * M, v) = (a.val * (f (M, v)).1, (f (M, v)).2) := by
    apply C.injective
    calc
      C (f (a.val * M, v)) = g.val (C (a.val * M, v)) := hC _
      _ = g.val ((leftCover Q S e a).val.val (C (M, v))) :=
        congrArg g.val (hl a (M, v)).symm
      _ = (leftCover Q S e a).val.val (g.val (C (M, v))) :=
        congrArg (fun k : quadraticIsometrySubgroup S => k.val (C (M, v))) (hg a)
      _ = (leftCover Q S e a).val.val (C (f (M, v))) :=
        congrArg (leftCover Q S e a).val.val (hC _).symm
      _ = C (a.val * (f (M, v)).1, (f (M, v)).2) := hl a (f (M, v))
  have hval (z : Mat (F := F) × V) : S (C z) = z.1.det + Q z.2 := by
    change S (e (coordinates.symm z.1, z.2)) = _
    rw [e.map_app, QuadraticMap.prod_apply, ← coordinates_det,
      LinearEquiv.apply_symm_apply]
  have hq z : (f z).1.det + Q (f z).2 = z.1.det + Q z.2 :=
    (hval (f z)).symm.trans ((congrArg S (hC z)).trans
      (((mem_quadraticIsometrySubgroup _ _).mp g.prop (C z)).trans (hval z)))
  obtain ⟨a, H, happly⟩ := matrix_isometry_commutant h2 Q f hf hq
  refine ⟨a, H, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  obtain ⟨⟨M, v⟩, rfl⟩ := C.surjective w
  calc
    g.val (C (M, v)) = C (f (M, v)) := (hC _).symm
    _ = C (M * a⁻¹.val, H.val v) := congrArg C (happly M v)
    _ = (rightIsometry Q S e (a, H)).val (C (M, v)) := by
      change e (coordinates.symm (M * a⁻¹.val), H.val v) =
        (rightIsometry Q S e (a, H)).val (e (coordinates.symm M, v))
      rw [rightIsometry_apply]
      apply congrArg e
      refine Prod.ext ?_ rfl
      apply coordinates.injective
      have ht : coordinates ((fourRight a).val.val (coordinates.symm M)) =
          (1 : Mat (F := F)) * coordinates (coordinates.symm M) * a⁻¹.val :=
        toOrthogonal_coordinates (1, a) (coordinates.symm M)
      simpa only [one_mul, LinearEquiv.apply_symm_apply] using ht.symm

/-- Every elementary lift of the literal projective centralizer belongs to the
full right block image. This is the coverage premise for the independent
prime-to-characteristic residual calculation. -/
theorem projective_centralizer_coverage (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((formD 2 F).prod Q).IsometryEquiv S) (g : elementarySubgroup S)
    (hg : projectiveElementaryMap S g ∈
      Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S))) :
    ∃ a : SpecialLinearGroup (Fin 2) F, ∃ h : quadraticIsometrySubgroup Q,
      g.val = rightIsometry Q S e (a, h) := by
  apply isometry_mem_rightIsometry_of_commute
    (Ring.two_ne_zero (by rwa [ringChar.eq F p])) Q S e g.val
  intro a
  exact (commute_leftCover_of_projective p hp Q S e g hg a).map
    (elementarySubgroup S).subtype

end ClassicalOrthogonal.Fundamental.SplitOddBlocks
