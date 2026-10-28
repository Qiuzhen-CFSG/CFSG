module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.CharAndCard
public import BenderSuzuki.MatrixGroups.PSL2

/-!
# The graph automorphism of projective SU₃ and its fixed subgroup

For the antidiagonal Hermitian form, entrywise application of the stored field
involution preserves SU₃ and descends through its actual image in PGL₃. In
characteristic two its fixed subgroup is PSL₂ over the actual fixed subfield.
The finite-field specialization retains both the matrix-field order q² and
fixed-field order q, with q = 2ⁿ and n ≥ 2.

The scalar kernel has exponent dividing three. If a projective fixed point is
represented by x, put k = x⁻¹γ(x). Then k³ = 1 and γ(k) = k⁻¹, so xk² is a
fixed representative. A fixed SU matrix preserves the antidiagonal symmetric
form. In characteristic two its middle row and column are (0,1,0); the corner
block therefore belongs to SL₂ of the fixed field. Conversely every such
block is fixed and unitary. Its middle entry also makes projectivization
injective on the fixed subgroup. Finally SL₂ = PSL₂ in characteristic two.

Source: GLS, *The Classification of the Finite Simple Groups*, Volume 4,
Chapter 4, Lemma 3.4(c), the graph fixed-group clause for U₃(q). This does not
classify arbitrary automorphisms. The block embedding calculation is adapted
from `BenderSuzuki.MatrixGroups.UnitarySL2Centralizer`; surjectivity and the
projective fixed-representative argument are proved here.
-/

open Matrix
open scoped Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
include hJ in
private theorem form_map : J.form.map J.conj = J.form := by
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
include hJ in
private theorem map_mem (x : J.specialSubgroup) :
    GeneralLinearGroup.map J.conj.toRingHom x.val ∈ J.specialSubgroup := by
  obtain ⟨hx, hd⟩ := (J.mem_specialSubgroup_iff x.val).mp x.property
  apply (J.mem_specialSubgroup_iff _).mpr
  constructor
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M.map J.conj) hx
    have ht : (J.conjTranspose x.val.val).map J.conj =
        J.conjTranspose (x.val.val.map J.conj) := by
      ext i j
      rfl
    change J.conjTranspose (x.val.val.map J.conj) * J.form *
      x.val.val.map J.conj = J.form
    simpa only [Matrix.map_mul, ht, form_map J hJ] using h
  · apply Units.ext
    change (J.conj.mapMatrix x.val.val).det = 1
    rw [← RingEquiv.map_det]
    have hd' : x.val.val.det = 1 := congrArg Units.val hd
    rw [hd', map_one]

/-- Entrywise conjugation on the actual special unitary subgroup. -/
public def specialGraphAut : MulAut J.specialSubgroup where
  toFun x := ⟨GeneralLinearGroup.map J.conj.toRingHom x.val, map_mem J hJ x⟩
  invFun x := ⟨GeneralLinearGroup.map J.conj.toRingHom x.val, map_mem J hJ x⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] public theorem specialGraphAut_apply_val (x : J.specialSubgroup) :
    (specialGraphAut J hJ x).val.val = x.val.val.map J.conj := by rfl

private def projectiveGraphHom : ProjectiveSpecialUnitaryMatrixGroup J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  ((ProjGenLinGroup.map J.conj.toRingHom).comp
    (ProjectiveSpecialUnitaryMatrixGroup J).subtype).codRestrict _ (by
      intro b
      obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
      change ProjGenLinGroup.map J.conj.toRingHom (J.specialToProjective x).val ∈ _
      rw [J.specialToProjective_apply_val]
      exact Subgroup.mem_map_of_mem _ (map_mem J hJ x))

private theorem projectiveGraphHom_apply (x : J.specialSubgroup) :
    projectiveGraphHom J hJ (J.specialToProjective x) = J.specialToProjective (specialGraphAut J hJ x) := by
  apply Subtype.ext
  change ProjGenLinGroup.map J.conj.toRingHom (J.specialToProjective x).val = _
  rw [specialToProjective_apply_val, ProjGenLinGroup.map_mk,
    specialToProjective_apply_val]
  rfl

/-- Entrywise conjugation descended to the actual projective image of SU₃. -/
public def projectiveGraphAut : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun := projectiveGraphHom J hJ
  invFun := projectiveGraphHom J hJ
  left_inv b := by
    obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
    rw [projectiveGraphHom_apply, projectiveGraphHom_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  right_inv b := by
    obtain ⟨x, rfl⟩ := J.specialToProjective_surjective b
    rw [projectiveGraphHom_apply, projectiveGraphHom_apply]
    congr 1
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  map_mul' := map_mul (projectiveGraphHom J hJ)

@[simp] public theorem projectiveGraphAut_specialToProjective (x : J.specialSubgroup) :
    projectiveGraphAut J hJ (J.specialToProjective x) =
      J.specialToProjective (specialGraphAut J hJ x) := by
  exact projectiveGraphHom_apply J hJ x

public theorem projectiveGraphAut_isEntrywiseConjugation : J.IsEntrywiseConjugation (projectiveGraphAut J hJ) := by
  intro x
  exact ⟨specialGraphAut J hJ x, specialGraphAut_apply_val J hJ x,
    projectiveGraphAut_specialToProjective J hJ x⟩

/-- The genuine scalar kernel of SU₃ → PGL₃ has exponent dividing three. -/
public theorem cube_eq_one_of_specialToProjective_eq_one
    (x : J.specialSubgroup) (hx : J.specialToProjective x = 1) : x ^ 3 = 1 :=
  congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x, hx⟩)

public theorem specialGraphAut_involutive : Function.Involutive (specialGraphAut J hJ) := by
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact J.conj_involutive _

/-- Every projective fixed point lifts to an entrywise fixed SU representative. -/
public theorem projectiveGraphAut_fixed_representative (b : (projectiveGraphAut J hJ).fixedSubgroup) :
    ∃ x : (specialGraphAut J hJ).fixedSubgroup, J.specialToProjective x.val = b.val := by
  obtain ⟨x, hx⟩ := J.specialToProjective_surjective b.val
  let k := x⁻¹ * specialGraphAut J hJ x
  have hk : J.specialToProjective k = 1 := by
    change J.specialToProjective (x⁻¹ * specialGraphAut J hJ x) = 1
    rw [map_mul, map_inv, ← projectiveGraphHom_apply]
    change (J.specialToProjective x)⁻¹ * projectiveGraphAut J hJ (J.specialToProjective x) = 1
    rw [hx, (MulAut.mem_fixedSubgroup _ _).mp b.property, inv_mul_cancel]
  have hk3 := cube_eq_one_of_specialToProjective_eq_one J k hk
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hck : specialGraphAut J hJ k = k⁻¹ := by
    simp [k, map_mul, map_inv, specialGraphAut_involutive J hJ x]
  have hcx : specialGraphAut J hJ x = x * k := by simp [k]
  have hz : specialGraphAut J hJ (x * k ^ 2) = x * k ^ 2 := by
    rw [map_mul, map_pow, hck, hcx]
    calc
      x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
      _ = x * k ^ 2 := by rw [hki]
  exact ⟨⟨x * k ^ 2, (MulAut.mem_fixedSubgroup _ _).mpr hz⟩, by simp [map_mul, map_pow, hk, hx]⟩

private theorem fixed_entries (x : (specialGraphAut J hJ).fixedSubgroup) (i j : Fin 3) :
    J.conj (x.val.val.val i j) = x.val.val.val i j := by
  exact congrArg (fun z : J.specialSubgroup => z.val.val i j)
    ((MulAut.mem_fixedSubgroup _ _).mp x.property)

private abbrev F := FixedBy.subfield E J.conj
private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (F J)

private def block (A : SL J) : Matrix (Fin 3) (Fin 3) E :=
  !![(A 0 0 : E), 0, (A 0 1 : E); 0, 1, 0; (A 1 0 : E), 0, (A 1 1 : E)]

private theorem det_two (A : SL J) :
    (A 0 0 : E) * (A 1 1 : E) - (A 0 1 : E) * (A 1 0 : E) = 1 := by
  have h := congrArg (fun x : F J => (x : E)) A.property
  simpa only [Matrix.det_fin_two, Subfield.coe_sub, Subfield.coe_mul,
    Subfield.coe_one] using h

private theorem fixed (x : F J) : J.conj (x : E) = (x : E) := x.property

private theorem block_det (A : SL J) : (block J A).det = 1 := by
  simpa [block, Matrix.det_fin_three] using det_two J A

private def blockGL (A : SL J) : GL (Fin 3) E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (block J A) (by rw [block_det]; exact one_ne_zero)

variable [CharP E 2]

private theorem block_unitary (A : SL J)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.conjTranspose (block J A) * J.form * block J A = J.form := by
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, fixed]
  · rw [mul_comm, CharTwo.add_self_eq_zero]
  · simpa [CharTwo.sub_eq_add, mul_comm, add_comm] using det_two J A
  · simpa [CharTwo.sub_eq_add, mul_comm, add_comm] using det_two J A
  · rw [mul_comm, CharTwo.add_self_eq_zero]

private def blockSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : SL J →* J.specialSubgroup :=
  { toFun := fun A => ⟨blockGL J A, by
      apply (J.mem_specialSubgroup_iff _).mpr
      constructor
      · exact block_unitary J A hJ
      · ext
        exact block_det J A⟩
    map_one' := by
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change block J 1 i j = (1 : Matrix (Fin 3) (Fin 3) E) i j
      fin_cases i <;> fin_cases j <;> simp [block]
    map_mul' := by
      intro A B
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change block J (A * B) i j = (block J A * block J B) i j
      fin_cases i <;> fin_cases j <;>
        simp [block, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          Fin.sum_univ_three] }

private theorem fixed_shape (x : (specialGraphAut J hJ).fixedSubgroup) :
    x.val.val.val = !![x.val.val.val 0 0, 0, x.val.val.val 0 2;
      0, 1, 0; x.val.val.val 2 0, 0, x.val.val.val 2 2] := by
  let A := x.val.val.val
  have hp := (J.mem_specialSubgroup_iff x.val.val).mp x.val.property |>.1
  change J.conjTranspose A * J.form * A = J.form at hp
  have hf : ∀ i j, J.conj (A i j) = A i j := fixed_entries J hJ x
  have hh (i j : Fin 3) : A 2 i * A 0 j + A 1 i * A 1 j + A 0 i * A 2 j = J.form i j := by
    simpa [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hf]
      using congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hp
  have hh00 := hh 0 0
  have hh11 := hh 1 1
  have hh22 := hh 2 2
  rw [hJ] at hh00 hh11 hh22
  change A 2 0 * A 0 0 + A 1 0 * A 1 0 + A 0 0 * A 2 0 = 0 at hh00
  change A 2 1 * A 0 1 + A 1 1 * A 1 1 + A 0 1 * A 2 1 = 1 at hh11
  change A 2 2 * A 0 2 + A 1 2 * A 1 2 + A 0 2 * A 2 2 = 0 at hh22
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have h10 : A 1 0 = 0 := by
    apply (pow_eq_zero_iff two_ne_zero).mp
    linear_combination hh00 - (A 0 0 * A 2 0) * h2
  have h11 : A 1 1 = 1 := by
    apply CharTwo.sq_inj.mp
    linear_combination hh11 - (A 0 1 * A 2 1) * h2
  have h12 : A 1 2 = 0 := by
    apply (pow_eq_zero_iff two_ne_zero).mp
    linear_combination hh22 - (A 0 2 * A 2 2) * h2
  have hd : A 0 0 * A 2 2 - A 0 2 * A 2 0 = 1 := by
    have hd := congrArg Units.val ((J.mem_specialSubgroup_iff x.val.val).mp x.val.property).2
    change A.det = 1 at hd
    simpa [Matrix.det_fin_three, h10, h11, h12] using hd
  have he0 : A 2 0 * A 0 1 + A 0 0 * A 2 1 = 0 := by
    simpa [h10, hJ] using hh 0 1
  have he2 : A 2 2 * A 0 1 + A 0 2 * A 2 1 = 0 := by
    simpa [h12, hJ] using hh 2 1
  have h01 : A 0 1 = 0 := by
    linear_combination A 0 0 * he2 - A 0 2 * he0 - A 0 1 * hd
  have h21 : A 2 1 = 0 := by
    linear_combination A 2 2 * he0 - A 2 0 * he2 - A 2 1 * hd
  change A = !![A 0 0, 0, A 0 2; 0, 1, 0; A 2 0, 0, A 2 2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h11, h12, h01, h21]

private def blockFixed : SL J →* (specialGraphAut J hJ).fixedSubgroup :=
  (blockSU J hJ).codRestrict _ (by
    intro A
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    apply Units.ext
    ext i j
    change J.conj (block J A i j) = block J A i j
    fin_cases i <;> fin_cases j <;> simp [block, fixed])

private theorem blockFixed_injective : Function.Injective (blockFixed J hJ) := by
  intro A B h
  have hm : block J A = block J B :=
    congrArg (fun x : (specialGraphAut J hJ).fixedSubgroup => x.val.val.val) h
  apply SpecialLinearGroup.ext
  intro i j
  apply Subtype.ext
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) hm
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hm
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 0) hm
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hm

private theorem blockFixed_surjective : Function.Surjective (blockFixed J hJ) := by
  intro x
  let M : Matrix (Fin 2) (Fin 2) (F J) :=
    !![⟨x.val.val.val 0 0, fixed_entries J hJ x 0 0⟩,
       ⟨x.val.val.val 0 2, fixed_entries J hJ x 0 2⟩;
       ⟨x.val.val.val 2 0, fixed_entries J hJ x 2 0⟩,
       ⟨x.val.val.val 2 2, fixed_entries J hJ x 2 2⟩]
  have hd : M.det = 1 := by
    apply (F J).subtype.injective
    have hd := congrArg Units.val ((J.mem_specialSubgroup_iff x.val.val).mp x.val.property).2
    change x.val.val.val.det = 1 at hd
    rw [fixed_shape J hJ x] at hd
    simpa [M, Matrix.det_fin_two, Matrix.det_fin_three] using hd
  refine ⟨⟨M, hd⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change block J ⟨M, hd⟩ = x.val.val.val
  exact (fixed_shape J hJ x).symm

/-- Fixed special unitary matrices are exactly the fixed-field SL₂ blocks. -/
public noncomputable def specialGraphFixedEquivSL2 : (specialGraphAut J hJ).fixedSubgroup ≃*
    SpecialLinearGroup (Fin 2) (FixedBy.subfield E J.conj) :=
  (MulEquiv.ofBijective (blockFixed J hJ)
    ⟨blockFixed_injective J hJ, blockFixed_surjective J hJ⟩).symm

omit [CharP E 2] in
private def fixedProjectiveHom : (specialGraphAut J hJ).fixedSubgroup →* (projectiveGraphAut J hJ).fixedSubgroup :=
  (J.specialToProjective.comp (specialGraphAut J hJ).fixedSubgroup.subtype).codRestrict _ (by
    intro x
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change projectiveGraphAut J hJ (J.specialToProjective x.val) =
      J.specialToProjective x.val
    rw [projectiveGraphAut_specialToProjective,
      (MulAut.mem_fixedSubgroup _ _).mp x.property])

private theorem fixedProjectiveHom_injective : Function.Injective (fixedProjectiveHom J hJ) := by
  intro x y h
  have hp : ProjGenLinGroup.mk x.val.val = ProjGenLinGroup.mk y.val.val := by
    have he := congrArg (fun b : (projectiveGraphAut J hJ).fixedSubgroup => b.val.val) h
    change (J.specialToProjective x.val).val = (J.specialToProjective y.val).val at he
    simpa only [specialToProjective_apply_val] using he
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hx : x.val.val.val 1 1 = 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) (fixed_shape J hJ x)
  have hy : y.val.val.val 1 1 = 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) (fixed_shape J hJ y)
  have huval : (u : E) = 1 := by
    have hh := congrArg (fun g : GL (Fin 3) E => g.val 1 1) hu
    simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.scalar, hx, hy] using hh
  have huone : u = 1 := Units.ext huval
  rw [huone, map_one, mul_one] at hu
  exact Subtype.ext (Subtype.ext hu)

/-- Projectivization is an isomorphism on the fixed subgroups in characteristic two. -/
public noncomputable def projectiveGraphFixedEquivSpecial :
    (projectiveGraphAut J hJ).fixedSubgroup ≃* (specialGraphAut J hJ).fixedSubgroup :=
  (MulEquiv.ofBijective (fixedProjectiveHom J hJ) ⟨fixedProjectiveHom_injective J hJ, by
    intro b
    obtain ⟨x, hx⟩ := projectiveGraphAut_fixed_representative J hJ b
    exact ⟨x, Subtype.ext hx⟩⟩).symm

private noncomputable def slEquivPSL (K : Type*) [Field K] [CharP K 2] :
    SpecialLinearGroup (Fin 2) K ≃* PSL2MatrixGroup K := by
  let p := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))
  apply MulEquiv.ofBijective p
  refine ⟨?_, QuotientGroup.mk'_surjective _⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.mk' _).ker = ⊥
  rw [QuotientGroup.ker_mk', eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = (1 : K) ^ 2 := by simpa using hr
  have hr1 : r = 1 := CharTwo.sq_inj.mp hr2
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

/-- The graph fixed subgroup of PSU₃ is PSL₂ of the stored involution's fixed field. -/
public noncomputable def projectiveGraphFixedEquiv :
    (projectiveGraphAut J hJ).fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj) :=
  (projectiveGraphFixedEquivSpecial J hJ).trans
    ((specialGraphFixedEquivSL2 J hJ).trans (slEquivPSL (FixedBy.subfield E J.conj)))

include hJ in
omit [CharP E 2] in
/-- The finite-field graph action and fixed-group identification, with both source
field cardinalities retained. -/
public theorem exists_projectiveGraphAut_fixedEquiv [Finite E] {n : ℕ} (_hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (_hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    ∃ γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      J.IsEntrywiseConjugation γ ∧
      Nonempty (γ.fixedSubgroup ≃* PSL2MatrixGroup (FixedBy.subfield E J.conj)) := by
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  exact ⟨projectiveGraphAut J hJ, projectiveGraphAut_isEntrywiseConjugation J hJ, ⟨projectiveGraphFixedEquiv J hJ⟩⟩
end BenderSuzuki.MatrixGroups.HermitianForm
