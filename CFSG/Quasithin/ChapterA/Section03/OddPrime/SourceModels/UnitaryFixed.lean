module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FieldArithmetic
public import Theory.SpecificGroups.SU3.ProjectiveLinearEmbedding
public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import Theory.GroupAction.AutomorphismFixedSubgroup
import all Theory.SpecificGroups.SU3.ProjectiveLinearEmbedding

/-!
# The unitary circle group and its marked PSU₃ component

On the field of order 2^(6n), use the identity Hermitian form and the
3n-th power of Frobenius as conjugation. The fixed points of graph--field
on PSL₃ are precisely the image of this form's genuine projective special
unitary group. If a projectively fixed SL₃ representative has discrepancy
k, then k³ = 1 and the lifted involution sends k to k⁻¹. Multiplication by
k² gives an exactly fixed representative. The component equivalence uses
the existing PSU₃-to-PSL₃ embedding followed by the original inner map;
both compatibility equations are retained.

A norm-one coefficient makes the mixed field--diagonal generator commute
with graph--field. Its outer image generates the same quotient as the
linear circle group. Consequently linear index three implies unitary index
three. The linear cube-one assertion descends to the unitary subgroup and
rules out a complement. These are the only two linear premises retained;
the source-model assembly discharges them independently.

For odd n, a generator of Fˣ raised to q-1 has norm one and is a noncube:
3 divides q+1 but does not divide q-1. No group-order or simplicity
certification for unrelated unitary models is used.

The internal import of `ProjectiveLinearEmbedding` is used only to prove
its missing compatibility equation with PGL₃, without modifying that shared
module or its public boundary.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Notation A.3.16 and Lemma A.3.18, printed pp.51--52. The fixed-representative
argument follows the technique in `Theory.SpecificGroups.SU3.ProjectiveGraphFixed`.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3.OuterSolvable BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem unitary_frobenius_apply (r : ℕ) (x : F) :
    (frobeniusEquiv F 2 ^ r) x = x ^ (2 ^ r) := by
  rw [← iterateFrobeniusEquiv_eq_pow]
  rfl

private theorem unitary_conj_involutive {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) :
    Function.Involutive ((frobeniusEquiv F 2) ^ (3 * n)) := by
  intro x
  rw [unitary_frobenius_apply, unitary_frobenius_apply, ← pow_mul,
    ← pow_add, show 3 * n + 3 * n = 6 * n by omega, ← hc]
  let := Fintype.ofFinite F
  simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card x

/-- The identity Hermitian form with the source Frobenius involution. -/
@[expose] def unitaryCircleForm {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) : HermitianForm 3 F where
  conj := (frobeniusEquiv F 2) ^ (3 * n)
  conj_involutive := by exact unitary_conj_involutive hc
  form := 1
  form_hermitian := by
    classical
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
  form_nondegenerate := by simp

private def unitaryLift (n : ℕ) : MulAut SL(3,F) :=
  graphSL F * Atlas.fieldEquivSL 3 ((frobeniusEquiv F 2) ^ (3 * n))

private theorem unitaryLift_toGL (n : ℕ) (x : SL(3,F)) :
    Matrix.SpecialLinearGroup.toGL (unitaryLift (F := F) n x) =
      inverseTransposeGL F (GeneralLinearGroup.map
        ((frobeniusEquiv F 2) ^ (3 * n)).toRingHom (Matrix.SpecialLinearGroup.toGL x)) := by
  have hg (y : SL(3,F)) : Matrix.SpecialLinearGroup.toGL (graphSL F y) =
      inverseTransposeGL F (Matrix.SpecialLinearGroup.toGL y) := by
    apply Units.ext
    exact (Matrix.adjugate_transpose y.val).symm
  change Matrix.SpecialLinearGroup.toGL (graphSL F
    (Matrix.SpecialLinearGroup.map ((frobeniusEquiv F 2) ^ (3 * n)).toRingHom x)) = _
  rw [hg]
  congr 1
  exact Units.ext rfl

private theorem unitaryLift_mk (n : ℕ) (x : SL(3,F)) :
    circleGraphField F n (QuotientGroup.mk x) =
      QuotientGroup.mk (unitaryLift (F := F) n x) := by
  rw [circleGraphField, MulAut.mul_apply, fieldAction_mk, graph_mk]
  rfl

private theorem unitaryLift_involutive {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) :
    Function.Involutive (unitaryLift (F := F) n) := by
  intro x
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [unitaryLift_toGL, unitaryLift_toGL]
  apply Units.ext
  ext i j
  exact unitary_conj_involutive hc _

omit [Finite F] [CharP F 2] in
private theorem central_cube (x : SL(3,F)) (hx : x ∈ center SL(3,F)) : x ^ 3 = 1 := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  apply Subtype.ext
  change x.val ^ 3 = 1
  rw [← hr, ← map_pow, (by simpa using hr3 : r ^ 3 = 1), map_one]

private theorem unitary_fixed_representative {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n))
    (b : (circleGraphField F n).fixedSubgroup) :
    ∃ x : SL(3,F), unitaryLift (F := F) n x = x ∧ QuotientGroup.mk x = b.val := by
  let p := QuotientGroup.mk' (center SL(3,F))
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) b.val
  let a := unitaryLift (F := F) n
  let k := x⁻¹ * a x
  have hk : p k = 1 := by
    change p (x⁻¹ * a x) = 1
    rw [map_mul, map_inv]
    have he : p (a x) = circleGraphField F n (p x) := (unitaryLift_mk n x).symm
    rw [he]
    change (p x)⁻¹ * circleGraphField F n (p x) = 1
    rw [hx, (MulAut.mem_fixedSubgroup _ _).mp b.property, inv_mul_cancel]
  have hk3 : k ^ 3 = 1 := central_cube k ((QuotientGroup.eq_one_iff k).mp hk)
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hck : a k = k⁻¹ := by
    change a (x⁻¹ * a x) = (x⁻¹ * a x)⁻¹
    rw [map_mul, map_inv, unitaryLift_involutive hc x]
    group
  have hcx : a x = x * k := by simp [k]
  refine ⟨x * k ^ 2, ?_, ?_⟩
  · change a (x * k ^ 2) = x * k ^ 2
    rw [map_mul, map_pow, hck, hcx]
    calc
      x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
      _ = x * k ^ 2 := by rw [hki]
  · change p (x * k ^ 2) = b.val
    simpa only [map_mul, map_pow, hk, one_pow, mul_one] using hx

private theorem unitaryLift_fixed_iff {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n))
    (x : SL(3,F)) : unitaryLift (F := F) n x = x ↔
      Matrix.SpecialLinearGroup.toGL x ∈ (unitaryCircleForm hc).specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  have hd := Matrix.SpecialLinearGroup.coeToGL_det x
  simp only [hd, and_true]
  let y := GeneralLinearGroup.map ((frobeniusEquiv F 2) ^ (3 * n)).toRingHom
    (Matrix.SpecialLinearGroup.toGL x)
  have he : (unitaryCircleForm hc).conjTranspose x.val =
      (inverseTransposeGL F y).inv := rfl
  change _ ↔ (unitaryCircleForm hc).conjTranspose x.val * 1 * x.val = 1
  rw [mul_one, he]
  constructor
  · intro h
    have hg := congrArg Matrix.SpecialLinearGroup.toGL h
    rw [unitaryLift_toGL] at hg
    change inverseTransposeGL F y = Matrix.SpecialLinearGroup.toGL x at hg
    change (inverseTransposeGL F y).inv * (Matrix.SpecialLinearGroup.toGL x).val = 1
    rw [← hg]
    exact (inverseTransposeGL F y).inv_val
  · intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [unitaryLift_toGL]
    change inverseTransposeGL F y = Matrix.SpecialLinearGroup.toGL x
    have hh : (inverseTransposeGL F y)⁻¹ * Matrix.SpecialLinearGroup.toGL x = 1 := Units.ext h
    exact inv_mul_eq_one.mp hh

omit [Finite F] [CharP F 2] in
private theorem embedding_toPGL (J : HermitianForm 3 F)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (J.projectiveLinearEmbedding b) = b.val := by
  unfold HermitianForm.projectiveLinearEmbedding
  exact congrArg Subtype.val ((MonoidHom.ofInjective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 3) (R := F))).apply_symm_apply _)

omit [Finite F] [CharP F 2] in
private theorem embedding_special (J : HermitianForm 3 F) (x : SL(3,F))
    (hx : Matrix.SpecialLinearGroup.toGL x ∈ J.specialSubgroup) :
    J.projectiveLinearEmbedding (J.specialToProjective ⟨Matrix.SpecialLinearGroup.toGL x, hx⟩) =
      QuotientGroup.mk x := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [embedding_toPGL, HermitianForm.specialToProjective_apply_val]
  rfl

private theorem embedding_fixed {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n))
    (b : ProjectiveSpecialUnitaryMatrixGroup (unitaryCircleForm hc)) :
    circleGraphField F n ((unitaryCircleForm hc).projectiveLinearEmbedding b) =
      (unitaryCircleForm hc).projectiveLinearEmbedding b := by
  obtain ⟨x, rfl⟩ := (unitaryCircleForm hc).specialToProjective_surjective b
  let y : SL(3,F) := ⟨x.val.val, congrArg Units.val x.property.2⟩
  have hy : Matrix.SpecialLinearGroup.toGL y = x.val := Units.ext rfl
  have hym : Matrix.SpecialLinearGroup.toGL y ∈ (unitaryCircleForm hc).specialSubgroup :=
    hy.symm ▸ x.property
  have he : x = ⟨Matrix.SpecialLinearGroup.toGL y, hym⟩ := Subtype.ext hy.symm
  rw [he, embedding_special, unitaryLift_mk, (unitaryLift_fixed_iff hc y).mpr hym]

private def unitaryCircleFixedEmbedding {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) :
    ProjectiveSpecialUnitaryMatrixGroup (unitaryCircleForm hc) →*
      (circleGraphField F n).fixedSubgroup :=
  (unitaryCircleForm hc).projectiveLinearEmbedding.codRestrict _
    (fun b => (MulAut.mem_fixedSubgroup _ _).mpr (embedding_fixed hc b))

private theorem unitaryCircleFixedEmbedding_bijective {n : ℕ}
    (hc : Nat.card F = 2 ^ (6 * n)) :
    Function.Bijective (unitaryCircleFixedEmbedding hc) := by
  constructor
  · intro x y h
    exact (unitaryCircleForm hc).projectiveLinearEmbedding_injective (congrArg Subtype.val h)
  · intro b
    obtain ⟨x, hx, hp⟩ := unitary_fixed_representative hc b
    let y := (unitaryCircleForm hc).specialToProjective
      ⟨Matrix.SpecialLinearGroup.toGL x, (unitaryLift_fixed_iff hc x).mp hx⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact (embedding_special (unitaryCircleForm hc) x _).trans hp

omit [Finite F] [CharP F 2] in
private theorem inner_commutes_iff (α : MulAut PSL(3,F)) (x : PSL(3,F)) :
    MulAut.conj x * α = α * MulAut.conj x ↔ α x = x := by
  have he : α * MulAut.conj x = MulAut.conj (α x) * α := by
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply]
  rw [he, mul_left_inj]
  exact (Matrix.PSL3.ExtensionBorel.inner_injective F).eq_iff.trans eq_comm

private def unitaryCircleFixedToComponent (n : ℕ) (a : Fˣ) :
    (circleGraphField F n).fixedSubgroup →* unitaryCircleComponent F n a where
  toFun x := ⟨⟨MulAut.conj x.val,
    inner_le_linearCircle F n a ⟨x.val, rfl⟩,
    mem_centralizer_singleton_iff.mpr ((inner_commutes_iff _ _).mpr
      ((MulAut.mem_fixedSubgroup _ _).mp x.property))⟩, ⟨x.val, rfl⟩⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one MulAut.conj
  map_mul' x y := by apply Subtype.ext; apply Subtype.ext; exact map_mul MulAut.conj _ _

private theorem unitaryCircleFixedToComponent_bijective (n : ℕ) (a : Fˣ) :
    Function.Bijective (unitaryCircleFixedToComponent (F := F) n a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact Matrix.PSL3.ExtensionBorel.inner_injective F (congrArg (fun z => z.val.val) h)
  · intro b
    obtain ⟨x, hx⟩ := b.property
    have hf : circleGraphField F n x = x := (inner_commutes_iff _ _).mp (by
      rw [hx]
      exact mem_centralizer_singleton_iff.mp b.val.property.2)
    exact ⟨⟨x, (MulAut.mem_fixedSubgroup _ _).mpr hf⟩, Subtype.ext (Subtype.ext hx)⟩

/-- The actual projective special unitary group is the marked fixed inner component. -/
def unitaryCircleComponentEquiv {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) :
    ProjectiveSpecialUnitaryMatrixGroup (unitaryCircleForm hc) ≃*
      unitaryCircleComponent F n a :=
  (MulEquiv.ofBijective (unitaryCircleFixedEmbedding hc)
    (unitaryCircleFixedEmbedding_bijective hc)).trans
    (MulEquiv.ofBijective (unitaryCircleFixedToComponent n a)
      (unitaryCircleFixedToComponent_bijective n a))

/-- The component equivalence retains the original inner-automorphism map. -/
theorem unitaryCircleComponentEquiv_inner {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n))
    (a : Fˣ) (b : ProjectiveSpecialUnitaryMatrixGroup (unitaryCircleForm hc)) :
    (unitaryCircleComponentEquiv hc a b).val.val =
      MulAut.conj ((unitaryCircleForm hc).projectiveLinearEmbedding b) := by rfl

/-- Its PSL₃ embedding retains the original projective-linear representative. -/
theorem unitaryCircleComponentEquiv_projective {n : ℕ}
    (hc : Nat.card F = 2 ^ (6 * n))
    (b : ProjectiveSpecialUnitaryMatrixGroup (unitaryCircleForm hc)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      ((unitaryCircleForm hc).projectiveLinearEmbedding b) = b.val :=
  embedding_toPGL _ _

/-- Cardinality comparison with the actual PSU₃ carrier, independent of the extension. -/
theorem unitaryCircleComponent_card {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) :
    Nat.card (unitaryCircleComponent F n a) =
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup (unitaryCircleForm hc)) :=
  Nat.card_congr (unitaryCircleComponentEquiv hc a).symm.toEquiv

/-- The stored conjugation is precisely the q-th power map for q = 2^(3n). -/
theorem unitaryCircleForm_conj {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) (x : F) :
    (unitaryCircleForm hc).conj x = x ^ (2 ^ (3 * n)) := unitary_frobenius_apply _ _

omit [Field F] [Finite F] [CharP F 2] in
/-- The Hermitian matrix field has the required quadratic cardinality. -/
theorem unitaryCircleForm_card {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) :
    Nat.card F = (2 ^ (3 * n)) ^ 2 := by
  rw [hc, ← pow_mul]
  congr 1
  omega

/-- The source field--diagonal actor, with the original multiplication order. -/
@[expose] def unitaryMixedGenerator (n : ℕ) (a : Fˣ) : MulAut PSL(3,F) :=
  fieldAction F (circleField F n) * linearConj F (OddPrimeCoverage.diagonalGL ![a, 1, 1])

/-- Norm one makes the mixed generator centralize the literal graph--field actor. -/
theorem unitaryMixedGenerator_commutes {n : ℕ} (a : Fˣ)
    (ha : a ^ (2 ^ (3 * n) + 1) = 1) :
    Commute (circleGraphField F n) (unitaryMixedGenerator n a) := by
  let σ := (frobeniusEquiv F 2) ^ (3 * n)
  let τ := circleField F n
  let d := OddPrimeCoverage.diagonalGL ![a, 1, 1]
  have hav : σ (a : F) = (a : F)⁻¹ := by
    rw [unitary_frobenius_apply]
    apply eq_inv_of_mul_eq_one_left
    exact congrArg Units.val (by simpa only [pow_succ] using ha)
  have hd : inverseTransposeGL F (GeneralLinearGroup.map σ.toRingHom d) = d := by
    apply Units.ext
    ext i j
    change σ (d.inv j i) = d.val i j
    fin_cases i <;> fin_cases j <;>
      simp [d, OddPrimeCoverage.diagonalGL, map_inv₀, hav]
  have hff : Commute (fieldAction F σ) (fieldAction F τ) := by
    change fieldAction F σ * fieldAction F τ = fieldAction F τ * fieldAction F σ
    rw [← map_mul, ← map_mul]
    congr 1
    dsimp [σ, τ, circleField]
    rw [← pow_add, ← pow_add, Nat.add_comm]
  have hf : Commute (circleGraphField F n) (fieldAction F τ) :=
    (field_commute_graph τ).symm.mul_left hff
  have hdiag : Commute (circleGraphField F n) (linearConj F d) := by
    change (graph F * fieldAction F σ) * linearConj F d =
      linearConj F d * (graph F * fieldAction F σ)
    rw [mul_assoc, field_linearConj, ← mul_assoc, graph_linearConj, hd, mul_assoc]
  exact hf.mul_right hdiag

/-- The mixed generator lies in the source graph--field centralizer. -/
theorem unitaryMixedGenerator_mem {n : ℕ} (a : Fˣ)
    (ha : a ^ (2 ^ (3 * n) + 1) = 1) :
    unitaryMixedGenerator n a ∈ unitaryCircle F n a := by
  refine ⟨?_, mem_centralizer_singleton_iff.mpr (unitaryMixedGenerator_commutes a ha).symm.eq⟩
  change Matrix.PSL3.ExtensionBorel.qOuter F (_ * _) ∈ zpowers _
  rw [map_mul]
  exact mem_zpowers _

end
end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
noncomputable section
open Matrix.PSL3.ExtensionBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem outer_index (E : Subgroup (MulAut PSL(3,F))) :
    ((MulAut.innerSubgroup PSL(3,F)).subgroupOf E).index =
      Nat.card (E.map (qOuter F)) := by
  have hk : ((qOuter F).comp E.subtype).ker =
      (MulAut.innerSubgroup PSL(3,F)).subgroupOf E := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  rw [← hk, Subgroup.index_ker]
  have hr : ((qOuter F).comp E.subtype).range = E.map (qOuter F) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [hr]

/-- The fixed extension has index three, assuming only the permitted linear index. -/
theorem unitaryCircle_index {n : ℕ} (a : Fˣ)
    (ha : a ^ (2 ^ (3 * n) + 1) = 1)
    (hlinear : (linearCircleComponent F n a).index = 3) :
    (unitaryCircleComponent F n a).index = 3 := by
  have hl : (linearCircle F n a).map (qOuter F) =
      zpowers (qOuter F (unitaryMixedGenerator n a)) := by
    change (Subgroup.comap (qOuter F) (zpowers _)).map (qOuter F) = _
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    simp only [unitaryMixedGenerator, map_mul]
  have hu : (unitaryCircle F n a).map (qOuter F) =
      (linearCircle F n a).map (qOuter F) := by
    apply le_antisymm (Subgroup.map_mono (unitaryCircle_le_linearCircle F n a))
    rw [hl]
    apply zpowers_le.mpr
    exact Subgroup.mem_map_of_mem _ (unitaryMixedGenerator_mem a ha)
  change ((MulAut.innerSubgroup PSL(3,F)).subgroupOf _).index = _
  rw [outer_index, hu, ← outer_index]
  exact hlinear

/-- The circle group has three times the order of its actual PSU₃ component. -/
theorem unitaryCircle_card {n : ℕ} (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ)
    (ha : a ^ (2 ^ (3 * n) + 1) = 1)
    (hlinear : (linearCircleComponent F n a).index = 3) :
    Nat.card (unitaryCircle F n a) =
      3 * Nat.card (ProjectiveSpecialUnitaryMatrixGroup (unitaryCircleForm hc)) := by
  rw [← (unitaryCircleComponent F n a).index_mul_card,
    unitaryCircle_index a ha hlinear]
  congr 1
  exact Nat.card_congr (unitaryCircleComponentEquiv hc a).symm.toEquiv

/-- The linear cube-one assertion restricts to the marked unitary component. -/
theorem unitaryCircle_cube_one_mem {n : ℕ} {a : Fˣ}
    (hlinear : ∀ x : linearCircle F n a, x ^ 3 = 1 →
      x ∈ linearCircleComponent F n a)
    (x : unitaryCircle F n a) (hx : x ^ 3 = 1) :
    x ∈ unitaryCircleComponent F n a := by
  let f := Subgroup.inclusion (unitaryCircle_le_linearCircle F n a)
  exact hlinear (f x) (by rw [← map_pow, hx, map_one])

/-- The actual marked extension has no complement. The two linear premises are
discharged by the independent linear-circle proof in the parent assembly. -/
theorem unitaryCircle_nonsplit {n : ℕ} (a : Fˣ)
    (ha : a ^ (2 ^ (3 * n) + 1) = 1)
    (hindex : (linearCircleComponent F n a).index = 3)
    (hcube : ∀ x : linearCircle F n a, x ^ 3 = 1 →
      x ∈ linearCircleComponent F n a) :
    ¬ ∃ C : Subgroup (unitaryCircle F n a), (unitaryCircleComponent F n a).IsComplement' C := by
  rintro ⟨C, hC⟩
  have hc : Nat.card C = 3 := hC.card_right.trans (unitaryCircle_index a ha hindex)
  have hle : C ≤ unitaryCircleComponent F n a := by
    intro x hx
    apply unitaryCircle_cube_one_mem hcube
    have hp : (⟨x, hx⟩ : C) ^ 3 = 1 := by
      simpa only [hc] using (pow_card_eq_one' (x := (⟨x, hx⟩ : C)))
    exact congrArg Subtype.val hp
  have hb : C = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp hC.disjoint (hle hx) hx)
  rw [hb, Subgroup.card_bot] at hc
  omega
end
end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Odd n gives the unitary signed congruence in A.3.18. -/
theorem unitary_parameter_mod_three {n : ℕ} (hn : Odd n) :
    2 ^ (3 * n) % 3 = 2 := by
  obtain ⟨k, hk⟩ := (show Odd (3 * n) from Odd.mul (by decide) hn)
  rw [hk, pow_add, pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

omit [CharP F 2] in
/-- A norm-one noncube coefficient exists in the original matrix field. -/
theorem exists_unitaryCircle_coefficient {n : ℕ} (hn : Odd n)
    (hc : Nat.card F = 2 ^ (6 * n)) :
    ∃ a : Fˣ, Noncube a ∧ a ^ (2 ^ (3 * n) + 1) = 1 := by
  let q := 2 ^ (3 * n)
  have hq : q % 3 = 2 := unitary_parameter_mod_three hn
  have hq2 : 2 ≤ q := by
    have hh := Nat.mod_le q 3
    omega
  have hc' : Nat.card F = q ^ 2 := by
    rw [hc]
    dsimp [q]
    rw [← pow_mul]
    congr 1
    omega
  have hu : Nat.card Fˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_units, hc']
    have hsub : q - 1 + 1 = q := by omega
    have hsub2 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hd : 3 ∣ q + 1 := by omega
  obtain ⟨t, ht⟩ := hd
  have ht0 : 0 < t := by omega
  have hq0 : 0 < q - 1 := by omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨g ^ (q - 1), ?_, ?_⟩
  · intro b hb
    have he : g ^ ((q - 1) * ((q - 1) * t)) = 1 := by
      rw [pow_mul, ← hb, ← pow_mul]
      have he : 3 * ((q - 1) * t) = Nat.card Fˣ := by rw [hu, ht]; ring
      rw [he]
      exact pow_card_eq_one'
    have hdiv := orderOf_dvd_iff_pow_eq_one.mpr he
    rw [hg, hu, ht] at hdiv
    have hf : 3 * ((q - 1) * t) ∣ (q - 1) * ((q - 1) * t) := by
      convert hdiv using 1
      ring
    have hn3 : 3 ∣ q - 1 := (Nat.mul_dvd_mul_iff_right (Nat.mul_pos hq0 ht0)).mp hf
    omega
  · rw [← pow_mul, ← hu, ← hg, pow_orderOf_eq_one]

/-- The coefficient construction applies to the literal source generator and
its membership in the graph--field centralizer. -/
theorem exists_unitaryCircle_generator {n : ℕ} (hn : Odd n)
    (hc : Nat.card F = 2 ^ (6 * n)) :
    ∃ a : Fˣ, Noncube a ∧ a ^ (2 ^ (3 * n) + 1) = 1 ∧
      unitaryMixedGenerator n a ∈ unitaryCircle F n a := by
  obtain ⟨a, ha, hnorm⟩ := exists_unitaryCircle_coefficient hn hc
  exact ⟨a, ha, hnorm, unitaryMixedGenerator_mem a hnorm⟩

end
end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
