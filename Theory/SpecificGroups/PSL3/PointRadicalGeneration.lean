module

public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.SL2.Affine.Core
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Concrete point radicals and their natural coordinates

The radical at a subspace fixes it pointwise and has all displacements in it.
For a line in F³ this is the conjugate of the existing coordinate root plane,
so it is explicitly isomorphic to additive F². The definition retains the full
setwise point stabilizer, and its normality is proved directly from the action.
Right conjugation by a matrix carries the radical to the line transformed by
its inverse, matching the convention used in the quasithin source.

These facts prepare the full parabolic-core and three-point generation
arguments; neither assertion is assumed here. The calculations apply over
arbitrary fields, with characteristic two used only for elementarity.

Source: Aschbacher–Smith, G.2.5(1–2), printed pp.335–336, with the point
parabolic argument of G.2.3 on pp.333–334.
-/

@[expose] public section
open Matrix Subgroup
open scoped MatrixGroups Pointwise
namespace Matrix.PSL3.PointRadicalGeneration
variable {F : Type*} [Field F]
/-- Matrices fixing P pointwise and acting trivially modulo P. -/
def radical (P : Submodule F (Fin 3 → F)) : Subgroup SL(3,F) where
  carrier := {a | (∀ v ∈ P, a.val *ᵥ v = v) ∧ ∀ v, a.val *ᵥ v - v ∈ P}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hb v hv, ha v hv]
    · intro v
      have hd := P.add_mem (hda (b.val *ᵥ v)) (hdb v)
      simpa only [SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec, sub_add_sub_cancel] using hd
  inv_mem' := by
    rintro a ⟨ha, hda⟩
    have hi (v : Fin 3 → F) : a.val *ᵥ (a⁻¹.val *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
        SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    refine ⟨?_, ?_⟩
    · intro v hv
      apply (SpecialLinearGroup.toLin' a).injective
      exact (hi v).trans (ha v hv).symm
    · intro v
      simpa only [hi, neg_sub] using P.neg_mem (hda (a⁻¹.val *ᵥ v))

abbrev parabolic (P : Submodule F (Fin 3 → F)) : Subgroup SL(3,F) :=
  MulAction.stabilizer SL(3,F) (P : Set (Fin 3 → F))

theorem radical_le_parabolic [Finite F] (P : Submodule F (Fin 3 → F)) :
    radical P ≤ parabolic P := by
  intro a ha
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
  intro v hv
  change a.val *ᵥ v ∈ P
  rw [ha.1 v hv]
  exact hv

def conjugatePoint (P : Submodule F (Fin 3 → F)) (a : SL(3,F)) :
    Submodule F (Fin 3 → F) := P.map (Matrix.mulVecLin a⁻¹.val)

theorem mem_conjugatePoint (P : Submodule F (Fin 3 → F)) (a : SL(3,F))
    (v : Fin 3 → F) : v ∈ conjugatePoint P a ↔ a.val *ᵥ v ∈ P := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    change a.val *ᵥ (a⁻¹.val *ᵥ w) ∈ P
    rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
      mul_inv_cancel, SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    exact hw
  · intro hv
    refine ⟨a.val *ᵥ v, hv, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
      inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.one_mulVec]

private theorem conj_radical_le (P : Submodule F (Fin 3 → F)) (a : SL(3,F)) :
    (radical P).map (MulAut.conj a⁻¹).toMonoidHom ≤ radical (conjugatePoint P a) := by
  rintro _ ⟨u,hu,rfl⟩
  change a⁻¹ * u * a⁻¹⁻¹ ∈ radical (conjugatePoint P a)
  rw [inv_inv]
  change (∀ v ∈ conjugatePoint P a, (a⁻¹ * u * a).val *ᵥ v = v) ∧ _
  have hi (v : Fin 3 → F) : a⁻¹.val *ᵥ (a.val *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv' := (mem_conjugatePoint P a v).mp hv
    simp only [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hu.1 _ hv', hi]
  · intro v
    refine ⟨u.val *ᵥ (a.val *ᵥ v) - a.val *ᵥ v, hu.2 _, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_sub, hi,
      SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

theorem parabolic_normalizes_radical [Finite F] (P : Submodule F (Fin 3 → F)) :
    parabolic P ≤ normalizer (radical P : Set SL(3,F)) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha u hu
  have hp : conjugatePoint P a⁻¹ = P := by
    ext v
    rw [mem_conjugatePoint]
    constructor
    · intro hv
      have hm := (MulAction.mem_stabilizer_set' (Set.toFinite _)).mp ha hv
      change a.val *ᵥ (a⁻¹.val *ᵥ v) ∈ P at hm
      simpa only [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
        mul_inv_cancel, SpecialLinearGroup.coe_one, Matrix.one_mulVec] using hm
    · intro hv
      exact (MulAction.mem_stabilizer_set' (Set.toFinite _)).mp ((parabolic P).inv_mem ha) hv
  have hm := conj_radical_le P a⁻¹ (mem_map_of_mem (MulAut.conj a⁻¹⁻¹).toMonoidHom hu)
  simpa only [hp, inv_inv, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] using hm


theorem conjugatePoint_inv (P : Submodule F (Fin 3 → F)) (a : SL(3,F)) :
    conjugatePoint (conjugatePoint P a) a⁻¹ = P := by
  ext v
  simp only [mem_conjugatePoint, Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
    mul_inv_cancel, SpecialLinearGroup.coe_one, Matrix.one_mulVec]

/-- Right conjugation uses the inverse matrix on the point. -/
theorem radical_conjugate (P : Submodule F (Fin 3 → F)) (a : SL(3,F)) :
    (radical P).map (MulAut.conj a⁻¹).toMonoidHom = radical (conjugatePoint P a) := by
  apply le_antisymm (conj_radical_le P a)
  intro u hu
  have hv := conj_radical_le (conjugatePoint P a) a⁻¹
    (mem_map_of_mem (MulAut.conj a⁻¹⁻¹).toMonoidHom hu)
  rw [conjugatePoint_inv] at hv
  refine ⟨_, hv, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

/-- The first coordinate point. -/
def standardPoint : Submodule F (Fin 3 → F) := Submodule.span F {![1,0,0]}

theorem mem_standardPoint (v : Fin 3 → F) :
    v ∈ standardPoint (F := F) ↔ v 1 = 0 ∧ v 2 = 0 := by
  rw [standardPoint, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,rfl⟩
    simp
  · rintro ⟨h1,h2⟩
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [h1,h2]

/-- The geometric definition is precisely the existing two-parameter root plane. -/
theorem radical_standardPoint :
    radical (standardPoint (F := F)) = RootPlaneGeometry.rootPlaneSL F true := by
  ext u
  rw [RootPlaneGeometry.mem_rootPlaneSL_point]
  constructor
  · intro hu
    have h0 := hu.1 (![1,0,0] : Fin 3 → F) ((mem_standardPoint _).mpr (by simp))
    have h1 := (mem_standardPoint _).mp (hu.2 (![0,1,0] : Fin 3 → F))
    have h2 := (mem_standardPoint _).mp (hu.2 (![0,0,1] : Fin 3 → F))
    have h00 := congrFun h0 0
    have h10 := congrFun h0 1
    have h20 := congrFun h0 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, sub_eq_zero] at h00 h10 h20 h1 h2
    refine ⟨u.val 0 1,u.val 0 2, ?_⟩
    apply Subtype.ext
    change Matrix.PSL3Even.UnipotentGeometry.matrix F _ = u.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.PSL3Even.UnipotentGeometry.matrix, h00,h10,h20,h1,h2]
  · rintro ⟨a,c,rfl⟩
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨h1,h2⟩ := (mem_standardPoint _).mp hv
      change Matrix.PSL3Even.UnipotentGeometry.matrix F _ *ᵥ v = v
      ext i
      fin_cases i <;> simp [Matrix.PSL3Even.UnipotentGeometry.matrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three,h1,h2]
    · intro v
      apply (mem_standardPoint _).mpr
      change ((Matrix.PSL3Even.UnipotentGeometry.matrix F _ *ᵥ v - v) 1 = 0) ∧
        ((Matrix.PSL3Even.UnipotentGeometry.matrix F _ *ᵥ v - v) 2 = 0)
      simp [Matrix.PSL3Even.UnipotentGeometry.matrix,
        dotProduct, Fin.sum_univ_three]



/-- Every line is an actual special-linear translate of the coordinate point. -/
theorem exists_standardPoint_conjugator (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) :
    ∃ a : SL(3,F), conjugatePoint (standardPoint (F := F)) a = P := by
  have hP0 : P ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hP
    exact Nat.zero_ne_one hP
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have he0 : (![1,0,0] : Fin 3 → F) ≠ 0 := by
    intro he
    have := congrFun he 0
    simp at this
  obtain ⟨a,ha⟩ := SpecialLinearGroup.exists_mulVec_eq_three v ![1,0,0] hv0 he0
  refine ⟨a, ?_⟩
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0
  ext w
  rw [mem_conjugatePoint, standardPoint, Submodule.mem_span_singleton,
    hspan, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c, (SpecialLinearGroup.toLin' a).injective ?_⟩
    change a.val *ᵥ (c • v) = a.val *ᵥ w
    rw [Matrix.mulVec_smul, ha, hc]
  · rintro ⟨c,rfl⟩
    exact ⟨c, by rw [Matrix.mulVec_smul,ha]⟩

/-- The literal root-plane carrier has its two additive field coordinates. -/
noncomputable def standardRadicalEquiv :
    radical (standardPoint (F := F)) ≃* Multiplicative (Fin 2 → F) :=
  (MulEquiv.subgroupCongr radical_standardPoint).trans
    ((Subgroup.equivMapOfInjective (Matrix.PSL3Even.UnipotentGeometry.V₁ F)
      (Matrix.PSL3Even.UnipotentGeometry.specialLinear F)
      (Matrix.PSL3Even.UnipotentGeometry.specialLinear_injective F)).symm.trans
      ((Matrix.PSL3Even.UnipotentGeometry.plane₁Equiv F).symm.trans
        (AddEquiv.toMultiplicative (LinearEquiv.finTwoArrow F F).symm.toAddEquiv)))

/-- Additive F² coordinates for the radical of any one-dimensional subspace. -/
noncomputable def radicalEquiv (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) : radical P ≃* Multiplicative (Fin 2 → F) := by
  classical
  let a := Classical.choose (exists_standardPoint_conjugator P hP)
  have ha := Classical.choose_spec (exists_standardPoint_conjugator P hP)
  exact ((MulEquiv.subgroupCongr ((radical_conjugate standardPoint a).trans
    (congrArg radical ha)).symm).trans
      (Subgroup.equivMapOfInjective (radical standardPoint)
        (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective).symm).trans
          standardRadicalEquiv

theorem card_radical (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) : Nat.card (radical P) = Nat.card F ^ 2 := by
  rw [Nat.card_congr (radicalEquiv P hP).toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → F) ≃ (Fin 2 → F)),
    Nat.card_fun, Nat.card_fin]



theorem conjugatePoint_finrank (P : Submodule F (Fin 3 → F)) (a : SL(3,F)) :
    Module.finrank F (conjugatePoint P a) = Module.finrank F P :=
  (SpecialLinearGroup.toLin' a⁻¹).finrank_map_eq P

theorem radical_normal [Finite F] (P : Submodule F (Fin 3 → F)) :
    ((radical P).subgroupOf (parabolic P)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (radical_le_parabolic P)).mpr
    (parabolic_normalizes_radical P)

theorem radical_elementary [CharP F 2] (P : Submodule F (Fin 3 → F))
    (hP : Module.finrank F P = 1) : IsElementaryAbelian 2 (radical P) :=
  IsElementaryAbelian.of_surjective (radicalEquiv P hP).symm.toMonoidHom
    (radicalEquiv P hP).symm.surjective

theorem parabolic_standardPoint [Finite F] :
    parabolic (standardPoint (F := F)) = LinearThree.pointParabolicSL F := by
  have he : (standardPoint (F := F) : Set (Fin 3 → F)) =
      {v : Fin 3 → F | v 1 = 0 ∧ v 2 = 0} := by
    ext v
    exact mem_standardPoint v
  change MulAction.stabilizer SL(3,F) _ = MulAction.stabilizer SL(3,F) _
  rw [he]

end Matrix.PSL3.PointRadicalGeneration
