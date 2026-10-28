module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.Reduction
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Odd index of the rank-one Levi seed

The literal Levi fixing the quotient coordinate line and preserving its axis
is identified with SL₂ over the defining field. Order the coordinates so that
coordinate 1 is i and coordinate 2 is j; the embedding is the two-by-two
special-linear block with a final diagonal entry 1. Preservation of the axis
and pointwise fixation of the line give precisely the last row and column
needed to prove that this embedding is bijective.

The upper root of this block fixes the i-coordinate hyperplane. The exact
three-transvection exchange word sends the j-coordinate hyperplane to that
hyperplane, so this root lies in the specified intersection K ∩ w Q w⁻¹. Its index
is odd by the upper-unipotent Sylow theorem, hence the seed's index is odd.
Averaging the quadratic seed through the original quotient map then supplies
the Levi-fixed lifts. This uses only the quotient's actual marking and works
for both quotient orientations, including the field of two elements.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(1), printed pp.92–93.
-/

public section
set_option linter.unusedSimpArgs false
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
open Representation Representation.BinaryOffender
open Representation.OneCohomology.SLHigherNatural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
open QuasisimpleSource
namespace RankOneGeometry

variable {F : Type*} [Field F]
private def block (A : SL(2, F)) : SL(3, F) :=
  ⟨!![A.val 0 0, A.val 0 1, 0; A.val 1 0, A.val 1 1, 0; 0, 0, 1], by
    have h := A.property
    rw [Matrix.det_fin_two] at h
    simpa [Matrix.det_fin_three] using h⟩

private def blockHom : SL(2, F) →* SL(3, F) where
  toFun := block
  map_one' := by ext a b; fin_cases a <;> fin_cases b <;> simp [block, Matrix.one_apply]
  map_mul' A B := by
    apply Subtype.ext
    change (block (A * B)).val = (block A).val * (block B).val
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [block, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mk,
        Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

private def relabel (e : Fin 3 ≃ Fin 3) : SL(3, F) ≃* SL(3, F) where
  toFun A := ⟨A.val.submatrix e e, by simp⟩
  invFun A := ⟨A.val.submatrix e.symm e.symm, by simp⟩
  left_inv A := by ext a b; simp [Matrix.submatrix]
  right_inv A := by ext a b; simp [Matrix.submatrix]
  map_mul' A B := by
    apply Subtype.ext
    exact (Matrix.submatrix_mul_equiv _ _ e e e).symm

private theorem block_injective : Function.Injective (blockHom (F := F)) := by
  intro A B h
  apply Subtype.ext
  ext a b
  have hh := congrArg (fun C : SL(3, F) => C.val a.castSucc b.castSucc) h
  change (block A).val a.castSucc b.castSucc = (block B).val a.castSucc b.castSucc at hh
  fin_cases a <;> fin_cases b <;> simpa [block] using hh

private theorem exists_block (B : SL(3, F))
    (hr : ∀ b, B.val 2 b = (1 : Matrix (Fin 3) (Fin 3) F) 2 b)
    (hc : ∀ a, B.val a 2 = (1 : Matrix (Fin 3) (Fin 3) F) a 2) :
    ∃ A : SL(2, F), block A = B := by
  have h20 := hr 0
  have h21 := hr 1
  have h22 := hr 2
  have h02 := hc 0
  have h12 := hc 1
  simp only [Matrix.one_apply, Fin.isValue, reduceIte] at h20 h21 h22 h02 h12
  have hdet := B.property
  rw [Matrix.det_fin_three, h20, h21, h22, h02, h12] at hdet
  let A : SL(2, F) := ⟨!![B.val 0 0, B.val 0 1; B.val 1 0, B.val 1 1], by
    simpa [Matrix.det_fin_two] using hdet⟩
  refine ⟨A, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [block, A, h20, h21, h22, h02, h12]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F 3 ρ} (m : QuotientCoordinates d)

private theorem coord_action (g : G) (v : Fin 3 → F.Carrier) :
    m.action.linearEquiv
      (d.space.quotientRepresentation g (m.action.linearEquiv.symm v)) =
        (m.action.groupEquiv g).val *ᵥ v := by
  rw [m.action.intertwines, LinearEquiv.apply_symm_apply]
  rfl

private theorem mem_K_entries (j : Fin 3) (g : G) :
    g ∈ m.K j ↔
      (∀ b, (m.action.groupEquiv g).val j b = (1 : Matrix (Fin 3) (Fin 3) F.Carrier) j b) ∧
      (∀ a, (m.action.groupEquiv g).val a j = (1 : Matrix (Fin 3) (Fin 3) F.Carrier) a j) := by
  constructor
  · intro hg
    have hc : ∀ a, (m.action.groupEquiv g).val a j =
        (1 : Matrix (Fin 3) (Fin 3) F.Carrier) a j := by
      have hz : m.action.linearEquiv.symm (Pi.single j (1 : F.Carrier)) ∈ m.line j := by
        change m.action.linearEquiv (m.action.linearEquiv.symm _) ∈
          Submodule.span F.Carrier {Pi.single j 1}
        rw [LinearEquiv.apply_symm_apply]
        exact Submodule.subset_span (Set.mem_singleton _)
      have hh := congrArg m.action.linearEquiv (hg.2.2 _ hz)
      rw [coord_action, LinearEquiv.apply_symm_apply] at hh
      intro a
      simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply, Matrix.col] using congrFun hh a
    refine ⟨?_, hc⟩
    intro b
    by_cases hb : b = j
    · subst b; exact hc j
    · have hz : m.action.linearEquiv.symm (Pi.single b (1 : F.Carrier)) ∈ m.axis j := by
        change (m.action.linearEquiv (m.action.linearEquiv.symm _)) j = 0
        simp [Ne.symm hb]
      have hh := (hg.1 _).mpr hz
      change (m.action.linearEquiv (d.space.quotientRepresentation g
        (m.action.linearEquiv.symm (Pi.single b 1)))) j = 0 at hh
      rw [coord_action] at hh
      simpa [Matrix.mulVec_single, Matrix.col, Matrix.one_apply, Ne.symm hb] using hh
  · rintro ⟨hr, hc⟩
    have heval (v : Fin 3 → F.Carrier) : ((m.action.groupEquiv g).val *ᵥ v) j = v j := by
      change (∑ b, (m.action.groupEquiv g).val j b * v b) = v j
      simp [hr, Matrix.one_apply]
    constructor
    · intro z
      change (m.action.linearEquiv (d.space.quotientRepresentation g z)) j = 0 ↔
        (m.action.linearEquiv z) j = 0
      rw [m.action.intertwines]
      exact congrArg (fun a => a = 0) (heval (m.action.linearEquiv z)) |>.to_iff
    · refine ⟨Subgroup.mem_top _, ?_⟩
      intro z hz
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
      change a • Pi.single j 1 = m.action.linearEquiv z at ha
      apply m.action.linearEquiv.injective
      rw [m.action.intertwines, ← ha]
      change (m.action.groupEquiv g).val *ᵥ (a • Pi.single j 1) = a • Pi.single j 1
      rw [Matrix.mulVec_smul]
      congr 1
      ext b
      simp [Matrix.mulVec_single, Matrix.col, hc, Matrix.one_apply, Pi.single_apply]

private def coordinateOrder {i j : Fin 3} (_hij : i ≠ j) : Fin 3 ≃ Fin 3 :=
  (Equiv.swap 1 ((Equiv.swap 2 j) i)).trans (Equiv.swap 2 j)

@[local simp] private theorem coordinateOrder_one {i j : Fin 3} (hij : i ≠ j) :
    coordinateOrder hij 1 = i := by simp [coordinateOrder]

@[local simp] private theorem coordinateOrder_two {i j : Fin 3} (hij : i ≠ j) :
    coordinateOrder hij 2 = j := by
  have h : (2 : Fin 3) ≠ (Equiv.swap 2 j) i := by
    simpa using (Equiv.swap (2 : Fin 3) j).injective.ne hij.symm
  simp [coordinateOrder, Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 1) h]

variable {i j : Fin 3} (hij : i ≠ j)

private def blockActorHom : SL(2, F.Carrier) →* G :=
  m.action.groupEquiv.symm.toMonoidHom.comp
    ((relabel (coordinateOrder hij)).symm.toMonoidHom.comp blockHom)

private theorem blockActor_entries (A : SL(2, F.Carrier)) (a b : Fin 3) :
    (m.action.groupEquiv (blockActorHom m hij A)).val
      (coordinateOrder hij a) (coordinateOrder hij b) = (block A).val a b := by
  change (m.action.groupEquiv (m.action.groupEquiv.symm _)).val _ _ = _
  rw [MulEquiv.apply_symm_apply]
  change (block A).val ((coordinateOrder hij).symm ((coordinateOrder hij) a))
    ((coordinateOrder hij).symm ((coordinateOrder hij) b)) = _
  simp only [Equiv.symm_apply_apply]

private theorem blockActor_mem (A : SL(2, F.Carrier)) : blockActorHom m hij A ∈ m.K j := by
  apply (mem_K_entries m j _).mpr
  constructor
  · intro b
    obtain ⟨b, rfl⟩ := (coordinateOrder hij).surjective b
    have h : (m.action.groupEquiv (blockActorHom m hij A)).val
        (coordinateOrder hij 2) (coordinateOrder hij b) =
          (1 : Matrix (Fin 3) (Fin 3) F.Carrier) (coordinateOrder hij 2) (coordinateOrder hij b) := by
      rw [blockActor_entries]
      simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
      fin_cases b <;> simp [block]
    simpa only [Matrix.one_apply, coordinateOrder_two] using h
  · intro a
    obtain ⟨a, rfl⟩ := (coordinateOrder hij).surjective a
    have h : (m.action.groupEquiv (blockActorHom m hij A)).val
        (coordinateOrder hij a) (coordinateOrder hij 2) =
          (1 : Matrix (Fin 3) (Fin 3) F.Carrier) (coordinateOrder hij a) (coordinateOrder hij 2) := by
      rw [blockActor_entries]
      simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
      fin_cases a <;> simp [block]
    simpa only [Matrix.one_apply, coordinateOrder_two] using h

private noncomputable def leviBlockHom : SL(2, F.Carrier) →* m.K j :=
  (blockActorHom m hij).codRestrict (m.K j) (blockActor_mem m hij)

private theorem leviBlockHom_bijective : Function.Bijective (leviBlockHom m hij) := by
  constructor
  · intro A B h
    have hh := congrArg (fun x : m.K j => m.action.groupEquiv x.val) h
    change m.action.groupEquiv (m.action.groupEquiv.symm _) =
      m.action.groupEquiv (m.action.groupEquiv.symm _) at hh
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at hh
    exact block_injective ((relabel (coordinateOrder hij)).symm.injective hh)
  · intro g
    let e := coordinateOrder hij
    let B := relabel e (m.action.groupEquiv g.val)
    obtain ⟨hr, hc⟩ := (mem_K_entries m j g.val).mp g.property
    have hr' : ∀ b, B.val 2 b = (1 : Matrix (Fin 3) (Fin 3) F.Carrier) 2 b := by
      intro b
      change (m.action.groupEquiv g.val).val (e 2) (e b) = _
      calc
        _ = (1 : Matrix (Fin 3) (Fin 3) F.Carrier) (e 2) (e b) := by
          simpa only [Matrix.one_apply, e, coordinateOrder_two] using hr (e b)
        _ = _ := by simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
    have hc' : ∀ a, B.val a 2 = (1 : Matrix (Fin 3) (Fin 3) F.Carrier) a 2 := by
      intro a
      change (m.action.groupEquiv g.val).val (e a) (e 2) = _
      calc
        _ = (1 : Matrix (Fin 3) (Fin 3) F.Carrier) (e a) (e 2) := by
          simpa only [Matrix.one_apply, e, coordinateOrder_two] using hc (e a)
        _ = _ := by simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
    obtain ⟨A, hA⟩ := exists_block B hr' hc'
    refine ⟨A, Subtype.ext ?_⟩
    apply m.action.groupEquiv.injective
    change m.action.groupEquiv (m.action.groupEquiv.symm ((relabel e).symm (block A))) = _
    rw [MulEquiv.apply_symm_apply, hA]
    exact (relabel e).symm_apply_apply _

private theorem exchange_coordinate (v : Fin 3 → F.Carrier) :
    ((linearNatural F 3) (m.action.groupEquiv (exchangeActor m hij)) v) i = v j := by
  simp only [exchangeActor, MulEquiv.apply_symm_apply]
  change specialLinearNatural 3 (_ * _ * _) v i = _
  simp only [map_mul, Module.End.mul_apply, action_transvection, one_mul,
    Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
    add_zero]
  calc
    _ = (v i + v i) + (v j + v j) + v j := by abel
    _ = v j := by simp [CharTwo.add_self_eq_zero]

private theorem upper_block_fixes (t : F.Carrier) (v : Fin 3 → F.Carrier) (hv : v i = 0) :
    (m.action.groupEquiv (blockActorHom m hij (transvection zero_ne_one t))).val *ᵥ v = v := by
  let e := coordinateOrder hij
  change (m.action.groupEquiv (m.action.groupEquiv.symm _)).val *ᵥ v = v
  rw [MulEquiv.apply_symm_apply]
  change (block (transvection zero_ne_one t)).val.submatrix e.symm e.symm *ᵥ v = v
  rw [Matrix.submatrix_mulVec_equiv]
  ext a
  obtain ⟨a, rfl⟩ := e.surjective a
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm]
  fin_cases a <;>
    simp [block, transvection_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_three, e, hv]

private theorem upper_block_mem_seed (t : F.Carrier) :
    blockActorHom m hij (transvection zero_ne_one t) ∈ seedGroup m hij := by
  let x := blockActorHom m hij (transvection zero_ne_one t)
  let w := exchangeActor m hij
  refine ⟨blockActor_mem m hij _, ?_⟩
  refine ⟨w⁻¹ * x * w, ?_, ?_⟩
  · refine ⟨Subgroup.mem_top _, ?_⟩
    intro z hz
    have hz' : (m.action.linearEquiv z) j = 0 := hz
    have hw : (m.action.linearEquiv (d.space.quotientRepresentation w z)) i = 0 := by
      rw [m.action.intertwines]
      exact (exchange_coordinate m hij _).trans hz'
    have hx : d.space.quotientRepresentation x
        (d.space.quotientRepresentation w z) = d.space.quotientRepresentation w z := by
      apply m.action.linearEquiv.injective
      rw [m.action.intertwines]
      exact upper_block_fixes m hij t _ hw
    simp only [map_mul, Module.End.mul_apply, hx]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · change w * (w⁻¹ * x * w) * w⁻¹ = x
    group

end RankOneGeometry
open RankOneGeometry
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F 3 ρ} (m : QuotientCoordinates d)
  {i j : Fin 3} (hij : i ≠ j)

/-- The actual two-by-two block equivalence onto the literal quotient Levi.
The ordered block coordinates are the remaining coordinate and i, with j fixed. -/
noncomputable def rankOneLeviEquiv : SL(2, F.Carrier) ≃* m.K j :=
  MulEquiv.ofBijective (leviBlockHom m hij) (leviBlockHom_bijective m hij)

/-- The block's upper root Sylow subgroup lies in the exact seed intersection,
using the exchange actor specified in `Seeds`. -/
theorem rankOne_upper_le_seed :
    (upperUnipotent F.Carrier).map (rankOneLeviEquiv m hij).toMonoidHom ≤ seedInLevi m hij := by
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F.Carrier a).mp ha
  exact upper_block_mem_seed m hij t

/-- The literal rank-one seed has odd relative index in the literal Levi,
over every supplied binary field. -/
theorem seedInLevi_index_odd : Odd (seedInLevi m hij).index := by
  have hodd : Odd (upperUnipotent F.Carrier).index := by
    apply Nat.not_even_iff_odd.mp
    intro h
    exact (upperUnipotentSylow F.Carrier 2).not_dvd_index h.two_dvd
  have hm : Odd ((upperUnipotent F.Carrier).map
      (rankOneLeviEquiv m hij).toMonoidHom).index := by
    exact hodd.of_dvd_nat ((upperUnipotent F.Carrier).index_map_dvd
      (rankOneLeviEquiv m hij).surjective)
  exact hm.of_dvd_nat (Subgroup.index_dvd_of_le (rankOne_upper_le_seed m hij))

/-- The rank-one application of the parent reduction, with its odd-index
premise discharged and the original quotient map retained. -/
theorem fixed_lifts_rank_one (hij : i ≠ j) (hq : IsQuadratic ρ (m.Q j)) : m.FixedLifts j :=
  fixed_lifts_of_odd_index m hij hq (seedInLevi_index_odd m hij)

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
