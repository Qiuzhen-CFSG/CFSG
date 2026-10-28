module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.Coordinates
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.FixedSpaces

/-!
# The inner upper point stabilizer in dimension four

Fixing (e₃,e₂*+e₃*) cuts out the three-parameter matrices
`[[1,a,0,b],[0,1,0,c],[0,0,1,c],[0,0,0,1]]`. On the kernel of
`e₂*+e₃*`, the basis `e₁,e₂+e₃,e₄` identifies their actual action with
the full upper unitriangular group in dimension three. The same parameters
count this inner subgroup without enumerating the ambient general linear group.

Source: corrected adapted-pair calculation for Aschbacher–Smith H.9.1(4),
printed p.390; the coordinates here are zero-based in the declarations.
-/

@[expose] public section

open BinaryNaturalDual BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.AdaptedPair.Four.PointSylow

/-- The actual inner upper point stabilizer. -/
def C : Subgroup (LinearGroup 4) :=
  upperGroup 4 ⊓ pointStabilizer BinaryLinear.NaturalDualFlag.action vectorFour

private theorem fixes_iff (g : LinearGroup 4) :
    BinaryLinear.NaturalDualFlag.action g vectorFour = vectorFour ↔
      g (axis 2) = axis 2 ∧ ∀ x, (g x) 1 + (g x) 2 = x 1 + x 2 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [BinaryLinear.NaturalDualFlag.action_fst, vectorFour] using congrArg Prod.fst h
    · intro x
      have he := congrArg (fun v : CoordinateSpace 4 => v.2 (g x)) h
      simpa [BinaryLinear.NaturalDualFlag.action_snd, vectorFour] using he.symm
  · rintro ⟨hx, hf⟩
    apply Prod.ext
    · simpa only [BinaryLinear.NaturalDualFlag.action_fst, vectorFour] using hx
    · apply LinearMap.ext
      intro x
      have he := hf (g.symm x)
      simpa [BinaryLinear.NaturalDualFlag.action_snd, vectorFour] using he.symm

theorem mem_C_iff (g : LinearGroup 4) : g ∈ C ↔
    g ∈ upperGroup 4 ∧ coordinateMatrix g 0 2 = 0 ∧
      coordinateMatrix g 1 2 = 0 ∧ coordinateMatrix g 1 3 = coordinateMatrix g 2 3 := by
  change (g ∈ upperGroup 4 ∧ BinaryLinear.NaturalDualFlag.action g vectorFour = vectorFour) ↔ _
  rw [fixes_iff]
  constructor
  · rintro ⟨hg, hx, hf⟩
    refine ⟨hg, ?_, ?_, ?_⟩
    · simpa [coordinateMatrix_apply, axis] using congrFun hx 0
    · simpa [coordinateMatrix_apply, axis] using congrFun hx 1
    · have he := hf (axis 3)
      simp only [← coordinateMatrix_apply] at he
      simpa [axis, CharTwo.add_eq_zero] using he
  · rintro ⟨hg, h02, h12, h13⟩
    have hl (i j : Fin 4) (h : j < i) : coordinateMatrix g i j = 0 :=
      (mem_upperGroup_iff g).mp hg h
    have hd := upper_diagonal hg
    refine ⟨hg, ?_, ?_⟩
    · ext i
      rw [← coordinateMatrix_apply]
      fin_cases i <;> simp [hl, hd, h02, h12, axis]
    · intro x
      rw [← coordinateMatrix_mulVec]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hl, hd, h12, h13]
      rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

/-- Coordinates on the natural moving three-space. -/
def W1 : Submodule (ZMod 2) (BinaryLinear.OuterCyclic.Space 4) :=
  (coordinateForm 1 + coordinateForm 2).ker

theorem mem_W1_iff (x : BinaryLinear.OuterCyclic.Space 4) : x ∈ W1 ↔ x 1 = x 2 := by
  change x 1 + x 2 = 0 ↔ x 1 = x 2
  exact CharTwo.add_eq_zero

/-- The basis `axis 0`, `axis 1 + axis 2`, `axis 3` of the kernel. -/
def basisEquiv : BinaryLinear.OuterCyclic.Space 3 ≃ₗ[ZMod 2] W1 where
  toFun x := ⟨![x 0, x 1, x 1, x 2], by simp [mem_W1_iff]⟩
  invFun x := ![x.val 0, x.val 1, x.val 3]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    have hx := (mem_W1_iff x.val).mp x.property
    fin_cases i <;> simp [hx]
  map_add' x y := by apply Subtype.ext; ext i; fin_cases i <;> rfl
  map_smul' c x := by apply Subtype.ext; ext i; fin_cases i <;> rfl

theorem basisEquiv_axis_zero : (basisEquiv (axis 0)).val = axis 0 := by
  ext i; fin_cases i <;> simp [basisEquiv, axis]

theorem basisEquiv_axis_one : (basisEquiv (axis 1)).val = axis 1 + axis 2 := by
  ext i; fin_cases i <;> simp [basisEquiv, axis]

theorem basisEquiv_axis_two : (basisEquiv (axis 2)).val = axis 3 := by
  ext i; fin_cases i <;> simp [basisEquiv, axis]

def matrix3 (a b c : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, a, b; 0, 1, c; 0, 0, 1]

def matrix4 (a b c : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, a, 0, b; 0, 1, 0, c; 0, 0, 1, c; 0, 0, 0, 1]

private theorem matrix3_upper (a b c : ZMod 2) : (matrix3 a b c).IsUpperTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [matrix3]

private theorem matrix4_upper (a b c : ZMod 2) : (matrix4 a b c).IsUpperTriangular := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [matrix4]

noncomputable def actor3 (a b c : ZMod 2) : LinearGroup 3 :=
  slEquivLinear 3 ⟨matrix3 a b c, by
    rw [Matrix.det_of_isUpperTriangular (matrix3_upper a b c)]
    simp [Fin.prod_univ_succ, matrix3]⟩

noncomputable def actor4 (a b c : ZMod 2) : LinearGroup 4 :=
  slEquivLinear 4 ⟨matrix4 a b c, by
    rw [Matrix.det_of_isUpperTriangular (matrix4_upper a b c)]
    simp [Fin.prod_univ_succ, matrix4]⟩

@[simp] theorem coordinateMatrix_actor3 (a b c : ZMod 2) :
    coordinateMatrix (actor3 a b c) = matrix3 a b c := by
  exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) => A.val)
    ((slEquivLinear 3).symm_apply_apply _)

@[simp] theorem coordinateMatrix_actor4 (a b c : ZMod 2) :
    coordinateMatrix (actor4 a b c) = matrix4 a b c := by
  exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) => A.val)
    ((slEquivLinear 4).symm_apply_apply _)

theorem actor3_mem_upper (a b c : ZMod 2) : actor3 a b c ∈ upperGroup 3 := by
  rw [mem_upperGroup_iff, coordinateMatrix_actor3]
  exact matrix3_upper a b c

theorem actor4_mem_C (a b c : ZMod 2) : actor4 a b c ∈ C := by
  rw [mem_C_iff, mem_upperGroup_iff, coordinateMatrix_actor4]
  exact ⟨matrix4_upper a b c, rfl, rfl, rfl⟩

theorem matrix_of_mem_C {g : LinearGroup 4} (hg : g ∈ C) :
    coordinateMatrix g = matrix4 (coordinateMatrix g 0 1)
      (coordinateMatrix g 0 3) (coordinateMatrix g 1 3) := by
  obtain ⟨hu, h02, h12, h13⟩ := (mem_C_iff g).mp hg
  have hl (i j : Fin 4) (h : j < i) : coordinateMatrix g i j = 0 :=
    (mem_upperGroup_iff g).mp hu h
  have hd := upper_diagonal hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix4, hl, hd, h02, h12, h13]

theorem matrix_of_mem_upper3 {g : LinearGroup 3} (hg : g ∈ upperGroup 3) :
    coordinateMatrix g = matrix3 (coordinateMatrix g 0 1)
      (coordinateMatrix g 0 2) (coordinateMatrix g 1 2) := by
  have hl (i j : Fin 3) (h : j < i) : coordinateMatrix g i j = 0 :=
    (mem_upperGroup_iff g).mp hg h
  have hd := upper_diagonal hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix3, hl, hd]

theorem actor3_apply (a b c : ZMod 2) (x : BinaryLinear.OuterCyclic.Space 3) :
    actor3 a b c x = ![x 0 + a * x 1 + b * x 2, x 1 + c * x 2, x 2] := by
  rw [← coordinateMatrix_mulVec, coordinateMatrix_actor3]
  ext i
  fin_cases i <;> simp [matrix3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

theorem actor4_apply (a b c : ZMod 2) (x : BinaryLinear.OuterCyclic.Space 4) :
    actor4 a b c x = ![x 0 + a * x 1 + b * x 3, x 1 + c * x 3,
      x 2 + c * x 3, x 3] := by
  rw [← coordinateMatrix_mulVec, coordinateMatrix_actor4]
  ext i
  fin_cases i <;> simp [matrix4, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

private theorem actor4_recover (g : C) :
    actor4 (coordinateMatrix g.val 0 1) (coordinateMatrix g.val 0 3)
      (coordinateMatrix g.val 1 3) = g.val := by
  apply coordinateMatrix_injective
  rw [coordinateMatrix_actor4, ← matrix_of_mem_C g.property]

private theorem actor3_recover (g : upperGroup 3) :
    actor3 (coordinateMatrix g.val 0 1) (coordinateMatrix g.val 0 2)
      (coordinateMatrix g.val 1 2) = g.val := by
  apply coordinateMatrix_injective
  rw [coordinateMatrix_actor3, ← matrix_of_mem_upper3 g.property]

noncomputable def innerMap (g : C) : upperGroup 3 :=
  ⟨actor3 (coordinateMatrix g.val 0 1) (coordinateMatrix g.val 0 3)
    (coordinateMatrix g.val 1 3), actor3_mem_upper _ _ _⟩

/-- The restriction to W1 is precisely the natural three-dimensional action. -/
theorem innerMap_intertwines (g : C) (x : BinaryLinear.OuterCyclic.Space 3) :
    (basisEquiv ((innerMap g).val x)).val = g.val (basisEquiv x).val := by
  conv_rhs => rw [← actor4_recover g]
  simp only [innerMap, actor3_apply, actor4_apply]
  ext i
  fin_cases i <;> rfl

/-- The actual inner point centralizer is the full upper group on W1. -/
noncomputable def innerEquiv : C ≃* upperGroup 3 where
  toFun := innerMap
  invFun g := ⟨actor4 (coordinateMatrix g.val 0 1) (coordinateMatrix g.val 0 2)
    (coordinateMatrix g.val 1 2), actor4_mem_C _ _ _⟩
  left_inv g := by
    apply Subtype.ext
    change actor4 _ _ _ = g.val
    simp only [innerMap, coordinateMatrix_actor3]
    exact actor4_recover g
  right_inv g := by
    apply Subtype.ext
    change actor3 _ _ _ = g.val
    simp only [coordinateMatrix_actor4]
    exact actor3_recover g
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply basisEquiv.injective
    apply Subtype.ext
    change (basisEquiv ((innerMap (g * h)).val x)).val =
      (basisEquiv ((innerMap g).val ((innerMap h).val x))).val
    rw [innerMap_intertwines, innerMap_intertwines, innerMap_intertwines]
    rfl

theorem innerEquiv_intertwines (g : C) (x : BinaryLinear.OuterCyclic.Space 3) :
    (basisEquiv ((innerEquiv g).val x)).val = g.val (basisEquiv x).val :=
  innerMap_intertwines g x

private noncomputable def parametersEquiv : C ≃ (ZMod 2 × ZMod 2 × ZMod 2) where
  toFun g := (coordinateMatrix g.val 0 1, coordinateMatrix g.val 0 3,
    coordinateMatrix g.val 1 3)
  invFun p := ⟨actor4 p.1 p.2.1 p.2.2, actor4_mem_C _ _ _⟩
  left_inv g := Subtype.ext (actor4_recover g)
  right_inv p := by simp only [coordinateMatrix_actor4]; rfl

theorem card_C : Nat.card C = 8 := by
  rw [Nat.card_congr parametersEquiv]
  simp [Nat.card_eq_fintype_card]

end BinaryNaturalDual.AdaptedPair.Four.PointSylow
