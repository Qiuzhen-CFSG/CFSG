module
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.FinCases

/-!
# Flag stabilizers and local factors in degree three

In SL₃(F), the standard incident flag is the first coordinate line in the
plane v₂ = 0. We construct both set stabilizers and their whole intersection.
Scalar matrices lie in that intersection, so their projective images have
exactly the specified matrix preimages.

The two smaller local factors fix respectively e₀ and the covector v ↦ v₂.
Their diagonal two-by-two blocks have determinant one. The projective projection is injective on each local factor.
Diagonal matrices give literal factorizations Pᵢ = LᵢB. The common local
intersection is the upper unitriangular subgroup; its Sylow property, the
semidirect-product descriptions, and the block assertions are not proved here.

The coordinate stabilizer proofs generalize the binary calculation in
`PSL3Two.Parabolics.Subgroups.Coordinates`.
Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
-/

@[expose] public section
namespace Matrix.PSL3.LinearThree
open scoped MatrixGroups Pointwise
variable (F : Type*) [Field F] [Finite F]

/-- Stabilizer of the standard one-dimensional subspace. -/
def pointParabolicSL : Subgroup SL(3, F) :=
  MulAction.stabilizer SL(3, F) {v : Fin 3 → F | v 1 = 0 ∧ v 2 = 0}
/-- Stabilizer of the standard two-dimensional subspace. -/
def lineParabolicSL : Subgroup SL(3, F) :=
  MulAction.stabilizer SL(3, F) {v : Fin 3 → F | v 2 = 0}
/-- The whole flag overlap, including its diagonal elements. -/
def borelSL : Subgroup SL(3, F) := pointParabolicSL F ⊓ lineParabolicSL F

theorem mem_pointParabolicSL_iff (g : SL(3, F)) :
    g ∈ pointParabolicSL F ↔ g.val 1 0 = 0 ∧ g.val 2 0 = 0 := by
  rw [pointParabolicSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → F⦄, v 1 = 0 ∧ v 2 = 0 →
    (g.val.mulVec v) 1 = 0 ∧ (g.val.mulVec v) 2 = 0) ↔ _
  constructor
  · intro h
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using
      h (v := ![1, 0, 0]) (by simp)
  · rintro ⟨h1, h2⟩ v ⟨v1, v2⟩
    simp [mulVec, dotProduct, Fin.sum_univ_three, h1, h2, v1, v2]

theorem mem_lineParabolicSL_iff (g : SL(3, F)) :
    g ∈ lineParabolicSL F ↔ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  rw [lineParabolicSL, MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 3 → F⦄, v 2 = 0 → (g.val.mulVec v) 2 = 0) ↔ _
  constructor
  · intro h
    constructor
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using
        h (v := ![1, 0, 0]) (by simp)
    · simpa [mulVec, dotProduct, Fin.sum_univ_three] using
        h (v := ![0, 1, 0]) (by simp)
  · rintro ⟨h1, h2⟩ v v2
    simp [mulVec, dotProduct, Fin.sum_univ_three, h1, h2, v2]

theorem mem_borelSL_iff (g : SL(3, F)) : g ∈ borelSL F ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  simp only [borelSL, Subgroup.mem_inf, mem_pointParabolicSL_iff, mem_lineParabolicSL_iff]
  tauto

theorem projection_ker_le_borelSL : (projection F).ker ≤ borelSL F := by
  intro g hg
  rw [projection_ker] at hg
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  rw [mem_borelSL_iff, ← hr]
  simp [Matrix.scalar]

def pointParabolic : Subgroup PSL(3, F) := (pointParabolicSL F).map (projection F)
def lineParabolic : Subgroup PSL(3, F) := (lineParabolicSL F).map (projection F)
def borel : Subgroup PSL(3, F) := (borelSL F).map (projection F)

theorem pointParabolic_comap : (pointParabolic F).comap (projection F) =
    pointParabolicSL F :=
  Subgroup.comap_map_eq_self ((projection_ker_le_borelSL F).trans inf_le_left)
theorem lineParabolic_comap : (lineParabolic F).comap (projection F) =
    lineParabolicSL F :=
  Subgroup.comap_map_eq_self ((projection_ker_le_borelSL F).trans inf_le_right)
theorem borel_comap : (borel F).comap (projection F) = borelSL F :=
  Subgroup.comap_map_eq_self (projection_ker_le_borelSL F)

/-- The local subgroup fixing the vector e₀, not merely its span. -/
def pointLocalSL : Subgroup SL(3, F) := MulAction.stabilizer SL(3, F) (![1,0,0] : Fin 3 → F)

omit [Finite F] in
theorem mem_pointLocalSL_iff (g : SL(3, F)) : g ∈ pointLocalSL F ↔
    g.val 0 0 = 1 ∧ g.val 1 0 = 0 ∧ g.val 2 0 = 0 := by
  change g.val.mulVec (![1,0,0] : Fin 3 → F) = _ ↔ _
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨h0,h1,h2⟩
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, h0, h1, h2]

/-- Matrices fixing the covector v ↦ v₂, hence acting trivially on the
one-dimensional quotient by the standard plane. -/
def lineLocalSL : Subgroup SL(3, F) where
  carrier := {g | ∀ j, g.val 2 j = if j = 2 then 1 else 0}
  one_mem' := by intro j; simp [SpecialLinearGroup.coe_one, Matrix.one_apply, eq_comm]
  mul_mem' := by
    intro a b ha hb j
    change ∀ j, a.val 2 j = if j = 2 then 1 else 0 at ha
    change ∀ j, b.val 2 j = if j = 2 then 1 else 0 at hb
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, ha, hb]
  inv_mem' := by
    intro g hg j
    change ∀ j, g.val 2 j = if j = 2 then 1 else 0 at hg
    have h := congrArg (fun a : SL(3, F) => a.val 2 j) (mul_inv_cancel g)
    change (g.val * g⁻¹.val) 2 j = (1 : Matrix (Fin 3) (Fin 3) F) 2 j at h
    simpa [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg,
      SpecialLinearGroup.coe_one, Matrix.one_apply, eq_comm] using h

omit [Finite F] in
theorem mem_lineLocalSL_iff (g : SL(3, F)) : g ∈ lineLocalSL F ↔
    g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1 := by
  change (∀ j, g.val 2 j = if j = 2 then 1 else 0) ↔ _
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0,h1,h2⟩ j
    fin_cases j <;> assumption

theorem pointLocalSL_le : pointLocalSL F ≤ pointParabolicSL F := by
  intro g hg
  exact (mem_pointParabolicSL_iff F g).mpr ((mem_pointLocalSL_iff F g).mp hg).2

theorem lineLocalSL_le : lineLocalSL F ≤ lineParabolicSL F := by
  intro g hg
  have h := (mem_lineLocalSL_iff F g).mp hg
  exact (mem_lineParabolicSL_iff F g).mpr ⟨h.1,h.2.1⟩

def pointLocal : Subgroup PSL(3, F) := (pointLocalSL F).map (projection F)
def lineLocal : Subgroup PSL(3, F) := (lineLocalSL F).map (projection F)

omit [Finite F] in
private theorem local_projection_injective (P : Subgroup SL(3, F)) (i : Fin 3)
    (hi : ∀ g : P, g.val.val i i = 1) :
    Function.Injective ((projection F).comp P.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro g hg
  apply Subtype.ext
  have hg' : g.val ∈ (projection F).ker := hg
  rw [projection_ker] at hg'
  obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hg'
  have hr1 : r = 1 := by
    have h := hi g
    rw [← hr] at h
    simpa [Matrix.scalar] using h
  apply Subtype.ext
  simpa [hr1] using hr.symm

omit [Finite F] in
theorem pointLocal_projection_injective :
    Function.Injective ((projection F).comp (pointLocalSL F).subtype) :=
  local_projection_injective F _ 0
    (fun g => ((mem_pointLocalSL_iff F g).mp g.property).1)

omit [Finite F] in
theorem lineLocal_projection_injective :
    Function.Injective ((projection F).comp (lineLocalSL F).subtype) :=
  local_projection_injective F _ 2
    (fun g => ((mem_lineLocalSL_iff F g).mp g.property).2.2)

noncomputable def pointLocalProjectEquiv : pointLocalSL F ≃* pointLocal F :=
  MulEquiv.ofBijective ((projection F).subgroupMap (pointLocalSL F))
    ⟨fun _ _ h => pointLocal_projection_injective F (congrArg Subtype.val h),
      (projection F).subgroupMap_surjective _⟩

noncomputable def lineLocalProjectEquiv : lineLocalSL F ≃* lineLocal F :=
  MulEquiv.ofBijective ((projection F).subgroupMap (lineLocalSL F))
    ⟨fun _ _ h => lineLocal_projection_injective F (congrArg Subtype.val h),
      (projection F).subgroupMap_surjective _⟩

omit [Finite F] in
@[simp] theorem pointLocalProjectEquiv_apply (g : pointLocalSL F) :
    (pointLocalProjectEquiv F g : PSL(3, F)) = projection F g := rfl

omit [Finite F] in
@[simp] theorem lineLocalProjectEquiv_apply (g : lineLocalSL F) :
    (lineLocalProjectEquiv F g : PSL(3, F)) = projection F g := rfl

/-- A diagonal element of the flag stabilizer scaling the first coordinate. -/
def pointTorus (a : Fˣ) : SL(3, F) :=
  ⟨diagonal ![(a : F), (↑a⁻¹ : F), 1], by
    simp [det_diagonal, Fin.prod_univ_three]⟩

/-- A diagonal element of the flag stabilizer scaling the plane quotient. -/
def lineTorus (a : Fˣ) : SL(3, F) :=
  ⟨diagonal ![1, (↑a⁻¹ : F), (a : F)], by
    simp [det_diagonal, Fin.prod_univ_three]⟩

theorem pointTorus_mem_borel (a : Fˣ) : pointTorus F a ∈ borelSL F := by
  rw [mem_borelSL_iff]
  simp [pointTorus]

theorem lineTorus_mem_borel (a : Fˣ) : lineTorus F a ∈ borelSL F := by
  rw [mem_borelSL_iff]
  simp [lineTorus]

theorem point_factorization (g : pointParabolicSL F) :
    ∃ l ∈ pointLocalSL F, ∃ b ∈ borelSL F, g.val = l * b := by
  have hg := (mem_pointParabolicSL_iff F g).mp g.property
  have hn : g.val.val 0 0 ≠ 0 := by
    intro hz
    have h := congrArg (fun a : SL(3, F) => a.val 0 0) (inv_mul_cancel g.val)
    change (g.val⁻¹.val * g.val.val) 0 0 = 1 at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hz] at h
  let a := Units.mk0 (g.val.val 0 0) hn
  let b := pointTorus F a⁻¹
  have hb := pointTorus_mem_borel F a⁻¹
  have hl : g.val * b ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    change (g.val.val * b.val) 0 0 = 1 ∧ (g.val.val * b.val) 1 0 = 0 ∧
      (g.val.val * b.val) 2 0 = 0
    simp [b, pointTorus, Matrix.mul_diagonal, a, hg.1, hg.2, hn]
  refine ⟨g.val * b, hl, b⁻¹, (borelSL F).inv_mem hb, ?_⟩
  simp

theorem line_factorization (g : lineParabolicSL F) :
    ∃ l ∈ lineLocalSL F, ∃ b ∈ borelSL F, g.val = l * b := by
  have hg := (mem_lineParabolicSL_iff F g).mp g.property
  have hn : g.val.val 2 2 ≠ 0 := by
    intro hz
    have h := congrArg (fun a : SL(3, F) => a.val 2 2) (mul_inv_cancel g.val)
    change (g.val.val * g.val⁻¹.val) 2 2 = 1 at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hz] at h
  let a := Units.mk0 (g.val.val 2 2) hn
  let b := lineTorus F a⁻¹
  have hb := lineTorus_mem_borel F a⁻¹
  have hl : g.val * b ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    change (g.val.val * b.val) 2 0 = 0 ∧ (g.val.val * b.val) 2 1 = 0 ∧
      (g.val.val * b.val) 2 2 = 1
    simp [b, lineTorus, Matrix.mul_diagonal, a, hg.1, hg.2, hn]
  refine ⟨g.val * b, hl, b⁻¹, (borelSL F).inv_mem hb, ?_⟩
  simp

theorem pointParabolicSL_eq_sup : pointParabolicSL F = pointLocalSL F ⊔ borelSL F := by
  apply le_antisymm _ (sup_le (pointLocalSL_le F) inf_le_left)
  intro g hg
  obtain ⟨l, hl, b, hb, h⟩ := point_factorization F ⟨g, hg⟩
  change g = l * b at h
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hb)

theorem lineParabolicSL_eq_sup : lineParabolicSL F = lineLocalSL F ⊔ borelSL F := by
  apply le_antisymm _ (sup_le (lineLocalSL_le F) inf_le_right)
  intro g hg
  obtain ⟨l, hl, b, hb, h⟩ := line_factorization F ⟨g, hg⟩
  change g = l * b at h
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hb)

theorem pointParabolic_eq_sup : pointParabolic F = pointLocal F ⊔ borel F := by
  unfold pointParabolic pointLocal borel
  rw [pointParabolicSL_eq_sup, Subgroup.map_sup]

theorem lineParabolic_eq_sup : lineParabolic F = lineLocal F ⊔ borel F := by
  unfold lineParabolic lineLocal borel
  rw [lineParabolicSL_eq_sup, Subgroup.map_sup]

/-- The common upper unitriangular subgroup. Its Sylow property in even
characteristic is a separate order calculation. -/
def unipotentSL : Subgroup SL(3, F) := pointLocalSL F ⊓ lineLocalSL F

def unipotent : Subgroup PSL(3, F) := (unipotentSL F).map (projection F)

theorem unipotentSL_le_borelSL : unipotentSL F ≤ borelSL F :=
  inf_le_inf (pointLocalSL_le F) (lineLocalSL_le F)

theorem unipotent_le_borel : unipotent F ≤ borel F :=
  Subgroup.map_mono (unipotentSL_le_borelSL F)

omit [Finite F] in
theorem unipotent_le_pointLocal : unipotent F ≤ pointLocal F :=
  Subgroup.map_mono inf_le_left

omit [Finite F] in
theorem unipotent_le_lineLocal : unipotent F ≤ lineLocal F :=
  Subgroup.map_mono inf_le_right

/-- A literal product decomposition in the projective group, stronger than
an equality of generated subgroups. -/
theorem projective_point_factorization (g : pointParabolic F) :
    ∃ l ∈ pointLocal F, ∃ b ∈ borel F, g.val = l * b := by
  obtain ⟨x, hx, hgx⟩ := g.property
  obtain ⟨l, hl, b, hb, h⟩ := point_factorization F ⟨x, hx⟩
  refine ⟨projection F l, Subgroup.mem_map_of_mem _ hl,
    projection F b, Subgroup.mem_map_of_mem _ hb, ?_⟩
  change x = l * b at h
  rw [← hgx, h, map_mul]

theorem projective_line_factorization (g : lineParabolic F) :
    ∃ l ∈ lineLocal F, ∃ b ∈ borel F, g.val = l * b := by
  obtain ⟨x, hx, hgx⟩ := g.property
  obtain ⟨l, hl, b, hb, h⟩ := line_factorization F ⟨x, hx⟩
  refine ⟨projection F l, Subgroup.mem_map_of_mem _ hl,
    projection F b, Subgroup.mem_map_of_mem _ hb, ?_⟩
  change x = l * b at h
  rw [← hgx, h, map_mul]

end Matrix.PSL3.LinearThree
