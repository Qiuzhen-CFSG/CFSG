module
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.Basic

/-!
# The two geometric five-point actions

The point stabilizer acts on the five incident lines, and the plane stabilizer
acts on the five incident points. These are restrictions of the actual paired
matrix-and-Frobenius action, transported to permutations of `Fin 5`.

The projective plane has 21 points and order four. Transitivity of the linear
point and contragredient line actions gives order 1920 for each parabolic.
Explicit unitriangular representatives show that the respective root planes
lie in the action kernels; both root planes have order 16. Consequently a
surjectivity proof will identify the exact kernels by counting.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and the exceptional case of §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel.MatrixRealization
open Configuration Projectivization
local instance : DecidableEq F := Classical.decEq _

/-- The lines through the point fixed by the first parabolic. -/
abbrev Pencil₁ := {l : PG // standardPoint ∈ l}
/-- The points on the plane fixed by the second parabolic. -/
abbrev Pencil₂ := {p : PG // p ∈ standardPlane}

theorem card_projectivePlane : Nat.card PG = 21 := by
  rw [Projectivization.card'']
  norm_num [Nat.card_fun, card_F]

theorem order_projectivePlane : ProjectivePlane.order PG PG = 4 := by
  let : Fintype PG := Fintype.ofFinite PG
  have h := ProjectivePlane.card_points PG PG
  rw [← Nat.card_eq_fintype_card, card_projectivePlane] at h
  nlinarith

theorem card_pencil₁ : Nat.card Pencil₁ = 5 := by
  change lineCount PG standardPoint = 5
  rw [ProjectivePlane.lineCount_eq, order_projectivePlane]

theorem card_pencil₂ : Nat.card Pencil₂ = 5 := by
  change pointCount PG standardPlane = 5
  rw [ProjectivePlane.pointCount_eq, order_projectivePlane]

theorem parabolic₁_preserves_pencil (g : parabolic₁) (l : PG) :
    standardPoint ∈ lineAction g.val l ↔ standardPoint ∈ l := by
  have h := Collineation.mem_iff (pairedAction g.val) standardPoint l
  change pointAction g.val standardPoint ∈ lineAction g.val l ↔ _ at h
  rwa [(mem_parabolic₁ _).mp g.property] at h

theorem parabolic₂_preserves_pencil (g : parabolic₂) (p : PG) :
    pointAction g.val p ∈ standardPlane ↔ p ∈ standardPlane := by
  have h := Collineation.mem_iff (pairedAction g.val) p standardPlane
  change pointAction g.val p ∈ lineAction g.val standardPlane ↔ _ at h
  rwa [(mem_parabolic₂ _).mp g.property] at h

/-- Restriction of the actual covector action to the lines through `standardPoint`. -/
def pencilAction₁ : parabolic₁ →* Equiv.Perm Pencil₁ where
  toFun g := (lineAction g.val).subtypePerm (parabolic₁_preserves_pencil g)
  map_one' := by ext l; exact congrArg (fun e : Equiv.Perm PG => e l.val) (map_one lineAction)
  map_mul' g h := by
    ext l
    exact congrArg (fun e : Equiv.Perm PG => e l.val) (map_mul lineAction g.val h.val)

/-- Restriction of the actual point action to the points on `standardPlane`. -/
def pencilAction₂ : parabolic₂ →* Equiv.Perm Pencil₂ where
  toFun g := (pointAction g.val).subtypePerm (parabolic₂_preserves_pencil g)
  map_one' := by ext p; exact congrArg (fun e : Equiv.Perm PG => e p.val) (map_one pointAction)
  map_mul' g h := by
    ext p
    exact congrArg (fun e : Equiv.Perm PG => e p.val) (map_mul pointAction g.val h.val)

@[simp] theorem pencilAction₁_apply (g : parabolic₁) (l : Pencil₁) :
    (pencilAction₁ g l).val = lineAction g.val l.val := rfl
@[simp] theorem pencilAction₂_apply (g : parabolic₂) (p : Pencil₂) :
    (pencilAction₂ g p).val = pointAction g.val p.val := rfl

/-- A labeling of the geometric pencil by five letters. -/
def pencilEquiv₁ : Pencil₁ ≃ Fin 5 := by
  let : Fintype Pencil₁ := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, card_pencil₁])

/-- A labeling of the five geometric points by five letters. -/
def pencilEquiv₂ : Pencil₂ ≃ Fin 5 := by
  let : Fintype Pencil₂ := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, card_pencil₂])

/-- The first geometric permutation representation, transported to five letters. -/
def fivePointAction₁ : parabolic₁ →* Equiv.Perm (Fin 5) :=
  pencilEquiv₁.permCongrHom.toMonoidHom.comp pencilAction₁
/-- The second geometric permutation representation, transported to five letters. -/
def fivePointAction₂ : parabolic₂ →* Equiv.Perm (Fin 5) :=
  pencilEquiv₂.permCongrHom.toMonoidHom.comp pencilAction₂

theorem fivePointAction₁_eq_one_iff (g : parabolic₁) :
    fivePointAction₁ g = 1 ↔ pencilAction₁ g = 1 :=
  pencilEquiv₁.permCongrHom.map_eq_one_iff

theorem fivePointAction₂_eq_one_iff (g : parabolic₂) :
    fivePointAction₂ g = 1 ↔ pencilAction₂ g = 1 :=
  pencilEquiv₂.permCongrHom.map_eq_one_iff

theorem mem_ker_fivePointAction₁ (g : parabolic₁) :
    g ∈ fivePointAction₁.ker ↔ ∀ l : PG, standardPoint ∈ l → lineAction g.val l = l := by
  rw [MonoidHom.mem_ker, fivePointAction₁_eq_one_iff]
  constructor
  · intro h l hl
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨l, hl⟩)
  · intro h
    ext l
    exact h l.val l.property

theorem mem_ker_fivePointAction₂ (g : parabolic₂) :
    g ∈ fivePointAction₂.ker ↔ ∀ p : PG, p ∈ standardPlane → pointAction g.val p = p := by
  rw [MonoidHom.mem_ker, fivePointAction₂_eq_one_iff]
  constructor
  · intro h p hp
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨p, hp⟩)
  · intro h
    ext p
    exact h p.val p.property


/-- Relabeling the pencil preserves surjectivity. -/
theorem fivePointAction₁_surjective_iff :
    Function.Surjective fivePointAction₁ ↔ Function.Surjective pencilAction₁ := by
  constructor
  · intro h σ
    obtain ⟨g, hg⟩ := h (pencilEquiv₁.permCongrHom σ)
    exact ⟨g, pencilEquiv₁.permCongrHom.injective hg⟩
  · intro h σ
    obtain ⟨g, hg⟩ := h (pencilEquiv₁.permCongrHom.symm σ)
    refine ⟨g, ?_⟩
    change pencilEquiv₁.permCongrHom (pencilAction₁ g) = σ
    rw [hg]
    exact pencilEquiv₁.permCongrHom.apply_symm_apply σ

/-- Relabeling the point set preserves surjectivity. -/
theorem fivePointAction₂_surjective_iff :
    Function.Surjective fivePointAction₂ ↔ Function.Surjective pencilAction₂ := by
  constructor
  · intro h σ
    obtain ⟨g, hg⟩ := h (pencilEquiv₂.permCongrHom σ)
    exact ⟨g, pencilEquiv₂.permCongrHom.injective hg⟩
  · intro h σ
    obtain ⟨g, hg⟩ := h (pencilEquiv₂.permCongrHom.symm σ)
    refine ⟨g, ?_⟩
    change pencilEquiv₂.permCongrHom (pencilAction₂ g) = σ
    rw [hg]
    exact pencilEquiv₂.permCongrHom.apply_symm_apply σ

@[simp] theorem standardPoint_mem_mk (v : Fin 3 → F) (hv : v ≠ 0) :
    standardPoint ∈ mk F v hv ↔ v 0 = 0 := by
  simp [standardPoint, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_three]

@[simp] theorem mk_mem_standardPlane (v : Fin 3 → F) (hv : v ≠ 0) :
    mk F v hv ∈ standardPlane ↔ v 2 = 0 := by
  simp [standardPlane, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_three]

theorem rootPlane₁_le_parabolic₁ : rootPlane₁ ≤ parabolic₁ := by
  intro g hg
  obtain ⟨x, c, rfl⟩ := (mem_rootPlane₁ g).mp hg
  exact (mem_parabolic₁_iff_left _).mpr (projective_mem_parabolic₁ _)

theorem rootPlane₂_le_parabolic₂ : rootPlane₂ ≤ parabolic₂ := by
  intro g hg
  obtain ⟨y, c, rfl⟩ := (mem_rootPlane₂ g).mp hg
  exact (mem_parabolic₂_iff_left _).mpr (projective_mem_parabolic₂ _)

/-- A first root-plane element fixes every line through its centre. -/
theorem rootPlane₁_fixes_pencil {g : FieldExtension} (hg : g ∈ rootPlane₁)
    (l : PG) (hl : standardPoint ∈ l) : lineAction g l = l := by
  obtain ⟨x, c, rfl⟩ := (mem_rootPlane₁ g).mp hg
  induction l using Projectivization.ind with | h v hv =>
  have hv0 : v 0 = 0 := (standardPoint_mem_mk v hv).mp hl
  change SpecialLinearGroup.inverseTranspose (specialLinear ⟨x, 0, c⟩) • mk F v hv = _
  rw [Projectivization.smul_mk]
  congr 1
  change ((specialLinear ⟨x, 0, c⟩)⁻¹.val.transpose) *ᵥ v = v
  rw [← map_inv]
  change (matrix ((⟨x, 0, c⟩ : U)⁻¹)).transpose *ᵥ v = v
  have hy : ((⟨x, 0, c⟩ : U)⁻¹).y = 0 := neg_zero
  ext i
  fin_cases i <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0, hy]

/-- A second root-plane element fixes every point of its axis. -/
theorem rootPlane₂_fixes_pencil {g : FieldExtension} (hg : g ∈ rootPlane₂)
    (p : PG) (hp : p ∈ standardPlane) : pointAction g p = p := by
  obtain ⟨y, c, rfl⟩ := (mem_rootPlane₂ g).mp hg
  induction p using Projectivization.ind with | h v hv =>
  have hv2 : v 2 = 0 := (mk_mem_standardPlane v hv).mp hp
  change specialLinear ⟨0, y, c⟩ • mk F v hv = _
  rw [Projectivization.smul_mk]
  congr 1
  change matrix ⟨0, y, c⟩ *ᵥ v = v
  ext i
  fin_cases i <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv2]

theorem rootPlane₁_le_ker_fivePointAction₁ :
    rootPlane₁.subgroupOf parabolic₁ ≤ fivePointAction₁.ker := by
  intro g hg
  exact (mem_ker_fivePointAction₁ g).mpr (rootPlane₁_fixes_pencil hg)

theorem rootPlane₂_le_ker_fivePointAction₂ :
    rootPlane₂.subgroupOf parabolic₂ ≤ fivePointAction₂.ker := by
  intro g hg
  exact (mem_ker_fivePointAction₂ g).mpr (rootPlane₂_fixes_pencil hg)


/-- The actual linear subgroup is already transitive on projective points. -/
theorem pointAction_transitive (p q : PG) : ∃ g : FieldExtension, pointAction g p = q := by
  obtain ⟨A, hA⟩ := MulAction.exists_smul_eq SL p q
  exact ⟨linearInclusion (A : PSL), hA⟩

/-- The contragredient linear action is transitive on projective lines. -/
theorem lineAction_transitive (l m : PG) : ∃ g : FieldExtension, lineAction g l = m := by
  obtain ⟨A, hA⟩ := MulAction.exists_smul_eq SL l m
  refine ⟨linearInclusion ((A.transpose)⁻¹ : PSL), ?_⟩
  change SpecialLinearGroup.inverseTranspose (A.transpose)⁻¹ • l = m
  have h : SpecialLinearGroup.inverseTranspose (A.transpose)⁻¹ = A := by
    change (((A.transpose)⁻¹)⁻¹).transpose = A
    rw [inv_inv]
    rfl
  rwa [h]

private theorem card_stabilizer_comap {G X : Type*} [Group G]
    (ρ : G →* Equiv.Perm X) (x : X) (ht : ∀ y : X, ∃ g : G, ρ g x = y) :
    Nat.card X * Nat.card ((MulAction.stabilizer (Equiv.Perm X) x).comap ρ) =
      Nat.card G := by
  let : MulAction G X := MulAction.compHom X ρ
  have ho : MulAction.orbit G x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact ht y
  have hc : Nat.card (MulAction.orbit G x) = Nat.card X := by
    rw [ho]
    exact Nat.card_congr (Equiv.Set.univ X)
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)
  rw [Nat.card_prod, hc] at h
  exact h

theorem card_parabolic₁ : Nat.card parabolic₁ = 1920 := by
  have h := card_stabilizer_comap pointAction standardPoint (pointAction_transitive standardPoint)
  change Nat.card PG * Nat.card parabolic₁ = Nat.card FieldExtension at h
  rw [card_projectivePlane, card_FieldExtension] at h
  omega

theorem card_parabolic₂ : Nat.card parabolic₂ = 1920 := by
  have h := card_stabilizer_comap lineAction standardPlane (lineAction_transitive standardPlane)
  change Nat.card PG * Nat.card parabolic₂ = Nat.card FieldExtension at h
  rw [card_projectivePlane, card_FieldExtension] at h
  omega

theorem card_rootPlane₁_subgroupOf_parabolic₁ :
    Nat.card (rootPlane₁.subgroupOf parabolic₁) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe rootPlane₁_le_parabolic₁).toEquiv,
    card_rootPlane₁]

theorem card_rootPlane₂_subgroupOf_parabolic₂ :
    Nat.card (rootPlane₂.subgroupOf parabolic₂) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe rootPlane₂_le_parabolic₂).toEquiv,
    card_rootPlane₂]

end Matrix.PSL3Four.SylowModel.MatrixRealization
