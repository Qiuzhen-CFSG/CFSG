module

public import Theory.SpecificGroups.PSL3Four.SylowModel
public import Mathlib.GroupTheory.Sylow

/-!
# The coordinate Sylow subgroup in the actual matrix field extension

The upper-unitriangular matrix with coordinates `(x,y,c)` has entries `x` at
(0,1), `y` at (1,2), and `c` at (0,2). Its image in PSL₃(4) is faithful because
an upper-unitriangular scalar matrix is the identity. Entrywise Frobenius
commutes with this embedding, so it extends to the semidirect products. The
range has order 128, the full 2-part of the field extension's order 40320.

We retain an actual isomorphism onto that Sylow subgroup and explicit matrix
representatives for both root planes and their common center. The normalizers
of those root planes are concrete local groups containing the Sylow. Their
identification as parabolics and their S₅ quotient maps are separate results.

The matrix and scalar-kernel arguments adapt Gerald Höhn's
`Atlas/LinearGroups/UpperUnitriangularThree.lean` and
`Atlas/LinearGroups/UnitriangularThreeProjective.lean`, upstream revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`. The ATLAS Research and Attribution
License 1.0 applies to these adapted portions; see `LICENSES/ATLAS.txt` and
`docs/atlas-porting.md`. Adaptation uses the existing CFSG coordinate group,
CFSG's PSL quotient, and Lean 4.33; the semidirect and marked local constructions
extend the upstream linear-group calculation.

Mathematical source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
§5.3.2 and §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel.MatrixRealization
open Matrix

def matrix (a : U) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a.x, a.c; 0, 1, a.y; 0, 0, 1]

def specialLinear : U →* SL where
  toFun a := ⟨matrix a, by simp [matrix, Matrix.det_fin_three]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix]
  map_mul' a b := by
    apply Subtype.ext
    change matrix (a * b) = matrix a * matrix b
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem specialLinear_injective : Function.Injective specialLinear := by
  intro a b h
  exact U.ext (congrArg (fun g : SL => g 0 1) h)
    (congrArg (fun g : SL => g 1 2) h) (congrArg (fun g : SL => g 0 2) h)

def projective : U →* PSL :=
  (QuotientGroup.mk' (Subgroup.center SL)).comp specialLinear

theorem projective_injective : Function.Injective projective := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hc : specialLinear a ∈ Subgroup.center SL :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨r, _, he⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have hd := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) he
  have hr : r = 1 := by
    change r = 1 at hd
    exact hd
  apply specialLinear_injective
  rw [map_one]
  apply Subtype.ext
  simpa [hr] using he.symm

theorem specialLinear_frob (a : U) : specialLinear (frob a) = slFrobenius (specialLinear a) := by
  apply Subtype.ext
  change matrix (frob a) = (matrix a).map fieldFrobenius
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, frob, Matrix.map_apply]

theorem projective_frob (a : U) : projective (frob a) = pslFrobenius (projective a) := by
  change (specialLinear (frob a) : PSL) = (slFrobenius (specialLinear a) : PSL)
  rw [specialLinear_frob]

def embedding : T →* FieldExtension :=
  SemidirectProduct.map projective (MonoidHom.id C2) (by
    intro t
    ext a
    rcases c2_cases t with rfl | rfl
    · simp
    · change projective (action τ a) = fieldAction (Multiplicative.ofAdd 1) (projective a)
      rw [action_τ, fieldAction_generator, projective_frob])

theorem embedding_injective : Function.Injective embedding := by
  intro a b h
  apply SemidirectProduct.ext
  · exact projective_injective (congrArg (fun g : FieldExtension => g.left) h)
  · exact congrArg (fun g : FieldExtension => g.right) h

theorem card_range : Nat.card embedding.range = 128 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv, card_T]

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def sylow : Sylow 2 FieldExtension := Sylow.ofCard embedding.range (by
  rw [card_range, card_FieldExtension]
  decide +kernel)

def equiv : T ≃* sylow := MonoidHom.ofInjective embedding_injective

@[simp] theorem equiv_apply (a : T) : (equiv a).val = embedding a := rfl

/-- The linear unipotent subgroup inside the matrix extension. -/
def unipotent : Subgroup FieldExtension := S.map embedding
/-- The first root plane, with `y = 0`. -/
def rootPlane₁ : Subgroup FieldExtension := V₁.map embedding
/-- The second root plane, with `x = 0`. -/
def rootPlane₂ : Subgroup FieldExtension := V₂.map embedding
/-- The highest-root subgroup. -/
def highestRoot : Subgroup FieldExtension := Z.map embedding
/-- The highest-root element with entry one. -/
def centralInvolution : FieldExtension := embedding z

def markedEquiv (H : Subgroup T) : H ≃* H.map embedding :=
  H.equivMapOfInjective embedding embedding_injective

@[simp] theorem embedding_left (a : T) : (embedding a).left = projective a.left := rfl
@[simp] theorem embedding_right (a : T) : (embedding a).right = a.right := rfl

@[simp] theorem embedding_inclusion (a : U) :
    embedding (inclusion a) = linearInclusion (projective a) := rfl

/-- The unipotent mark consists of precisely the unitriangular representatives. -/
theorem mem_unipotent (g : FieldExtension) : g ∈ unipotent ↔
    ∃ a : U, linearInclusion (projective a) = g := by
  constructor
  · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨inclusion a, ⟨a, rfl⟩, rfl⟩

/-- The actual Sylow isomorphism carries all marks simultaneously. -/
theorem equiv_marks :
    let f := (sylow : Subgroup FieldExtension).subtype.comp equiv.toMonoidHom
    S.map f = unipotent ∧ V₁.map f = rootPlane₁ ∧
      V₂.map f = rootPlane₂ ∧ Z.map f = highestRoot ∧ f z = centralInvolution :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every root-plane element has the indicated literal matrix representative. -/
theorem mem_rootPlane₁ (g : FieldExtension) : g ∈ rootPlane₁ ↔
    ∃ x c : F, linearInclusion (projective ⟨x, 0, c⟩) = g := by
  constructor
  · rintro ⟨a, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.toAdd.1, p.toAdd.2, rfl⟩
  · rintro ⟨x, c, rfl⟩
    exact ⟨inclusion (axis₁ (Multiplicative.ofAdd (x, c))), ⟨_, rfl⟩, rfl⟩

theorem mem_rootPlane₂ (g : FieldExtension) : g ∈ rootPlane₂ ↔
    ∃ y c : F, linearInclusion (projective ⟨0, y, c⟩) = g := by
  constructor
  · rintro ⟨a, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.toAdd.1, p.toAdd.2, rfl⟩
  · rintro ⟨y, c, rfl⟩
    exact ⟨inclusion (axis₂ (Multiplicative.ofAdd (y, c))), ⟨_, rfl⟩, rfl⟩

theorem mem_highestRoot (g : FieldExtension) : g ∈ highestRoot ↔
    ∃ c : F, linearInclusion (projective ⟨0, 0, c⟩) = g := by
  constructor
  · rintro ⟨a, ⟨p, rfl⟩, rfl⟩
    exact ⟨p.toAdd, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨inclusion (central (Multiplicative.ofAdd c)), ⟨_, rfl⟩, rfl⟩

theorem centralInvolution_matrix :
    centralInvolution = linearInclusion (projective ⟨0, 0, 1⟩) := rfl

theorem rootPlane₁_inf_rootPlane₂ : rootPlane₁ ⊓ rootPlane₂ = highestRoot := by
  rw [rootPlane₁, rootPlane₂, ← Subgroup.map_inf _ _ _ embedding_injective, V₁_inf_V₂]
  rfl

theorem center_unipotent :
    (Subgroup.center unipotent).map unipotent.subtype = highestRoot := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hc := (Subgroup.centerCongr (markedEquiv S).symm ⟨a, ha⟩).property
    have hc' : ((markedEquiv S).symm a : T) ∈ Z := by
      rw [← center_S]
      exact ⟨_, hc, rfl⟩
    refine ⟨_, hc', ?_⟩
    exact congrArg Subtype.val ((markedEquiv S).apply_symm_apply a)
  · rintro ⟨a, ha, rfl⟩
    rw [← center_S] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨markedEquiv S b,
      (Subgroup.centerCongr (markedEquiv S) ⟨b, hb⟩).property, rfl⟩

private theorem conjugate_left (g a : T) (ha : a.right = 1) :
    (g * a * g⁻¹).left = g.left * action g.right a.left * g.left⁻¹ := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
    SemidirectProduct.mul_right, ha, mul_one, ← MulAut.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, MulAut.one_apply]

private theorem normal_V₁ : V₁.Normal where
  conj_mem a ha g := by
    obtain ⟨hr, hy⟩ := (mem_V₁ a).mp ha
    apply (mem_V₁ _).mpr
    refine ⟨by simp [hr], ?_⟩
    rw [conjugate_left g a hr, mul_y, mul_y]
    have h : (action g.right a.left).y = 0 := by
      rcases c2_cases g.right with h | h <;> simp [h, hy]
    rw [h]
    change g.left.y + 0 + -g.left.y = 0
    simp

private theorem normal_V₂ : V₂.Normal where
  conj_mem a ha g := by
    obtain ⟨hr, hx⟩ := (mem_V₂ a).mp ha
    apply (mem_V₂ _).mpr
    refine ⟨by simp [hr], ?_⟩
    rw [conjugate_left g a hr, mul_x, mul_x]
    have h : (action g.right a.left).x = 0 := by
      rcases c2_cases g.right with h | h <;> simp [h, hx]
    rw [h]
    change g.left.x + 0 + -g.left.x = 0
    simp

/-- Intrinsic matrix definitions of the two local groups. Identification with
point and line stabilizers, and their S₅ quotients, is a separate theorem. -/
def local₁ : Subgroup FieldExtension := Subgroup.normalizer (rootPlane₁ : Set FieldExtension)
def local₂ : Subgroup FieldExtension := Subgroup.normalizer (rootPlane₂ : Set FieldExtension)

theorem sylow_le_local₁ : (sylow : Subgroup FieldExtension) ≤ local₁ := by
  let := normal_V₁
  change embedding.range ≤ Subgroup.normalizer (V₁.map embedding : Set FieldExtension)
  rw [MonoidHom.range_eq_map]
  exact (Subgroup.map_mono (Subgroup.le_normalizer_of_normal (H := V₁))).trans
    (Subgroup.le_normalizer_map _)

theorem sylow_le_local₂ : (sylow : Subgroup FieldExtension) ≤ local₂ := by
  let := normal_V₂
  change embedding.range ≤ Subgroup.normalizer (V₂.map embedding : Set FieldExtension)
  rw [MonoidHom.range_eq_map]
  exact (Subgroup.map_mono (Subgroup.le_normalizer_of_normal (H := V₂))).trans
    (Subgroup.le_normalizer_map _)

/-- The same concrete Sylow embedding, with codomain in each local group. -/
def localEmbedding₁ : T →* local₁ := embedding.codRestrict local₁
  (fun a => sylow_le_local₁ ⟨a, rfl⟩)
def localEmbedding₂ : T →* local₂ := embedding.codRestrict local₂
  (fun a => sylow_le_local₂ ⟨a, rfl⟩)

theorem localEmbedding₁_injective : Function.Injective localEmbedding₁ :=
  fun _ _ h => embedding_injective (congrArg Subtype.val h)
theorem localEmbedding₂_injective : Function.Injective localEmbedding₂ :=
  fun _ _ h => embedding_injective (congrArg Subtype.val h)

end Matrix.PSL3Four.SylowModel.MatrixRealization
