module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import BenderSuzuki.MatrixGroups.Unitary

/-!
# Projective graph-involution fixed groups in degree three

The fixed subgroup of a linear-times-inverse-transpose involution of PSL₃(F)
embeds in the determinant-one isometry group of a nondegenerate symmetric
ternary form over F. The form has Gram matrix inverse to the conjugating
matrix. This proves the fixed-group embedding used for the PSL₃ branch of
Aschbacher–Smith E.6.18, printed p.252 (PDF p.263), for the models in Theorem C,
printed p.33. The matrix action conventions are those of GLS3 §2.7.

Perfectness of SL₃ makes its action on the actual scalar quotient faithful.
Thus a trivial linear projective actor is scalar, and the square of the graph
actor forces its conjugating matrix to be symmetric: the intervening scalar
has both square and cube one. For each projective fixed point, multiply a lift
by the square of its central discrepancy. This gives a unique fixed lift,
since the graph actor inverts the exponent-three scalar center. Exactly fixed
matrices preserve the inverse Gram matrix, giving the injective homomorphism.

The construction works over every field; no simplicity, finiteness, prime-field
or orthogonal rank hypothesis is used. Perfectness is reused from the attributed
ATLAS port in `Theory.AtlasPort.ExceptionalIsomorphisms.Elementary`; its source
attribution and license remain in that imported module.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.OddInvolutionFixed
variable {F : Type*} [Field F]

private theorem centerAction_injective : Function.Injective (centerAction F) := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have he : centerAction F = Subgroup.quotientAut (center SL(3,F)) := by
    ext a x
    obtain ⟨y, rfl⟩ := projection_surjective F x
    change centerAction F a (QuotientGroup.mk y) =
      (center SL(3,F)).quotientAut a (QuotientGroup.mk' (center SL(3,F)) y)
    rw [centerAction_mk, Subgroup.quotientAut_apply_mk]
    rfl
  rw [he]
  exact MulAut.quotient_center_injective

private theorem linearConj_eq_one_scalar (g : GL (Fin 3) F)
    (hg : linearConj F g = 1) : ∃ u : Fˣ, GeneralLinearGroup.scalar (Fin 3) u = g := by
  have hs : linearConjSL F g = 1 := centerAction_injective (hg.trans (map_one _).symm)
  have hc (x : SL(3,F)) : g * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * g := by
    have he := congrArg SpecialLinearGroup.toGL (DFunLike.congr_fun hs x)
    rw [linearConjSL_toGL] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hz : g ∈ center (GL (Fin 3) F) := by
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact (congrArg Units.val (hc ⟨t.toMatrix, by simp⟩)).symm
  rwa [GeneralLinearGroup.center_eq_range_scalar] at hz

private theorem inverseTransposeGL_involutive (g : GL (Fin 3) F) :
    inverseTransposeGL (inverseTransposeGL g) = g := Units.ext rfl

private theorem inverseTransposeGL_scalar (u : Fˣ) :
    inverseTransposeGL (GeneralLinearGroup.scalar (Fin 3) u) =
      GeneralLinearGroup.scalar (Fin 3) u⁻¹ := by
  apply Units.ext
  change (GeneralLinearGroup.scalar (Fin 3) u).inv.transpose = _
  simp [GeneralLinearGroup.scalar]

private theorem det_inverseTransposeGL (g : GL (Fin 3) F) :
    GeneralLinearGroup.det (inverseTransposeGL g) = (GeneralLinearGroup.det g)⁻¹ := by
  apply Units.ext
  exact (Matrix.det_transpose g.inv).trans (congrArg Units.val (map_inv GeneralLinearGroup.det g))

/-- The conjugating matrix of an involutory projective graph action is symmetric. -/
theorem graph_involution_symmetric (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1) : g.val.transpose = g.val := by
  have hlin : linearConj F (g * inverseTransposeGL g) = 1 := by
    calc
      _ = (linearConj F g * graph F) ^ 2 := by
        rw [pow_two, mul_assoc, ← mul_assoc (graph F), graph_linearConj,
          mul_assoc, ← pow_two, graph_sq, mul_one, ← map_mul]
      _ = 1 := hg
  obtain ⟨u, hu⟩ := linearConj_eq_one_scalar (g * inverseTransposeGL g) hlin
  have h3 : u ^ 3 = 1 := by
    have he := congrArg GeneralLinearGroup.det hu
    simpa only [GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul,
      det_inverseTransposeGL, mul_inv_cancel] using he
  have hswap : inverseTransposeGL g * g = GeneralLinearGroup.scalar (Fin 3) u := by
    apply mul_left_cancel (a := g)
    calc
      g * (inverseTransposeGL g * g) = GeneralLinearGroup.scalar (Fin 3) u * g := by
        rw [← mul_assoc, ← hu]
      _ = g * GeneralLinearGroup.scalar (Fin 3) u := GeneralLinearGroup.scalar_commute _ _
  have hi : GeneralLinearGroup.scalar (Fin 3) u⁻¹ = GeneralLinearGroup.scalar (Fin 3) u := by
    have he := congrArg inverseTransposeGL hu
    rwa [inverseTransposeGL_scalar, map_mul, inverseTransposeGL_involutive, hswap] at he
  have hui : u⁻¹ = u := by
    apply Units.ext
    simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] using congrArg (fun z : GL (Fin 3) F => z.val 0 0) hi
  have h2 : u ^ 2 = 1 := by simpa only [pow_two, hui] using inv_mul_cancel u
  have hu1 : u = 1 := by simpa only [pow_succ, h2, one_mul] using h3
  have hinv : inverseTransposeGL g = g⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa only [hu1, map_one] using hu.symm
  have he := congrArg (fun z : GL (Fin 3) F => z.inv) hinv
  exact he

private theorem central_cube (x : SL(3,F)) (hx : x ∈ center SL(3,F)) : x ^ 3 = 1 := by
  obtain ⟨r, hr3, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hx
  apply Subtype.ext
  change x.val ^ 3 = 1
  rw [← hr, ← map_pow, (by simpa using hr3 : r ^ 3 = 1), map_one]

private theorem graphActorSL_central (g : GL (Fin 3) F)
    (x : SL(3,F)) (hx : x ∈ center SL(3,F)) :
    (linearConjSL F g * graphSL F) x = x⁻¹ := by
  have ht : SpecialLinearGroup.transpose x = x := by
    obtain ⟨r, _, hr⟩ := SpecialLinearGroup.mem_center_iff.mp hx
    apply Subtype.ext
    change x.val.transpose = x.val
    rw [← hr]
    simp
  change linearConjSL F g (SpecialLinearGroup.transpose x)⁻¹ = x⁻¹
  rw [ht]
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  have hc := (SpecialLinearGroup.toGL_mem_center_iff x⁻¹).mpr ((center SL(3,F)).inv_mem hx)
  rw [mem_center_iff.mp hc g, mul_inv_cancel_right]

/-- Projectivization restricted to the fixed subgroup of the lifted graph actor. -/
def graphFixedProjection (g : GL (Fin 3) F) :
    (linearConjSL F g * graphSL F).fixedSubgroup →*
      (linearConj F g * graph F).fixedSubgroup :=
  ((projection F).comp (linearConjSL F g * graphSL F).fixedSubgroup.subtype).codRestrict _ (by
    intro x
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change projection F ((linearConjSL F g * graphSL F) x.val) = projection F x.val
    rw [(MulAut.mem_fixedSubgroup _ _).mp x.property])

theorem graphFixedProjection_injective (g : GL (Fin 3) F) :
    Function.Injective (graphFixedProjection g) := by
  apply (graphFixedProjection g).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  have hp : projection F x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hz : x.val ∈ center SL(3,F) := by
    rw [← projection_ker F]
    exact hp
  have he : x.val⁻¹ = x.val :=
    (graphActorSL_central g x.val hz).symm.trans ((MulAut.mem_fixedSubgroup _ _).mp x.property)
  have h2 : x.val ^ 2 = 1 := by simpa only [pow_two, he] using inv_mul_cancel x.val
  change x.val = 1
  simpa only [pow_succ, h2, one_mul] using central_cube x.val hz

/-- Multiplying a projective fixed lift by the square of its central discrepancy
produces an exactly fixed lift. -/
theorem graphFixedProjection_surjective (g : GL (Fin 3) F) :
    Function.Surjective (graphFixedProjection g) := by
  intro b
  obtain ⟨x, hx⟩ := projection_surjective F b.val
  let a := linearConjSL F g * graphSL F
  let k := x⁻¹ * a x
  have hproj (y : SL(3,F)) : projection F (a y) =
      (linearConj F g * graph F) (projection F y) := rfl
  have hk : projection F k = 1 := by
    change projection F (x⁻¹ * a x) = 1
    rw [map_mul, map_inv, hproj, hx,
      (MulAut.mem_fixedSubgroup _ _).mp b.property, inv_mul_cancel]
  have hkz : k ∈ center SL(3,F) := by
    rw [← projection_ker F]
    exact hk
  have hk3 : k ^ 3 = 1 := central_cube k hkz
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hck : a k = k⁻¹ := graphActorSL_central g k hkz
  have hcx : a x = x * k := by simp [k]
  have hz : a (x * k ^ 2) = x * k ^ 2 := by
    rw [map_mul, map_pow, hck, hcx]
    calc
      x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
      _ = x * k ^ 2 := by rw [hki]
  refine ⟨⟨x * k ^ 2, (MulAut.mem_fixedSubgroup _ _).mpr hz⟩, Subtype.ext ?_⟩
  change projection F (x * k ^ 2) = b.val
  simp [map_mul, map_pow, hk, hx]

/-- The actual projective and linear fixed groups are isomorphic, including
when the central quotient has a nontrivial kernel. -/
noncomputable def graphProjectiveFixedEquiv (g : GL (Fin 3) F) :
    (linearConj F g * graph F).fixedSubgroup ≃*
      (linearConjSL F g * graphSL F).fixedSubgroup :=
  (MulEquiv.ofBijective (graphFixedProjection g)
    ⟨graphFixedProjection_injective g, graphFixedProjection_surjective g⟩).symm

/-- The fixed lift projects to the original projective element. -/
@[simp] theorem graphProjectiveFixedEquiv_projection (g : GL (Fin 3) F)
    (x : (linearConj F g * graph F).fixedSubgroup) :
    projection F (graphProjectiveFixedEquiv g x).val = x.val :=
  congrArg Subtype.val ((graphProjectiveFixedEquiv g).symm_apply_apply x)

open BenderSuzuki.MatrixGroups

/-- The inverse of the symmetric conjugating matrix is the Gram matrix
preserved by the graph actor's fixed matrices. -/
def graphOrthogonalForm (g : GL (Fin 3) F) (hs : g.val.transpose = g.val) :
    HermitianForm 3 F where
  conj := 1
  conj_involutive := fun _ => rfl
  form := g.inv
  form_hermitian := by
    have hi : inverseTransposeGL g = g⁻¹ := by
      apply inv_injective
      exact Units.ext hs
    exact congr_fun₂ (congrArg Units.val hi)
  form_nondegenerate := GeneralLinearGroup.det_ne_zero g⁻¹

@[simp] theorem graphOrthogonalForm_conj (g : GL (Fin 3) F) (hs : g.val.transpose = g.val) :
    (graphOrthogonalForm g hs).conj = 1 := by rfl

@[simp] theorem graphOrthogonalForm_form (g : GL (Fin 3) F) (hs : g.val.transpose = g.val) :
    (graphOrthogonalForm g hs).form = g.inv := by rfl

private theorem graphLinearFixed_mem_orthogonal (g : GL (Fin 3) F)
    (hs : g.val.transpose = g.val) (x : (linearConjSL F g * graphSL F).fixedSubgroup) :
    SpecialLinearGroup.toGL x.val ∈ (graphOrthogonalForm g hs).specialSubgroup := by
  apply ((graphOrthogonalForm g hs).mem_specialSubgroup_iff _).mpr
  refine ⟨?_, SpecialLinearGroup.coeToGL_det x.val⟩
  have he := congrArg SpecialLinearGroup.toGL ((MulAut.mem_fixedSubgroup _ _).mp x.property)
  change SpecialLinearGroup.toGL (linearConjSL F g (graphSL F x.val)) = _ at he
  rw [linearConjSL_toGL, graphSL_toGL] at he
  have hm : (inverseTransposeGL (SpecialLinearGroup.toGL x.val))⁻¹ * g⁻¹ *
      SpecialLinearGroup.toGL x.val = g⁻¹ := by
    calc
      _ = (inverseTransposeGL (SpecialLinearGroup.toGL x.val))⁻¹ * g⁻¹ *
          (g * inverseTransposeGL (SpecialLinearGroup.toGL x.val) * g⁻¹) := by rw [he]
      _ = g⁻¹ := by group
  exact congrArg Units.val hm

/-- An exactly fixed special linear matrix preserves the inverse Gram matrix. -/
def graphLinearFixedToOrthogonal (g : GL (Fin 3) F) (hs : g.val.transpose = g.val) :
    (linearConjSL F g * graphSL F).fixedSubgroup →*
      (graphOrthogonalForm g hs).specialSubgroup :=
  (SpecialLinearGroup.toGL.comp (linearConjSL F g * graphSL F).fixedSubgroup.subtype).codRestrict _
    (graphLinearFixed_mem_orthogonal g hs)

theorem graphLinearFixedToOrthogonal_injective (g : GL (Fin 3) F)
    (hs : g.val.transpose = g.val) : Function.Injective (graphLinearFixedToOrthogonal g hs) := by
  intro x y he
  apply Subtype.ext
  exact SpecialLinearGroup.toGL_injective (congrArg Subtype.val he)

/-- Embed the actual projective fixed group into a ternary special orthogonal
group. The scalar correction is supplied by `graphProjectiveFixedEquiv`. -/
noncomputable def graphFixedToOrthogonal (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1) :
    (linearConj F g * graph F).fixedSubgroup →*
      (graphOrthogonalForm g (graph_involution_symmetric g hg)).specialSubgroup :=
  (graphLinearFixedToOrthogonal g (graph_involution_symmetric g hg)).comp
    (graphProjectiveFixedEquiv g).toMonoidHom

/-- The orthogonal matrix is the unique exactly fixed lift of the projective point. -/
theorem graphFixedToOrthogonal_apply (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1)
    (x : (linearConj F g * graph F).fixedSubgroup) :
    (graphFixedToOrthogonal g hg x).val =
      SpecialLinearGroup.toGL (graphProjectiveFixedEquiv g x).val := by rfl

theorem graphFixedToOrthogonal_injective (g : GL (Fin 3) F)
    (hg : (linearConj F g * graph F) ^ 2 = 1) :
    Function.Injective (graphFixedToOrthogonal g hg) :=
  (graphLinearFixedToOrthogonal_injective g (graph_involution_symmetric g hg)).comp
    (graphProjectiveFixedEquiv g).injective

/-- Every involutory linear-times-graph projective action has its full fixed
group embedded in an actual ternary orthogonal group over the same field. -/
theorem exists_graphFixed_orthogonal_embedding (g : GL (Fin 3) F)
    (hg : orderOf (linearConj F g * graph F) = 2) :
    ∃ J : HermitianForm 3 F, J.conj = 1 ∧
      ∃ f : (linearConj F g * graph F).fixedSubgroup →* J.specialSubgroup,
        Function.Injective f := by
  have hs : (linearConj F g * graph F) ^ 2 = 1 := hg ▸ pow_orderOf_eq_one _
  exact ⟨graphOrthogonalForm g (graph_involution_symmetric g hs), rfl,
    graphFixedToOrthogonal g hs, graphFixedToOrthogonal_injective g hs⟩

end Matrix.PSL3.OddInvolutionFixed
