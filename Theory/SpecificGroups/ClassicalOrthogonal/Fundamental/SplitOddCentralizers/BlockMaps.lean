module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Elementary orthogonal block maps

An isometry of quadratic spaces transports the actual Siegel generators.
On an orthogonal direct sum, extending either generator by the identity is
again the Siegel transformation with its two parameters in that summand.
Consequently the product of the two elementary groups embeds in the ambient
elementary group. Explicit hyperbolic coordinates realize the split and odd
block embeddings, keeping the odd square coordinate in the complement.

This supplies the block construction used for the fundamental subgroup and
complement in Aschbacher–Smith A.2.17, printed p.39; the coordinate models and
Siegel conventions are those of GLS3 §2.7. No full-isometry substitution or
characteristic restriction is needed.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks
open Theory.AlgebraicGroup
universe u
variable {F U V W : Type u} [Field F]
  [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- Transport of quadratic isometries along an actual isometry of forms. -/
def conjugate {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) : quadraticIsometrySubgroup Q →* quadraticIsometrySubgroup R where
  toFun g := ⟨e.symm.toLinearEquiv.trans (g.val.trans e.toLinearEquiv), by
    apply (mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    exact (e.map_app _).trans (((mem_quadraticIsometrySubgroup _ _).mp g.prop _).trans
      (e.symm.map_app _))⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact e.apply_symm_apply v
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change e (g.val (h.val (e.symm v))) = e (g.val (e.symm (e (h.val (e.symm v)))))
    rw [e.symm_apply_apply]

theorem conjugate_apply {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) (g : quadraticIsometrySubgroup Q) (v : V) :
    (conjugate e g).val v = e (g.val (e.symm v)) := rfl

theorem conjugate_injective {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) : Function.Injective (conjugate e) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have ht := congrArg (fun k : quadraticIsometrySubgroup R => k.val (e v)) hgh
  simpa only [conjugate_apply, e.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq] using ht

theorem polar_transport {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) (x y : U) : R.polarBilin (e x) (e y) = Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, e.map_app]

theorem conjugate_siegel {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) (x y : U) (hx : Q x = 0) (hxy : Q.polarBilin x y = 0) :
    conjugate e (siegelElement Q x y hx hxy) =
      siegelElement R (e x) (e y) ((e.map_app x).trans hx)
        ((polar_transport e x y).trans hxy) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := e.surjective v
  change e (Quadratic.siegel Q x y (e.symm (e w))) = Quadratic.siegel R (e x) (e y) (e w)
  rw [e.symm_apply_apply]
  simp only [Quadratic.siegel, map_sub, map_add, map_smul, polar_transport, e.map_app]

theorem conjugate_mem_elementary {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) (g : elementarySubgroup Q) :
    conjugate e g.val ∈ elementarySubgroup R := by
  have h : elementarySubgroup Q ≤ (elementarySubgroup R).comap (conjugate e) := by
    apply (Subgroup.closure_le _).mpr
    rintro s ⟨x, y, hx, hxy, rfl⟩
    change conjugate e (siegelElement Q x y hx hxy) ∈ elementarySubgroup R
    rw [conjugate_siegel]
    exact siegelElement_mem _ _ _ _ _
  exact h g.prop

def elementaryConjugate {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) : elementarySubgroup Q →* elementarySubgroup R :=
  ((conjugate e).comp (elementarySubgroup Q).subtype).codRestrict _ (conjugate_mem_elementary e)

theorem elementaryConjugate_injective {Q : QuadraticForm F U} {R : QuadraticForm F V}
    (e : Q.IsometryEquiv R) : Function.Injective (elementaryConjugate e) := by
  intro g h hgh
  exact Subtype.ext (conjugate_injective e (congrArg Subtype.val hgh))

/-- Independent quadratic isometries acting on the two summands. -/
def orthogonalProd (Q : QuadraticForm F U) (R : QuadraticForm F V) :
    quadraticIsometrySubgroup Q × quadraticIsometrySubgroup R →*
      quadraticIsometrySubgroup (Q.prod R) where
  toFun g := ⟨g.1.val.prodCongr g.2.val, by
    apply (mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    exact congrArg₂ (· + ·) ((mem_quadraticIsometrySubgroup _ _).mp g.1.prop v.1)
      ((mem_quadraticIsometrySubgroup _ _).mp g.2.prop v.2)⟩
  map_one' := by rfl
  map_mul' _ _ := by rfl

theorem orthogonalProd_apply (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (g : quadraticIsometrySubgroup Q × quadraticIsometrySubgroup R) (v : U × V) :
    (orthogonalProd Q R g).val v = (g.1.val v.1, g.2.val v.2) := rfl

private theorem polar_prod (Q : QuadraticForm F U) (R : QuadraticForm F V) (x y : U × V) :
    (Q.prod R).polarBilin x y = Q.polarBilin x.1 y.1 + R.polarBilin x.2 y.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, QuadraticMap.prod_apply,
    Prod.fst_add, Prod.snd_add]
  ring

private theorem prodLeft_siegel (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (x y : U) (hx : Q x = 0) (hxy : Q.polarBilin x y = 0) :
    orthogonalProd Q R (siegelElement Q x y hx hxy, 1) =
      siegelElement (Q.prod R) (x, 0) (y, 0) (by simpa using hx)
        (by simpa only [polar_prod, map_zero, LinearMap.zero_apply, add_zero] using hxy) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  rintro ⟨a, b⟩
  change (Quadratic.siegel Q x y a, b) = Quadratic.siegel (Q.prod R) (x, 0) (y, 0) (a, b)
  simp [Quadratic.siegel]

private theorem prodRight_siegel (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (x y : V) (hx : R x = 0) (hxy : R.polarBilin x y = 0) :
    orthogonalProd Q R (1, siegelElement R x y hx hxy) =
      siegelElement (Q.prod R) (0, x) (0, y) (by simpa using hx)
        (by simpa only [polar_prod, map_zero, LinearMap.zero_apply, zero_add] using hxy) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  rintro ⟨a, b⟩
  change (a, Quadratic.siegel R x y b) = Quadratic.siegel (Q.prod R) (0, x) (0, y) (a, b)
  simp [Quadratic.siegel]

theorem orthogonalProd_mem_elementary (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (g : elementarySubgroup Q × elementarySubgroup R) :
    orthogonalProd Q R (g.1.val, g.2.val) ∈ elementarySubgroup (Q.prod R) := by
  have hl : elementarySubgroup Q ≤ (elementarySubgroup (Q.prod R)).comap
      ((orthogonalProd Q R).comp (MonoidHom.inl _ _)) := by
    apply (Subgroup.closure_le _).mpr
    rintro s ⟨x, y, hx, hxy, rfl⟩
    change orthogonalProd Q R (siegelElement Q x y hx hxy, 1) ∈ elementarySubgroup (Q.prod R)
    rw [prodLeft_siegel]
    exact siegelElement_mem _ _ _ _ _
  have hr : elementarySubgroup R ≤ (elementarySubgroup (Q.prod R)).comap
      ((orthogonalProd Q R).comp (MonoidHom.inr _ _)) := by
    apply (Subgroup.closure_le _).mpr
    rintro s ⟨x, y, hx, hxy, rfl⟩
    change orthogonalProd Q R (1, siegelElement R x y hx hxy) ∈ elementarySubgroup (Q.prod R)
    rw [prodRight_siegel]
    exact siegelElement_mem _ _ _ _ _
  have heq : (g.1.val, g.2.val) = (g.1.val, 1) * (1, g.2.val) := by simp
  rw [heq, map_mul]
  exact Subgroup.mul_mem _ (hl g.1.prop) (hr g.2.prop)

def elementaryProd (Q : QuadraticForm F U) (R : QuadraticForm F V) :
    elementarySubgroup Q × elementarySubgroup R →* elementarySubgroup (Q.prod R) :=
  ((orthogonalProd Q R).comp ((elementarySubgroup Q).subtype.prodMap
    (elementarySubgroup R).subtype)).codRestrict _ (orthogonalProd_mem_elementary Q R)

theorem elementaryProd_injective (Q : QuadraticForm F U) (R : QuadraticForm F V) :
    Function.Injective (elementaryProd Q R) := by
  intro g h hgh
  have ht (v : U × V) := congrArg (fun k : elementarySubgroup (Q.prod R) => k.val.val v) hgh
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro a
    exact congrArg Prod.fst (ht (a, 0))
  · apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro b
    exact congrArg Prod.snd (ht (0, b))

/-- Elementary block action transported into the specified ambient coordinates. -/
def blockMap (Q : QuadraticForm F U) (R : QuadraticForm F V) (S : QuadraticForm F W)
    (e : (Q.prod R).IsometryEquiv S) :
    elementarySubgroup Q × elementarySubgroup R →* elementarySubgroup S :=
  (elementaryConjugate e).comp (elementaryProd Q R)

theorem blockMap_injective (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (S : QuadraticForm F W) (e : (Q.prod R).IsometryEquiv S) :
    Function.Injective (blockMap Q R S e) :=
  (elementaryConjugate_injective e).comp (elementaryProd_injective Q R)

theorem blockMap_apply (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (S : QuadraticForm F W) (e : (Q.prod R).IsometryEquiv S)
    (g : elementarySubgroup Q × elementarySubgroup R) (v : U × V) :
    (blockMap Q R S e g).val.val (e v) = e (g.1.val.val v.1, g.2.val.val v.2) := by
  change e ((elementaryProd Q R g).val.val (e.symm (e v))) = _
  rw [e.symm_apply_apply]
  rfl


/-- Split the first `a` hyperbolic pairs from the remaining `b` pairs. -/
def splitD (a b : ℕ) : VectorD (a + b) F ≃ₗ[F] VectorD a F × VectorD b F where
  toFun v := (fun i => v (i.map (Fin.castAdd b) (Fin.castAdd b)),
    fun i => v (i.map (Fin.natAdd a) (Fin.natAdd a)))
  invFun v := Sum.elim
    (Fin.addCases (fun i => v.1 (.inl i)) (fun i => v.2 (.inl i)))
    (Fin.addCases (fun i => v.1 (.inr i)) (fun i => v.2 (.inr i)))
  left_inv v := by
    funext i
    cases i with
    | inl i => exact Fin.addCases_castAdd_natAdd (fun j => v (.inl j)) i
    | inr i => exact Fin.addCases_castAdd_natAdd (fun j => v (.inr j)) i
  right_inv v := by
    apply Prod.ext <;> funext i <;> cases i <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem splitD_form (a b : ℕ) (v : VectorD (a + b) F) :
    ((formD a F).prod (formD b F)) (splitD a b v) = formD (a + b) F v := by
  simp only [QuadraticMap.prod_apply, formD_apply]
  rw [Fin.sum_univ_add]
  rfl

def splitDIsometry (a b : ℕ) :
    (formD (a + b) F).IsometryEquiv ((formD a F).prod (formD b F)) where
  __ := splitD a b
  map_app' := splitD_form a b

/-- In the odd space the anisotropic coordinate stays in the complement. -/
def splitB (a b : ℕ) : VectorB (a + b) F ≃ₗ[F] VectorD a F × VectorB b F :=
  ((splitD (F := F) a b).prodCongr (LinearEquiv.refl F F)).trans
    (LinearEquiv.prodAssoc F (VectorD a F) (VectorD b F) F)

theorem splitB_form (a b : ℕ) (v : VectorB (a + b) F) :
    ((formD a F).prod (formB b F)) (splitB a b v) = formB (a + b) F v := by
  simp only [QuadraticMap.prod_apply, formB_apply]
  change formD a F ((splitD a b v.1).1) +
    (formD b F ((splitD a b v.1).2) + v.2 ^ 2) = formD (a + b) F v.1 + v.2 ^ 2
  rw [← add_assoc, ← splitD_form a b v.1]
  rfl

def splitBIsometry (a b : ℕ) :
    (formB (a + b) F).IsometryEquiv ((formD a F).prod (formB b F)) where
  __ := splitB a b
  map_app' := splitB_form a b

/-- Extension by identity in a larger split space. -/
def plusBlocks (a b : ℕ) : OmegaPlus a F × OmegaPlus b F →* OmegaPlus (a + b) F :=
  blockMap _ _ _ (splitDIsometry a b).symm

/-- Extension by identity in a larger odd space. -/
def oddBlocks (a b : ℕ) : OmegaPlus a F × OmegaOdd b F →* OmegaOdd (a + b) F :=
  blockMap _ _ _ (splitBIsometry a b).symm

theorem plusBlocks_injective (a b : ℕ) : Function.Injective (plusBlocks (F := F) a b) :=
  blockMap_injective _ _ _ _

theorem oddBlocks_injective (a b : ℕ) : Function.Injective (oddBlocks (F := F) a b) :=
  blockMap_injective _ _ _ _

end ClassicalOrthogonal.Fundamental.SplitOddBlocks
