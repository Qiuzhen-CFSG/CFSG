module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.GraphFixed
public import Theory.SpecificGroups.PSp4Three.Transvections
public import Mathlib.FieldTheory.Fixed

/-!
# The graph-fixed symplectic group in dimension five

The identity bilinear form in characteristic two splits as a nondegenerate
alternating four-space and its all-ones vector. Explicit coordinates begin
with the two vectors of the existing unitary flag. Every bilinear isometry
fixes the last summand, and restriction and extension give inverse group
maps with the actual symplectic matrix carrier. Entrywise descent to the
stored fixed field identifies this bilinear group with graph-fixed SU₅.
The scalar-corrected fixed projection then identifies graph-fixed PSU₅(4)
with Sp₄ over the same fixed field, preserving the literal projection.

Source: Aschbacher--Smith F.4.37(1), printed p.293 of `refs/quasithin.pdf`.
This establishes the native fixed group, not ambient centralizer Sylow
placement or the outer involution selection required for F.4.38.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {K : Type*} [Field K] [CharP K 2]
local notation "V" => Matrix.PSp4Three.Vector 2 K

private def coordinates : (V × K) ≃ₗ[K] (Fin 5 → K) where
  toFun x := ![x.1 (.inl 0)+x.1 (.inr 1)+x.2,
    x.1 (.inl 0)+x.1 (.inr 0)+x.1 (.inr 1)+x.2,
    x.1 (.inl 1)+x.2, x.1 (.inl 1)+x.1 (.inr 1)+x.2,
    x.1 (.inr 0)+x.1 (.inr 1)+x.2]
  invFun v := (Sum.elim ![v 1+v 4,v 0+v 1+v 3+v 4] ![v 0+v 1,v 2+v 3],
    v 0+v 1+v 2+v 3+v 4)
  left_inv x := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> simp <;>
        ring_nf <;> simp [CharTwo.ofNat_eq_mod]
    · simp
      ring_nf
      simp [CharTwo.ofNat_eq_mod]
  right_inv v := by
    funext i
    fin_cases i <;> simp <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

private theorem coordinates_dot (x y : V × K) :
    dotProduct (coordinates x) (coordinates y) =
      Matrix.PSp4Three.form x.1 y.1+x.2*y.2 := by
  simp [coordinates,dotProduct,Fin.sum_univ_succ,Matrix.PSp4Three.form_apply,
    CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]


/-- Linear isometries of the five-dimensional identity bilinear form. -/
private def dotGroup (K : Type*) [Field K] : Subgroup ((Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) where
  carrier := {g | ∀ x y, dotProduct (g x) (g y) = dotProduct x y}
  one_mem' := fun _ _ => rfl
  mul_mem' hg hh x y := (hg _ _).trans (hh x y)
  inv_mem' {g} hg x y := by
    have he := hg (g.symm x) (g.symm y)
    change dotProduct (g.symm x) (g.symm y)=dotProduct x y
    simpa only [g.apply_symm_apply] using he.symm

private def splitAction (g : dotGroup K) : (V × K) ≃ₗ[K] (V × K) :=
  (coordinates.trans g.val).trans coordinates.symm

private theorem split_preserves (g : dotGroup K) (x y : V × K) :
    Matrix.PSp4Three.form (splitAction g x).1 (splitAction g y).1 +
      (splitAction g x).2*(splitAction g y).2 =
    Matrix.PSp4Three.form x.1 y.1+x.2*y.2 := by
  rw [←coordinates_dot,←coordinates_dot]
  simpa only [splitAction,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] using
    g.property (coordinates x) (coordinates y)

private theorem split_snd (g : dotGroup K) (x : V × K) :
    (splitAction g x).2=x.2 := by
  apply CharTwo.sq_injective
  have he := split_preserves g x x
  simpa only [Matrix.PSp4Three.form_self,zero_add,pow_two] using he

private theorem split_axis (g : dotGroup K) (a : K) :
    splitAction g (0,a)=(0,a) := by
  apply Prod.ext _ (split_snd g _)
  apply Matrix.PSp4Three.form_left_separating
  intro y
  let x := (splitAction g).symm (y,0)
  have hx : splitAction g x=(y,0) := (splitAction g).apply_symm_apply _
  have hx2 : x.2=0 := (split_snd g x).symm.trans (congrArg Prod.snd hx)
  have he := split_preserves g (0,a) x
  rw [hx,hx2] at he
  simpa using he

private theorem split_first (g : dotGroup K) (x : V × K) :
    (splitAction g x).1=(splitAction g (x.1,0)).1 := by
  have he : x=(x.1,0)+(0,x.2) := by simp
  conv_lhs => rw [he,map_add,split_axis]
  simp

private def restriction (g : dotGroup K) : V ≃ₗ[K] V where
  toFun x := (splitAction g (x,0)).1
  invFun x := (splitAction g⁻¹ (x,0)).1
  left_inv x := by
    dsimp only
    rw [←split_first g⁻¹ (splitAction g (x,0))]
    change ((coordinates.symm (g.val.symm (coordinates
      (coordinates.symm (g.val (coordinates (x,0)))))))).1=x
    simp
  right_inv x := by
    dsimp only
    rw [←split_first g (splitAction g⁻¹ (x,0))]
    change ((coordinates.symm (g.val (coordinates
      (coordinates.symm (g.val.symm (coordinates (x,0)))))))).1=x
    simp
  map_add' x y := by
    simpa using congrArg Prod.fst (map_add (splitAction g) (x,0) (y,0))
  map_smul' a x := by
    simpa using congrArg Prod.fst (map_smul (splitAction g) a (x,0))

private theorem restriction_preserves (g : dotGroup K) (x y : V) :
    Matrix.PSp4Three.form (restriction g x) (restriction g y)=
      Matrix.PSp4Three.form x y := by
  have he := split_preserves g (x,0) (y,0)
  simpa [restriction,split_snd] using he

/-- Restriction to the alternating complement of the all-ones vector. -/
private def toSymplectic : dotGroup K →* Matrix.PSp4Three.Sp 2 K where
  toFun g := Matrix.PSp4Three.ofLinear (restriction g) (restriction_preserves g)
  map_one' := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro x
    rw [Matrix.PSp4Three.ofLinear_apply,one_smul]
    change (coordinates.symm (coordinates (x,0))).1=x
    simp
  map_mul' g h := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro x
    rw [mul_smul,Matrix.PSp4Three.ofLinear_apply,Matrix.PSp4Three.ofLinear_apply,
      Matrix.PSp4Three.ofLinear_apply]
    change (splitAction (g*h) (x,0)).1=
      (splitAction g ((splitAction h (x,0)).1,0)).1
    rw [←split_first g (splitAction h (x,0))]
    simp only [splitAction,LinearEquiv.trans_apply,Subgroup.coe_mul,
      LinearEquiv.mul_apply,LinearEquiv.apply_symm_apply]

private def extend (g : Matrix.PSp4Three.Sp 2 K) : dotGroup K :=
  ⟨(coordinates.symm.trans ((Matrix.PSp4Three.toLinear g).prodCongr
      (LinearEquiv.refl K K))).trans coordinates,by
    intro x y
    change dotProduct (coordinates (g • (coordinates.symm x).1,(coordinates.symm x).2))
      (coordinates (g • (coordinates.symm y).1,(coordinates.symm y).2))=dotProduct x y
    rw [coordinates_dot]
    rw [show Matrix.PSp4Three.form (g • (coordinates.symm x).1)
        (g • (coordinates.symm y).1) =
        Matrix.PSp4Three.form (coordinates.symm x).1 (coordinates.symm y).1 from
      Matrix.PSp4Three.preserves g _ _]
    rw [←coordinates_dot]
    simp⟩

/-- The full identity-bilinear group in odd dimension five is exactly Sp₄
in characteristic two, with explicit coordinates on its alternating part. -/
private def dotSymplecticEquiv : dotGroup K ≃* Matrix.PSp4Three.Sp 2 K :=
  MulEquiv.ofBijective toSymplectic ⟨by
    intro g h he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply coordinates.symm.injective
    have he' := congrArg (fun a : Matrix.PSp4Three.Sp 2 K =>
      a • (coordinates.symm x).1) he
    simp only [toSymplectic,MonoidHom.coe_mk,OneHom.coe_mk,
      Matrix.PSp4Three.ofLinear_apply] at he'
    have hf : (splitAction g (coordinates.symm x)).1=
        (splitAction h (coordinates.symm x)).1 := by
      rw [split_first g,split_first h]
      exact he'
    have hh := Prod.ext hf ((split_snd g _).trans (split_snd h _).symm)
    simpa only [splitAction,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] using hh,
    by
      intro g
      refine ⟨extend g,?_⟩
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro x
      change Matrix.PSp4Three.ofLinear (restriction (extend g))
        (restriction_preserves (extend g)) • x=g • x
      rw [Matrix.PSp4Three.ofLinear_apply]
      simp [restriction,splitAction,extend]⟩


private def linearEquivalence : GL (Fin 5) K ≃* ((Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) :=
  GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 5 → K))

private def linearMatrix : dotGroup K →* GL (Fin 5) K :=
  linearEquivalence.symm.toMonoidHom.comp (dotGroup K).subtype

omit [CharP K 2] in
private theorem linearMatrix_mulVec (g : dotGroup K) (x : Fin 5 → K) :
    (linearMatrix g).val *ᵥ x=g.val x :=
  congrArg (fun a : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) => a x)
    (linearEquivalence.apply_symm_apply g.val)

omit [CharP K 2] in
private theorem linearMatrix_orthogonal (g : dotGroup K) :
    (linearMatrix g).val.transpose*(linearMatrix g).val=1 := by
  ext i j
  have he := g.property (Pi.single i 1) (Pi.single j 1)
  simpa [←linearMatrix_mulVec,Matrix.mulVec_single,
    dotProduct,Pi.single_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.one_apply,eq_comm] using he


private theorem orthogonal_det (A : Matrix (Fin 5) (Fin 5) K)
    (hA : A.transpose*A=1) : A.det=1 := by
  apply CharTwo.sq_injective
  have he := congrArg Matrix.det hA
  simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one,pow_two,one_mul] using he

variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form=1)
local notation "K₀" => FixedBy.subfield F J.conj

private def fixedEmbeddingGL : dotGroup K₀ →* GL (Fin 5) F :=
  (GeneralLinearGroup.map (FixedBy.subfield F J.conj).subtype).comp linearMatrix

include hJ in
private theorem fixedEmbedding_unitary (g : dotGroup K₀) :
    fixedEmbeddingGL J g ∈ J.specialSubgroup := by
  constructor
  · change J.conjTranspose ((linearMatrix g).val.map (FixedBy.subfield F J.conj).subtype) * J.form *
        (linearMatrix g).val.map (FixedBy.subfield F J.conj).subtype=J.form
    have hc : J.conjTranspose ((linearMatrix g).val.map (FixedBy.subfield F J.conj).subtype) =
        (linearMatrix g).val.transpose.map (FixedBy.subfield F J.conj).subtype := by
      ext i j
      exact ((linearMatrix g).val j i).property
    rw [hc,hJ,mul_one,←Matrix.map_mul,linearMatrix_orthogonal]
    exact map_one (FixedBy.subfield F J.conj).subtype.mapMatrix
  · apply Units.ext
    simp only [GeneralLinearGroup.val_det_apply,Units.val_one,fixedEmbeddingGL,
      MonoidHom.comp_apply]
    change (((FixedBy.subfield F J.conj).subtype.mapMatrix) (linearMatrix g).val).det=1
    rw [←RingHom.map_det,orthogonal_det _ (linearMatrix_orthogonal g),map_one]

/-- Fixed-field identity-bilinear isometries in the original SU coordinates. -/
private def dotToFixed : dotGroup K₀ →* (matrixAut J hJ).fixedSubgroup :=
  (((fixedEmbeddingGL J).codRestrict J.specialSubgroup (fixedEmbedding_unitary J hJ)).codRestrict
    (matrixAut J hJ).fixedSubgroup (fun g => by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      apply Subtype.ext
      apply Units.ext
      ext i j
      exact ((linearMatrix g).val i j).property))

private theorem dotToFixed_injective : Function.Injective (dotToFixed J hJ) := by
  intro g h he
  apply Subtype.ext
  apply linearEquivalence.symm.injective
  apply Units.ext
  ext i j
  exact congrArg (fun a : (matrixAut J hJ).fixedSubgroup => a.val.val.val i j) he

private theorem dotToFixed_surjective : Function.Surjective (dotToFixed J hJ) := by
  intro g
  have hfixed (i j : Fin 5) : J.conj (g.val.val.val i j)=g.val.val.val i j :=
    congrArg (fun a : J.specialSubgroup => a.val.val i j)
      ((MulAut.mem_fixedSubgroup _ _).mp g.property)
  let A : Matrix (Fin 5) (Fin 5) K₀ := fun i j => ⟨g.val.val.val i j,hfixed i j⟩
  have ha : A.transpose*A=1 := by
    apply Matrix.map_injective (FixedBy.subfield F J.conj).subtype.injective
    dsimp only
    rw [Matrix.map_mul]
    have hc : A.transpose.map (FixedBy.subfield F J.conj).subtype =
        J.conjTranspose g.val.val.val := by
      ext i j
      exact (hfixed j i).symm
    rw [hc,show (1 : Matrix (Fin 5) (Fin 5) K₀).map
      (FixedBy.subfield F J.conj).subtype=1 from
        map_one (FixedBy.subfield F J.conj).subtype.mapMatrix]
    change J.conjTranspose g.val.val.val*g.val.val.val=1
    have he := g.val.property.1
    change J.conjTranspose g.val.val.val * J.form * g.val.val.val=J.form at he
    simpa only [hJ,mul_one] using he
  let AGL : GL (Fin 5) K₀ := GeneralLinearGroup.mkOfDetNeZero A
    (by rw [orthogonal_det A ha]; exact one_ne_zero)
  have hl : linearEquivalence AGL ∈ dotGroup K₀ := by
    intro x y
    change dotProduct (A*ᵥx) (A*ᵥy)=dotProduct x y
    rw [Matrix.dotProduct_mulVec,Matrix.vecMul_mulVec,ha,Matrix.vecMul_one]
  refine ⟨⟨linearEquivalence AGL,hl⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have he : linearMatrix (⟨linearEquivalence AGL,hl⟩ : dotGroup K₀)=AGL :=
    linearEquivalence.symm_apply_apply AGL
  change (linearMatrix (⟨linearEquivalence AGL,hl⟩ : dotGroup K₀)).val.map (FixedBy.subfield F J.conj).subtype =
    g.val.val.val
  rw [he]
  rfl

/-- Exact fixed-field descent of the graph-fixed special unitary group. -/
private def dotFixedEquiv : dotGroup K₀ ≃* (matrixAut J hJ).fixedSubgroup :=
  MulEquiv.ofBijective (dotToFixed J hJ)
    ⟨dotToFixed_injective J hJ,dotToFixed_surjective J hJ⟩

/-- The actual graph-fixed SU₅ group is the actual symplectic matrix group
on the four-dimensional alternating complement over the fixed field. -/
def fixedMatrixSymplecticEquiv : (matrixAut J hJ).fixedSubgroup ≃*
    Matrix.PSp4Three.Sp 2 K₀ :=
  (dotFixedEquiv J hJ).symm.trans dotSymplecticEquiv

/-- Projective graph fixed points are Sp₄ over the stored fixed field;
the nontrivial scalar kernel is removed using the corrected fixed lift. -/
def fixedProjectiveSymplecticEquiv [Finite F] (hF : Nat.card F=16)
    (hconj : ∀ x, J.conj x=x^4) :
    (projectiveAut J hJ).fixedSubgroup ≃* Matrix.PSp4Three.Sp 2 K₀ :=
  (fixedProjectEquiv J hJ hconj hF).symm.trans (fixedMatrixSymplecticEquiv J hJ)

/-- Compatibility with the literal fixed SU-to-PSU projection. -/
theorem fixedProjectiveSymplecticEquiv_project [Finite F] (hF : Nat.card F=16)
    (hconj : ∀ x, J.conj x=x^4) (g : (matrixAut J hJ).fixedSubgroup) :
    fixedProjectiveSymplecticEquiv J hJ hF hconj (fixedProjectEquiv J hJ hconj hF g) =
      fixedMatrixSymplecticEquiv J hJ g := by
  simp [fixedProjectiveSymplecticEquiv]

end Theory.SpecificGroups.UnitaryFive.GraphFixed
