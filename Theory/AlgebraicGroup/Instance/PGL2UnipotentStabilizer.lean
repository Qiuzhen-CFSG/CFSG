module

public import Theory.AlgebraicGroup.PGL2ProjectiveLine
import all Theory.AlgebraicGroup.Bor1.OppositePairPGL2OpenCell
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Triples
public import Theory.AlgebraicGroup.Unipotent.Basic
public import Theory.AlgebraicGroup.Tori.Semisimple
public import Theory.AlgebraicGroup.Jordan.Intersection
public import Theory.AlgebraicGroup.Dimension.Fiber
public import Theory.AlgebraicGroup.Unipotent.OneParameterCore
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected

/-!
# Unipotent point stabilizers in the actual PGL₂ model

A determinant-one triangular lift with distinct diagonal entries is conjugate
to the standard torus, hence semisimple. An algebraically unipotent element
fixing infinity is therefore a translation. This gives the dimension bound
for connected unipotent stabilizers and shows that a unipotent element fixing
two distinct projective-line points is trivial. The finite-kernel morphism
consumer supplies precisely the dimension estimate required in Borel §13.14.
The matrix argument applies in every characteristic and assumes no separability.
The internal import deliberately couples these concrete matrix proofs to the
existing root-matrix definitions; those bodies remain outside the public API.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem projection_surjective :
    Function.Surjective (pgl2SLPointProjection (k := k)) := by
  intro g
  let e := Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty
    (n := Fin 2) (F := k)
  obtain ⟨A,hA⟩ := QuotientGroup.mk_surjective (e (pgl2PointMulEquiv (k := k) g))
  refine ⟨A,?_⟩
  apply (pgl2PointMulEquiv (k := k)).injective
  rw [←pgl2SLPointProjection_class]
  have hh := congrArg e.symm hA
  change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) =
    e.symm (e (pgl2PointMulEquiv (k := k) g)) at hh
  simpa only [EquivLike.coe_coe, MulEquiv.symm_apply_apply] using hh

private theorem torusElement_semisimple (a : k) (ha : a ≠ 0) :
    IsSemisimpleElement (pgl2Variety (k := k)) (pgl2TorusElement a ha) := by
  rw [←pgl2StandardTorusMorphism_parameter]
  exact morphism_preserves_semisimpleElement _ _ ((dVariety_isTorus 1).all_semisimple _)

private theorem conjugate_semisimple
    {G : Variety k} [AlgebraicGroup G] (g x : Variety.Point G)
    (hx : IsSemisimpleElement G x) : IsSemisimpleElement G (g*x*g⁻¹) := by
  let f : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G g
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  exact morphism_preserves_semisimpleElement f x hx

private theorem diagonal_equal_projection_upper (A : PGL2SLPoint (k := k))
    (h10 : A.1 1 0=0) (he : A.1 0 0=A.1 1 1) :
    ∃b, pgl2SLPointProjection A=pgl2UpperRoot b := by
  have hdet : A.1 0 0*A.1 1 1=1 := by
    have hh := A.2
    rw [Matrix.det_fin_two,h10,mul_zero,sub_zero] at hh
    exact hh
  have hd : A.1 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  refine ⟨A.1 0 1 / A.1 1 1,?_⟩
  apply (pgl2PointMulEquiv (k := k)).injective
  rw [pgl2UpperRoot_eq,←pgl2SLPointProjection_class,←pgl2SLPointProjection_class]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (A.1 1 1)⁻¹ (inv_ne_zero hd),?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.toGL,pgl2UpperRootMatrix,
      Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_diagonal,
      he,hd,h10,div_eq_mul_inv]

private theorem triangular_distinct_conjugate (A : PGL2SLPoint (k := k))
    (h10 : A.1 1 0=0) (he : A.1 0 0 ≠ A.1 1 1) :
    ∃ (a c : k) (ha:a≠0), pgl2SLPointProjection A=
      pgl2UpperRoot c*pgl2TorusElement a ha*(pgl2UpperRoot c)⁻¹ := by
  have hdet : A.1 0 0*A.1 1 1=1 := by
    have hh := A.2
    rw [Matrix.det_fin_two,h10,mul_zero,sub_zero] at hh
    exact hh
  have ha : A.1 0 0≠0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : A.1 1 1=(A.1 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  let c := A.1 0 1/(A.1 1 1-A.1 0 0)
  have hc : A.1 1 1-A.1 0 0≠0 := sub_ne_zero.mpr he.symm
  refine ⟨A.1 0 0,c,ha,?_⟩
  rw [pgl2UpperRoot_eq,pgl2TorusElement_eq,←map_inv,←map_mul,←map_mul]
  congr 1
  rw [pgl2TorusMatrix_eq_diag2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pgl2UpperRootMatrix,Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.diag2_coe',Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,h10,←h11]
  dsimp [c]
  field_simp [hc]
  ring

theorem unipotent_fixing_infinity_is_upperRoot
    (g : Variety.Point (pgl2Variety (k := k)))
    (hg : g∈pgl2InfinityStabilizer (k := k))
    (hu : IsUnipotentElement (pgl2Variety (k := k)) g) :
    ∃b:k,g=pgl2UpperRoot b := by
  obtain ⟨A,rfl⟩ := projection_surjective g
  have h10 : A.1 1 0=0 := (mem_pgl2InfinityStabilizer_iff _ _ (pgl2SLPointProjection_class A)).mp hg
  by_cases he : A.1 0 0=A.1 1 1
  · exact diagonal_equal_projection_upper A h10 he
  · obtain ⟨a,c,ha,hconj⟩ := triangular_distinct_conjugate A h10 he
    have hs : IsSemisimpleElement (pgl2Variety (k := k)) (pgl2SLPointProjection A) :=
      hconj ▸ conjugate_semisimple _ _ (torusElement_semisimple a ha)
    have hone := semisimple_unipotent_eq_one _ hs hu
    refine ⟨0,hone.trans ?_⟩
    rw [pgl2UpperRoot_eq]
    simp [pgl2UpperRootMatrix]

theorem unipotent_fixing_zero_and_infinity_eq_one
    (g : Variety.Point (pgl2Variety (k := k)))
    (hi : g∈pgl2InfinityStabilizer (k := k))
    (hz : g∈pgl2ZeroStabilizer (k := k))
    (hu : IsUnipotentElement (pgl2Variety (k := k)) g) : g=1 := by
  obtain ⟨b,rfl⟩ := unipotent_fixing_infinity_is_upperRoot g hi hu
  have hrep := pgl2SLPointProjection_class (pgl2UpperRootMatrix (k := k) b)
  rw [←pgl2UpperRoot_eq] at hrep
  have hb := (mem_pgl2ZeroStabilizer_iff _ _ hrep).mp hz
  have hb0 : b=0 := by simpa [pgl2UpperRootMatrix,Matrix.SpecialLinearGroup.transvection_coe] using hb
  subst b
  rw [pgl2UpperRoot_eq]
  simp [pgl2UpperRootMatrix]

theorem unipotent_stabilizer_dimension_le_one
    (U : ClosedSubgroup (pgl2Variety (k := k)))
    (hUc : _root_.IsConnected (U : Set (Variety.Point (pgl2Variety (k := k)))))
    (hUu : @IsUnipotentAlgebraicGroup k _ U.carrierVariety U.carrierAlgebraicGroup)
    (hUi : U.toSubgroup ≤ pgl2InfinityStabilizer (k := k)) :
    Variety.dimension U.carrierVariety ≤ 1 := by
  let : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
  have hle : U ≤ pgl2UpperUnipotentClosed (k := k) := by
    intro g hg
    let u := U.pointEquiv.symm ⟨g,hg⟩
    have hu := morphism_preserves_unipotentElement U.inclusion u (hUu u)
    have hu' : IsUnipotentElement (pgl2Variety (k := k)) g := by
      have he : U.inclusion.onPoints u=g := congrArg Subtype.val (U.pointEquiv.apply_symm_apply ⟨g,hg⟩)
      rwa [he] at hu
    obtain ⟨b,rfl⟩ := unipotent_fixing_infinity_is_upperRoot g (hUi hg) hu'
    exact ⟨kPlusPoint b,rfl⟩
  apply le_trans (connected_closedSubgroup_dimension_le_of_le U _ hUc hle)
  have hd := morphism_dimension_eq_kernel_add_image (pgl2UpperUnipotentMorphism (k := k))
  rw [kPlus_dimension_eq_one] at hd
  change Variety.dimension (pgl2UpperUnipotentMorphism (k := k)).imageClosedSubgroup.carrierVariety ≤ 1
  rw [hd]
  exact self_le_add_left _ _


theorem finite_kernel_unipotent_pgl2_morphism_dimension_le_one
    {V : Variety k} [AlgebraicGroup V] (hVc : Variety.IsConnected V)
    (hVu : IsUnipotentAlgebraicGroup V)
    (f : AlgebraicGroup.Morphism V (pgl2Variety (k := k)))
    (hker : Finite (Variety.Point f.kernelClosedSubgroup.carrierVariety))
    (hfix : ∀ v, f.onPoints v ∈ pgl2InfinityStabilizer (k := k)) :
    Variety.dimension V ≤ 1 := by
  let I := f.imageClosedSubgroup
  let : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let fi := f.codRestrictClosedSubgroup I (fun v => ⟨v,rfl⟩)
  have hfi : Function.Surjective fi.onPoints :=
    f.codRestrictImageClosedSubgroup_surjective _
  have hIu : IsUnipotentAlgebraicGroup I.carrierVariety := hVu.of_surjective fi hfi
  have hIc := f.imageClosedSubgroup_isConnected hVc
  have hIi : I.toSubgroup ≤ pgl2InfinityStabilizer (k := k) := by
    rintro _ ⟨v,rfl⟩
    exact hfix v
  have hd := unipotent_stabilizer_dimension_le_one I hIc hIu hIi
  have he := morphism_dimension_eq_kernel_add_image f
  rw [(dimension_zero_iff_finite_points _).mpr hker,zero_add] at he
  exact he.trans_le hd

private def pgl2Conjugation (g : Variety.Point (pgl2Variety (k := k))) :
    AlgebraicGroup.Morphism (pgl2Variety (k := k)) (pgl2Variety (k := k)) where
  toVariety := AlgebraicGroup.conjugationByMorphism _ g
  map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
  map_mul := by
    intro x y
    simp only [AlgebraicGroup.conjugationByMorphism_apply]
    group

private lemma exists_pgl2_pair (p q : Point (projectiveLine k)) (hpq : p≠q) :
    let := pgl2ProjectiveLinePointMulAction (k := k)
    ∃g : Variety.Point (pgl2Variety (k := k)),
      g • projectiveLineInfinity = p ∧ g • projectiveLineZero = q := by
  classical
  let := pgl2ProjectiveLinePointMulAction (k := k)
  let : Infinite (Point (projectiveLine k)) :=
    Infinite.of_injective _ ProjectiveLineAutomorphisms.projectiveLineAffinePoint_injective
  obtain ⟨r,hr⟩ := Infinite.exists_notMem_finset ({p,q} : Finset (Point (projectiveLine k)))
  have hrp : r≠p := fun hh => hr (by simp [hh])
  have hrq : r≠q := fun hh => hr (by simp [hh])
  obtain ⟨g,hg0,_,hgi⟩ := ProjectiveLineAutomorphisms.exists_pgl2_of_distinct_points q r p hrq hrp.symm hpq
  exact ⟨g,hgi,hg0⟩

theorem unipotent_two_fixed_points_eq_one
    (g : Variety.Point (pgl2Variety (k := k)))
    (hu : IsUnipotentElement (pgl2Variety (k := k)) g)
    (p q : Point (projectiveLine k)) (hpq : p≠q)
    (hp : (pgl2ProjectiveLinePointMulAction (k := k)).smul g p=p)
    (hq : (pgl2ProjectiveLinePointMulAction (k := k)).smul g q=q) : g=1 := by
  let := pgl2ProjectiveLinePointMulAction (k := k)
  change g • p=p at hp
  change g • q=q at hq
  obtain ⟨a,hai,ha0⟩ := exists_pgl2_pair p q hpq
  have hu' := morphism_preserves_unipotentElement (pgl2Conjugation a⁻¹) g hu
  change IsUnipotentElement (pgl2Variety (k := k)) (a⁻¹*g*(a⁻¹)⁻¹) at hu'
  rw [inv_inv] at hu'
  have hi : a⁻¹*g*a ∈ pgl2InfinityStabilizer (k := k) := by
    change (a⁻¹*g*a) • projectiveLineInfinity = projectiveLineInfinity
    simp only [mul_smul,hai,hp]
    rw [←hai,inv_smul_smul]
  have hz : a⁻¹*g*a ∈ pgl2ZeroStabilizer (k := k) := by
    change (a⁻¹*g*a) • projectiveLineZero = projectiveLineZero
    simp only [mul_smul,ha0,hq]
    rw [←ha0,inv_smul_smul]
  have hone := unipotent_fixing_zero_and_infinity_eq_one _ hi hz hu'
  have h := congrArg (fun z => a*z*a⁻¹) hone
  simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_one,mul_inv_cancel] using h


theorem finite_kernel_unipotent_pgl2_point_fixer_dimension_le_one
    {V : Variety k} [AlgebraicGroup V] (hVc : Variety.IsConnected V)
    (hVu : IsUnipotentAlgebraicGroup V)
    (f : AlgebraicGroup.Morphism V (pgl2Variety (k := k)))
    (hker : Finite (Variety.Point f.kernelClosedSubgroup.carrierVariety))
    (p : Point (projectiveLine k))
    (hfix : ∀ v, (pgl2ProjectiveLinePointMulAction (k := k)).smul (f.onPoints v) p=p) :
    Variety.dimension V ≤ 1 := by
  let := pgl2ProjectiveLinePointMulAction (k := k)
  let : Infinite (Point (projectiveLine k)) :=
    Infinite.of_injective _ ProjectiveLineAutomorphisms.projectiveLineAffinePoint_injective
  change ∀ v, f.onPoints v • p=p at hfix
  obtain ⟨q,hq⟩ := exists_ne p
  obtain ⟨a,hai,_⟩ := exists_pgl2_pair p q hq.symm
  let f' := (pgl2Conjugation a⁻¹).comp f
  have hf' (v) : f'.onPoints v=a⁻¹*f.onPoints v*a := by
    change a⁻¹*f.onPoints v*(a⁻¹)⁻¹=_
    rw [inv_inv]
  have hk : f'.kernelClosedSubgroup=f.kernelClosedSubgroup := by
    apply SetLike.coe_injective
    ext v
    change (f'.onPoints v=1) ↔ (f.onPoints v=1)
    rw [hf']
    constructor
    · intro hh
      have h := congrArg (fun z => a*z*a⁻¹) hh
      simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_one,mul_inv_cancel] using h
    · intro hh
      rw [hh,mul_one,inv_mul_cancel]
  have hfker : Finite (Variety.Point f'.kernelClosedSubgroup.carrierVariety) := hk.symm ▸ hker
  apply finite_kernel_unipotent_pgl2_morphism_dimension_le_one hVc hVu f' hfker
  intro v
  change f'.onPoints v • projectiveLineInfinity = projectiveLineInfinity
  rw [hf']
  simp only [mul_smul,hai,hfix]
  rw [←hai,inv_smul_smul]

end Theory.AlgebraicGroup.Variety.Geometric
