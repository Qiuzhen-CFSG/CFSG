module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsFirstGeometry
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionFirstAlgebra

/-!
# The literal six labels in the first Mathieu endpoint

Change from the source's radius-two labels to the elementary-eight basis
used by the concrete model. The six-arc commutator calculation gives every
relation required by the first endpoint normalization theorem.

Source: Goldschmidt (1980), (6.12.6), printed p.405.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem conj_product (g x y : G) :
    g*(x*y)*g⁻¹=(g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem conj_fixed {g x : G} (hx : Commute g x) : g*x*g⁻¹=x := by
  rw [hx.eq,mul_assoc,mul_inv_cancel,mul_one]

/-- The source labels provide the exact model basis and conjugation relations. -/
theorem FirstGeometry.baseRelations {d : CanonicalLabelSetup F s}
    {a : Subgroup.CosetGeometry.RankTwo.Vertex F} {u v A B C : G}
    (R : FirstGeometry d a u v A B C) :
    FirstBaseRelations (d.label a*v) (u*v) A B C (d.label a) := by
  let z := d.label a
  have hzz : z*z=1 := by simpa only [pow_two] using R.z_sq
  have huu : u*u=1 := by simpa only [pow_two] using R.u_sq
  have hvv : v*v=1 := by simpa only [pow_two] using R.v_sq
  have hef : (z*v)*(u*v)=z*u := by
    rw [mul_assoc,← mul_assoc v,R.uv.symm.eq,mul_assoc u,hvv,mul_one]
  refine ⟨?_,?_,R.A_sq,R.B_sq,R.C_sq,R.z_sq,?_,?_,?_,R.zA,R.zB,R.zC,R.AC,
    ?_,?_,?_,?_,?_,?_⟩
  · rw [R.zv.mul_pow,R.z_sq,R.v_sq,mul_one]
  · rw [R.uv.mul_pow,R.u_sq,R.v_sq,mul_one]
  · exact (R.zu.mul_right R.zv).mul_left (R.uv.symm.mul_right (Commute.refl v))
  · exact (Commute.refl z).mul_right R.zv
  · exact R.zu.mul_right R.zv
  · rw [conj_product,conj_fixed R.zA.symm,R.Av,← mul_assoc,← mul_assoc,hzz,one_mul]
  · rw [conj_product,R.Au,R.Av,← mul_assoc,← mul_assoc,R.zu.symm.eq,
      mul_assoc z,huu,mul_one]
  · rw [conj_product,conj_fixed R.zB.symm,R.Bv]
  · rw [conj_product,R.Bu,R.Bv,mul_assoc (z*u),hvv,mul_one,hef]
  · rw [conj_product,conj_fixed R.zC.symm,R.Cv]
  · rw [conj_product,R.Cu,R.Cv,← mul_assoc,huu,one_mul,← mul_assoc,hzz,one_mul]

/-- The model's two basis vectors and central label generate the literal eight-group. -/
theorem FirstGeometry.radiusTwo_eq_closure_basis {d : CanonicalLabelSetup F s}
    {a : Subgroup.CosetGeometry.RankTwo.Vertex F} {u v A B C : G}
    (R : FirstGeometry d a u v A B C) :
    d.labelBall a 2 = closure ({d.label a*v,u*v,d.label a} : Set G) := by
  rw [R.generators]
  apply le_antisymm
  · apply (closure_le _).mpr
    let K := closure ({d.label a*v,u*v,d.label a} : Set G)
    have hz : d.label a ∈ K := subset_closure (by simp)
    have he : d.label a*v ∈ K := subset_closure (by simp)
    have hf : u*v ∈ K := subset_closure (by simp)
    have hv : v ∈ K := by
      simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem hz) he
    have hu : u ∈ K := by
      simpa only [mul_inv_cancel_right] using K.mul_mem hf (K.inv_mem hv)
    rintro x (rfl|rfl|rfl)
    · exact hz
    · exact hu
    · exact hv
  · apply (closure_le _).mpr
    let K := closure ({d.label a,u,v} : Set G)
    have hz : d.label a ∈ K := subset_closure (by simp)
    have hu : u ∈ K := subset_closure (by simp)
    have hv : v ∈ K := subset_closure (by simp)
    rintro x (rfl|rfl|rfl)
    · exact K.mul_mem hz hv
    · exact K.mul_mem hu hv
    · exact hz

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
