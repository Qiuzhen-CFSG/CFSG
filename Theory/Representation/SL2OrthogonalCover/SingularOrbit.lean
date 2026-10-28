module
public import Theory.Representation.SL2OrthogonalCover.FullFixed.Geometry
public import Theory.Representation.SL2OrthogonalCover.Sylow
public import Theory.SpecificGroups.SL2.Affine.Action
/-!
# Singular orbits and fixed-plane additivity in the orthogonal SL₂ cover

Projection identifies the singular vectors with the natural plane, giving
transitivity on nonzero singular vectors. Conjugating a Sylow subgroup to
the upper root group also shows that the quadratic form is additive on
its fixed plane. These calculations identify the original outside-center
factor with the singular line in the source 2.4.21 geometry.

Source: Aschbacher–Smith, I.2.3 and 2.4.21, printed pp.413 and 536.
-/
public section
namespace Representation.SL2OrthogonalCover
open Matrix Matrix.SpecialLinearGroup Representation.OneCohomology
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem singular_transitive (u v : Space F) (hu : form u=0) (hu0 : u≠0)
    (hv : form v=0) (hv0 : v≠0) : ∃ g : SL F, action g u=v := by
  have hp (w : Space F) (hw : form w=0) (hw0 : w≠0) : projection w≠0 := by
    intro he
    exact hw0 (FullFixed.singular_unique w 0 (by simpa using he) hw (map_zero _))
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq F (projection u) (projection v) (hp u hu hu0) (hp v hv hv0)
  refine ⟨g,FullFixed.singular_unique _ _ ?_ (by rw [form_invariant];exact hu) hv⟩
  rw [projection.isIntertwining]
  exact hg

theorem form_add_of_sylow_fixed (P : Sylow 2 (SL F)) (u v : Space F)
    (hu : u ∈ fixed (action.comp (P : Subgroup (SL F)).subtype))
    (hv : v ∈ fixed (action.comp (P : Subgroup (SL F)).subtype)) :
    form (u+v)=form u+form v := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL F) (upperUnipotentSylow F 2) P
  have hP : (P : Subgroup (SL F)) = (upperUnipotent F).map (MulAut.conj g).toMonoidHom := by
    rw [←hg];rfl
  have hroot (w : Space F) (hw : w ∈ fixed (action.comp (P : Subgroup (SL F)).subtype)) :
      action g⁻¹ w ∈ fixedPlane := by
    rw [←root_fixed]
    intro t
    have ht : (MulAut.conj g) t.val ∈ (P : Subgroup (SL F)) := by
      rw [hP];exact Subgroup.mem_map_of_mem _ t.property
    have hh := congrArg (action g⁻¹) (hw ⟨(MulAut.conj g) t.val,ht⟩)
    change action g⁻¹ (action ((MulAut.conj g) t.val) w)=action g⁻¹ w at hh
    change action t.val (action g⁻¹ w)=action g⁻¹ w
    rw [←Module.End.mul_apply,←map_mul] at hh ⊢
    simpa only [MulAut.conj_apply,mul_assoc,inv_mul_cancel_left] using hh
  have hu2 := (mem_fixedPlane _).mp (hroot u hu)
  have hv2 := (mem_fixedPlane _).mp (hroot v hv)
  calc
    form (u+v) = form (action g⁻¹ (u+v)) := (form_invariant _ _).symm
    _ = form (action g⁻¹ u)+form (action g⁻¹ v) := by
      rw [map_add]
      simp only [form_apply,Pi.add_apply,hu2,hv2,add_zero,mul_zero,CharTwo.add_sq]
    _ = form u+form v := by rw [form_invariant,form_invariant]
end Representation.SL2OrthogonalCover
