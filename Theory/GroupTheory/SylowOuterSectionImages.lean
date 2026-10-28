module
public import Theory.GroupTheory.SylowOuterSimpleSections
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Theory.GroupTheory.SectionLift

/-!
# Actual simple sections under Sylow restriction

A nonsolvable simple section survives a solvable kernel as a subgroup
surjection in the image. Applied to the stabilizer of a Sylow subgroup in
the automorphism group, this retains the actual section in Aut(P), rather
than just its order. Sylow conjugacy supplies the surjection to Out(G).

This refines SylowOuterSimpleSections for the field-four Hermitian use of
Aschbacher--Smith 4.4.10--11, printed p.621.
-/
public noncomputable section
open Subgroup
open scoped Pointwise
namespace MulAut

/-- A solvable kernel preserves a nonsolvable simple section in the actual target. -/
theorem section_image_of_solvable_kernel
    {H R S : Type*} [Group H] [Group R] [Group S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (r : H →* R) [Group.IsSolvable r.ker]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    ∃ W : Subgroup R, ∃ g : W →* S, Function.Surjective g := by
  let m : Group.SolvableKernelModel H r.range :=
    ⟨r.ker,inferInstance,inferInstance,QuotientGroup.quotientKerEquivRange r⟩
  obtain ⟨W,g,hg⟩ := m.simple_section hS U f hf
  exact MonoidHom.exists_section_of_surjective_of_injective
    (MonoidHom.id r.range) Function.surjective_id r.range.subtype
    r.range.subtype_injective W g hg

/-- Sylow restriction preserves the literal simple section, with its full kernels. -/
theorem simple_outer_section_in_sylow_aut
    {G S : Type*} [Group G] [Finite G] [Group S] [IsSimpleGroup S]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G))]
    (hS : ¬ Group.IsSolvable S)
    (U : Subgroup (Outer G)) (f : U →* S) (hf : Function.Surjective f) :
    ∃ W : Subgroup (MulAut P), ∃ g : W →* S, Function.Surjective g := by
  let H := MulAction.stabilizer (MulAut G) (P : Subgroup G)
  let F := fixingSubgroup (MulAut G) (P : Set G)
  let r : H →* MulAut P :=
    { toFun := fun a => (a.val.subgroupMap (P : Subgroup G)).trans
        (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let i : r.ker →* F :=
    (H.subtype.comp r.ker.subtype).codRestrict F (by
      intro a
      apply (mem_fixingSubgroup_iff (MulAut G)).mpr
      intro x hx
      change (a.val.val : MulAut G) x = x
      exact congrArg (fun b : MulAut P => ((b ⟨x,hx⟩ : P) : G)) a.property)
  have hi : Function.Injective i := by
    intro a b hab
    have hab' : (a.val.val : MulAut G) = b.val.val :=
      congrArg (fun z : F => (z : MulAut G)) hab
    exact Subtype.ext (Subtype.ext hab')
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective hi
  let q := (QuotientGroup.mk' (innerSubgroup G)).comp H.subtype
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G (a • P) P
    have hm : MulAut.conj g * a ∈ H := by
      change (MulAut.conj g * a) • (P : Subgroup G) = (P : Subgroup G)
      rw [mul_smul]
      exact congrArg Sylow.toSubgroup hg
    refine ⟨⟨MulAut.conj g * a,hm⟩,?_⟩
    change QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g * a) = _
    have hi : QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rw [map_mul,hi,one_mul]
  exact section_image_of_solvable_kernel hS r (U.comap q)
    (f.comp (q.subgroupComap U))
    (hf.comp (q.subgroupComap_surjective_of_surjective U hq))

end MulAut
