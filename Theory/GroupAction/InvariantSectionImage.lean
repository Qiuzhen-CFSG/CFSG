module
public import Theory.GroupAction.HomomorphismFixedKernel
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PPerfectHom

/-!
# Prime-group images across an invariant section

If an action has prime-power image on the values of a homomorphism and
on its kernel, its image on the full finite group is a prime-group.
The prime residual acts trivially on both pieces. The automorphisms fixing
both pieces form a prime-group, so the residual acts trivially everywhere.

The kernel action may use a separately identified carrier; its fixing
condition retains that identification. This supplies the elementary
section argument behind Fong--Seitz I (6F), printed p.47, without requiring
semisimplicity of the full group action.
-/

public noncomputable section
open Subgroup
namespace MonoidHom
/-- A p-group action on a normal subgroup and its quotient gives a p-group
image on the full group. The homomorphism and both action squares are literal. -/
theorem isPGroup_range_of_kernel_and_quotient
    {A W V K : Type*} [Group A] [Finite A] [Group W] [Finite W] [Group V] [Group K]
    {p : ℕ} [Fact p.Prime] (q : W →* V) (hp : IsPGroup p q.ker)
    (f : A →* MulAut W) (g : A →* MulAut V) (k : A →* K)
    (hq : ∀ a w, q (f a w)=g a (q w))
    (hk : ∀ a, k a=1 → ∀ w : q.ker, f a w=w)
    (hg : IsPGroup p g.range) (hkp : IsPGroup p k.range) :
    IsPGroup p f.range := by
  let R := pResidual p A
  have hRg : R ≤ g.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using
      pResidual_le_ker_of_isPGroup p g.rangeRestrict hg
  have hRk : R ≤ k.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using
      pResidual_le_ker_of_isPGroup p k.rangeRestrict hkp
  let S := R.map f
  have hS : IsPGroup p S := by
    apply q.isPGroup_of_fixes_kernel_and_quotient hp S.subtype
    · rw [S.ker_subtype]
      exact IsPGroup.of_card (n:=0) (by simp)
    · intro s w
      obtain ⟨a,ha,he⟩ := s.property
      change q ((s : MulAut W) w)=q w
      rw [←he,hq,show g a=1 from hRg ha]
      rfl
    · intro s w
      obtain ⟨a,ha,he⟩ := s.property
      change (s : MulAut W) w=w
      rw [←he]
      exact hk a (hRk ha) w
  have hf : R ≤ f.ker := by
    have he := (isPPerfect_pResidual (G:=A) p).hom_eq_one_of_isPGroup hS (f.subgroupMap R)
    intro a ha
    exact congrArg (fun t : R →* S => (t ⟨a,ha⟩ : MulAut W)) he
  exact ((pResidual_le_iff_isPGroup_quotient p f.ker).mp hf).of_equiv
    (QuotientGroup.quotientKerEquivRange f)
end MonoidHom
