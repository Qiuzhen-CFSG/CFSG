module

public import Theory.GroupAction.FixedCentralizerRigidity
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupAction.CentralKernelFixedResidual
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Two-central fixed residuals through a perfect central cover

An inner involution fixing a Sylow two-subgroup descends faithfully through
a perfect cover whose kernel is the center. In the centerless quotient its
implementing element is a two-central involution. The original projection
maps the fixed-subgroup two-residual onto that involution-centralizer
residual, so the latter order divides the former. Central two-kernels are
retained; no splitting or full fixed-point lifting is assumed.

Applications: the M₁₂ and A₈ exclusions in the opposite-centralizer
recognition of Aschbacher--Smith 14.3.22, printed p.999.
-/

public section
open Subgroup
namespace PerfectCentralCovering
variable {E B : Type*} [Group E] [Group B] [Finite E]

theorem Cover.exists_twoCentral_fixedResidual_dvd (f : Cover E B)
    (hk : f.toMonoidHom.ker = center E) (hp : IsPGroup 2 f.toMonoidHom.ker)
    (hB : center B = ⊥) (α : MulAut E) (hα : orderOf α = 2)
    (hi : ∃ x, α = MulAut.conj x) (P : Sylow 2 E)
    (hfix : ∀ x : P, α (x : E) = x) :
    ∃ t : B, orderOf t = 2 ∧ Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral t ∧
      Nat.card (pResidual 2 (centralizer ({t} : Set B))) ∣
        Nat.card (pResidual 2 α.fixedSubgroup) := by
  let β := f.autMap hk α
  let Q := P.mapSurjective f.surjective
  have hβ : orderOf β = 2 :=
    (orderOf_injective (f.autMap hk) (f.autMap_injective hk) α).trans hα
  have hbi : ∃ x, β = MulAut.conj x := (f.autMap_inner_iff hk α).mpr hi
  have hbfix : ∀ x ∈ Q, β x = x := by
    rintro _ ⟨x,hx,rfl⟩
    rw [f.autMap_apply, hfix ⟨x,hx⟩]
  obtain ⟨t,ht,hto,he⟩ := MulAut.inner_involution_fixing_sylow_center hB Q β hβ hbi hbfix
  refine ⟨t,hto,⟨Q,t.property,ht⟩,?_⟩
  have hd := card_dvd_of_surjective
    (MulAut.fixedResidualMap 2 α β f.toMonoidHom
      (fun x => (f.autMap_apply hk α x).symm))
    (MulAut.fixedResidualMap_surjective 2 α β f.toMonoidHom f.surjective
      f.ker_le_center hp (fun x => (f.autMap_apply hk α x).symm))
  rwa [he, MulAut.fixedSubgroup_conj] at hd
end PerfectCentralCovering
