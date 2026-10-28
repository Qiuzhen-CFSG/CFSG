module

public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.RootCentralizer
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.GroupAction.CentralCoverTwoCentral
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The fixed residual of a central G₂ cover

A Sylow-fixing inner involution of the perfect cover descends to a genuine
two-central involution of the model. The native root-class theorem moves
it to a nonzero highest-root element. The full centralizer is the first
local group, which is perfect over fields larger than two. Central-kernel
fixed-residual transport therefore supplies a surjection from the original
embedded fixed residual onto that local group, with central two-kernel.

The covering group is arbitrary; its multiplier and center order are not
classified. Source: Aschbacher–Smith 1.1.5(3)(b), pp.501–503, and the
inspection in 14.7.68(2), p.1071; F.1.11–12, pp.262–264.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Atlas.G2.CoverFixedNaturalSections
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

theorem exists_fixedResidual_local_cover {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (hq : 2 < Nat.card F) (e : (A ⧸ pCore 2 A) ≃* Model F)
    (hZ : center A = pCore 2 A) (α : MulAut A)
    (hne : α ≠ 1) (hsq : α ^ 2 = 1)
    (hi : α ∈ (MulAut.conj (G := A)).range)
    (P : Sylow 2 A) (hP : ∀ x ∈ P, α x = x) :
    ∃ f : MulAut.embeddedFixedResidual 2 α →* local₁ (F := F),
      Function.Surjective f ∧ f.ker ≤ center (MulAut.embeddedFixedResidual 2 α) ∧
      IsPGroup 2 f.ker := by
  let eZ : (A ⧸ center A) ≃* Model F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans e
  have hz : center (Model F) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh := (centerCongr eZ.symm ⟨x,hx⟩).property
    change eZ.symm x ∈ center (A ⧸ center A) at hh
    rw [Group.IsPerfect.center_quotient_center_eq_bot A] at hh
    apply mem_bot.mpr
    apply eZ.symm.injective
    simpa only [map_one] using (mem_bot.mp hh)
  let f : A →* Model F := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hc : f.ker ≤ center A := by rw [hker, hZ]
  have hk : IsPGroup 2 f.ker := hker.symm ▸ pCore_isPGroup
  obtain ⟨t,ht,⟨Q,htQ,htcent⟩,heq⟩ :=
    MulAut.exists_twoCentral_model_of_central_cover f hf hc hz α hi
      (orderOf_eq_prime hsq hne) P hP
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htn : t ≠ 1 := by intro he; simp [he] at ht
  obtain ⟨g,a,ha,hroot⟩ := EvenInvolutionGeometry.central_involution_isLongRoot Q htQ ht2
    (fun y hy => (congrArg Subtype.val (mem_center_iff.mp htcent ⟨y,hy⟩)).symm) htn
  let f' : A →* Model F := (MulAut.conj g⁻¹).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g⁻¹).surjective.comp hf
  have hk' : f'.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g⁻¹).injective
  have hc' : f'.ker ≤ center A := hk'.symm ▸ hc
  have hp' : IsPGroup 2 f'.ker := hk'.symm ▸ hk
  have heq' (x : A) : f' (α x) = (MulAut.conj (rootA a)) (f' x) := by
    change (MulAut.conj g⁻¹) (f (α x)) = (MulAut.conj (rootA a)) ((MulAut.conj g⁻¹) (f x))
    rw [heq, hroot]
    simp only [MulAut.conj_apply]
    group
  have hfix : (MulAut.conj (rootA a)).fixedSubgroup = local₁ (F := F) :=
    (MulAut.fixedSubgroup_conj _).trans (centralizer_rootA_eq_local₁ ha)
  have hres : pResidual 2 (local₁ (F := F)) = ⊤ := by
    let : Group.IsNilpotent (local₁ (F := F) ⧸ pResidual 2 (local₁ (F := F))) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    have h := solvableResidual_le_of_solvable_quotient (pResidual 2 (local₁ (F := F)))
    rw [local₁_solvableResidual_eq_top hq] at h
    exact top_unique h
  let R := MulAut.embeddedFixedResidual 2 α
  have hm : R.map f' = local₁ (F := F) := by
    change ((pResidual 2 α.fixedSubgroup).map α.fixedSubgroup.subtype).map f' = _
    rw [MulAut.map_embedded_fixedResidual_of_central_pgroup_ker 2 α
      (MulAut.conj (rootA a)) f' hf' hc' hp' heq', hfix, hres,
      ← MonoidHom.range_eq_map, range_subtype]
  let r : R →* local₁ (F := F) := (f'.comp R.subtype).codRestrict local₁
    (fun x => hm ▸ mem_map_of_mem f' x.property)
  have hrs : Function.Surjective r := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hm.ge y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  have hrk : r.ker = f'.ker.subgroupOf R := by
    ext x
    change r x = 1 ↔ f' (x : A) = 1
    exact Subtype.ext_iff
  refine ⟨r, hrs, ?_, ?_⟩
  · intro x hx
    have hx' : (x : A) ∈ f'.ker := by rw [hrk] at hx; exact hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc' hx') y)
  · rw [hrk]
    exact hp'.comap_subtype
end Atlas.G2.CoverFixedNaturalSections
