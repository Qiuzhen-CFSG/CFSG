module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.Automorphisms
public import Theory.SpecificGroups.Tits.RelativeSylowMarking
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Innerness of automorphisms of the full binary Ree group

The native full Ree carrier is the automorphism group of the centerless
simple Tits group. The elementary automorphism-tower theorem therefore
makes every automorphism inner. Transporting that statement along an
actual subgroup equivalence supplies the normalizer step in J.5.3.

Source: Aschbacher–Smith J.5.3, printed p.445, and the full-Ree
identification in F.1.12, printed pp.263–264.
-/

public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee

/-- Innerness on any actual group identified with the full binary Ree carrier. -/
theorem inner_of_equiv {K:Type*} [Group K] (e:K≃*ReeF4.Model 0) (α:MulAut K) :
    ∃k:K,MulAut.conj k=α := by
  let f:K≃*MulAut Atlas1600Group:=e.trans atlasAutEquiv
  let β:MulAut (MulAut Atlas1600Group):=(f.symm.trans α).trans f
  obtain ⟨b,hb⟩:=MulAut.automorphismTower_inner_of_isSimpleGroup
    RelativeSylowMarking.atlas_center_eq_bot β
  refine ⟨f.symm b,?_⟩
  apply MulEquiv.ext
  intro x
  apply f.injective
  have hh:=DFunLike.congr_fun hb (f x)
  change b*f x*b⁻¹=f (α (f.symm (f x))) at hh
  rw [f.symm_apply_apply] at hh
  change f (f.symm b*x*(f.symm b)⁻¹)=f (α x)
  rw [map_mul,map_mul,map_inv,f.apply_symm_apply]
  exact hh

/-- Every automorphism of the native full binary Ree group is inner. -/
theorem automorphisms_inner (α:MulAut (ReeF4.Model 0)) :
    ∃g:ReeF4.Model 0,MulAut.conj g=α := inner_of_equiv (MulEquiv.refl _) α

end Tits.ExceptionalParabolics.FullRee
