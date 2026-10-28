module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# A trivial core action on a quasisimple image

An automorphism trivial modulo the original two-core induces the identity
on every equivariant quasisimple quotient. The two-core maps into the
central two-core of that image, and perfectness removes central displacement.
No centrality of the original two-core is assumed.

Source application: Aschbacher--Smith 6.1.4, the SL₂ centralizer block on p.666.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory

/-- Detect identity on the full quasisimple image through the original
surjection and actual quotient action. -/
theorem quasisimple_image_action_eq_one_of_twoCore_action
    {E B : Type*} [Group E] [Finite E] [Group B] [Finite B] [IsQuasisimple B]
    (f : E →* B) (hf : Function.Surjective f) (a : MulAut E) (b : MulAut B)
    (he : f.comp a.toMonoidHom = b.toMonoidHom.comp f)
    (ha : quotientAut (pCore 2 E) a = 1) : b = 1 := by
  have hcore : (pCore 2 E).map f ≤ pCore 2 B :=
    le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  apply MulAut.eq_one_of_central_displacement
  intro y
  obtain ⟨x,rfl⟩ := hf y
  have hx : x⁻¹ * a x ∈ pCore 2 E := by
    apply QuotientGroup.eq.mp
    have hh := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 E) x)
    rw [quotientAut_apply_mk] at hh
    exact hh.symm
  have hh := (hcore.trans (IsQuasisimple.pCore_le_center 2)) (mem_map_of_mem f hx)
  have he' : f (a x) = b (f x) := DFunLike.congr_fun he x
  simpa only [map_mul,map_inv,he'] using hh

end Theory.GroupTheory
