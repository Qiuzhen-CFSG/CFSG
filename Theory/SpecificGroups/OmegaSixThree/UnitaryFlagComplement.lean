module
public import Theory.SpecificGroups.OmegaSixThree.UnitaryFlagImages
open Subgroup
/-!
# The marked independent local S₄ factor

The three corrected and twisted unitary matrices act as transpositions along
a spanning path on the second tetrahedron. Conjugating the standard adjacent
generators by the fixed label permutation shows that they generate the entire
independent complement, with the original ambient inclusion retained.

Source: Aschbacher–Smith F.5.7, printed p.303.
-/
@[expose] public noncomputable section
namespace OmegaSixThree.VertexComparison.FlagWords
open TriangleLocal

def complementParam : Four →* H :=
  productEquiv.symm.toMonoidHom.comp
    ((MonoidHom.inr Four Four).comp (MulAut.conj delta).toMonoidHom)

theorem complementParam_image (p : Four) :
    productEquiv (complementParam p) = (1,delta*p*delta⁻¹) :=
  productEquiv.apply_symm_apply _

theorem complementParam_range : complementParam.range = complementFactor := by
  apply le_antisymm
  · rintro _ ⟨p,rfl⟩
    change productEquiv (complementParam p) ∈ (⊥ : Subgroup Four).prod ⊤
    rw [complementParam_image]
    exact ⟨rfl,mem_top _⟩
  · intro g hg
    refine ⟨(MulAut.conj delta).symm (productEquiv g).2,?_⟩
    apply productEquiv.injective
    rw [complementParam_image]
    apply Prod.ext
    · exact hg.1.symm
    · exact (MulAut.conj delta).apply_symm_apply _

theorem complementParam_adjacent (k : Fin 3) :
    complementParam (Equiv.swap k.castSucc k.succ) = complementElement k := by
  apply productEquiv.injective
  rw [complementParam_image,complementElement_image]
  apply congrArg (fun p : Four => (1,p))
  revert k
  decide +kernel

/-- The three twisted source generators generate exactly the independent
second S₄ factor in the literal triangle group. -/
theorem complementElement_generate : closure (Set.range complementElement) = complementFactor := by
  rw [←complementParam_range]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨k,rfl⟩
    exact ⟨Equiv.swap k.castSucc k.succ,complementParam_adjacent k⟩
  · rintro _ ⟨p,rfl⟩
    let K := (closure (Set.range complementElement)).comap complementParam
    have ht : K = ⊤ := by
      apply Subgroup.toSubmonoid_injective
      apply top_unique
      rw [←Equiv.Perm.mclosure_swap_castSucc_succ 3]
      apply Submonoid.closure_le.mpr
      rintro _ ⟨k,rfl⟩
      change (Equiv.swap k.castSucc k.succ) ∈ K
      change complementParam (Equiv.swap k.castSucc k.succ) ∈ closure (Set.range complementElement)
      rw [complementParam_adjacent]
      exact subset_closure ⟨k,rfl⟩
    exact (show p ∈ K by rw [ht]; exact mem_top p)

/-- The identical statement in the original ambient Omega carrier. -/
theorem complementGenerator_generate : closure (Set.range complementGenerator) =
    complementFactor.map H.subtype := by
  rw [←complementElement_generate,MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨complementElement k,⟨k,rfl⟩,rfl⟩
  · rintro ⟨h,⟨k,rfl⟩,rfl⟩
    exact ⟨k,rfl⟩

end OmegaSixThree.VertexComparison.FlagWords
