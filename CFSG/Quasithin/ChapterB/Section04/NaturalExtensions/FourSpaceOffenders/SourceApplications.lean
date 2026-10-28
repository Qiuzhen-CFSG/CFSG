module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.CentralQuotient
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.NaturalSubmodule
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.ActorTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.CentralExtension
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Construction

/-!
# Full B.4.8(2)–(3) on the marked source actions

The natural quotient or submodule supplies the actor isomorphism. Reindex the
original representation along its inverse, apply the proved four-space
geometry, and transport every subgroup and fixed space back along that same
map. The quotient projection has the literal global fixed space as its kernel;
the natural submodule contains the literal commutator space.

These theorems discharge the universal `EarlierB48Two` and `EarlierB48Three`
inputs used by the B.5.9 seed-cover and B.5.6 exceptional-extension consumers.
All their offender, ratio, Sylow and involution conclusions are retained.

Source: Aschbacher–Smith, B.4.8(2)–(3), printed p.91 (1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers
namespace CFSG.Quasithin.ChapterB.NaturalExtensions
open BinaryLinearThree FourSpaceOffenders
universe u v

/-- The full central-quotient source implication, with the given actor marking. -/
theorem earlierB48Two : CentralExtension.EarlierB48Two.{u,v} := by
  intro D _ _ U _ _ _ σ _ hi hd e
  let j : D ≃* BinaryLinearThree.Group := e.groupEquiv
  let τ : Representation (ZMod 2) BinaryLinearThree.Group U :=
    σ.comp j.symm.toMonoidHom
  let p : τ.IntertwiningMap W :=
    (e.linearEquiv.toLinearMap.comp σ.invariants.mkQ).intertwiningMap_of_isIntertwiningMap τ W
      (by
        intro g v
        have h := e.intertwines (j.symm g) (σ.invariants.mkQ v)
        change e.linearEquiv (σ.invariants.mkQ (σ (j.symm g) v)) =
          W (j (j.symm g)) (e.linearEquiv (σ.invariants.mkQ v)) at h
        change e.linearEquiv (σ.invariants.mkQ (σ (j.symm g) v)) =
          W g (e.linearEquiv (σ.invariants.mkQ v))
        rw [j.apply_symm_apply] at h
        exact h)
  have hp : Function.Surjective p := e.linearEquiv.surjective.comp σ.invariants.mkQ_surjective
  have hk : p.toLinearMap.ker ≤ Representation.OneCohomology.fixed τ := by
    intro v hv g
    change e.linearEquiv (σ.invariants.mkQ v) = 0 at hv
    have hz : σ.invariants.mkQ v = 0 := e.linearEquiv.injective (by
      change e.linearEquiv (σ.invariants.mkQ v) = e.linearEquiv 0
      simpa only [map_zero] using hv)
    have hv' : v ∈ σ.invariants := by
      exact (Submodule.Quotient.mk_eq_zero _).mp hz
    exact hv' (j.symm g)
  have hind := reindex_indecomposable σ j.symm hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    have hb := reindex_best σ j.symm (A.map j.toMonoidHom)
    have hm : (A.map j.toMonoidHom).map j.symm.toMonoidHom = A := by
      rw [map_map]; simp
    rw [hm] at hb
    exact hb.symm.trans (central_best_iff_fullCenter τ p hp hk hind hd _)
  · rw [← reindex_ratio σ j.symm]
    exact central_quadraticRatio τ p hp hk hind hd
  · intro T
    have hs := central_quotient_sylow τ p hp hk hind hd
      (T.mapSurjective (f := j.toMonoidHom) j.surjective)
    change fixedSpace τ ((T : Subgroup D).map j.toMonoidHom) = τ.invariants at hs
    have hf := reindex_fixed σ j.symm ((T : Subgroup D).map j.toMonoidHom)
    have hc : ((T : Subgroup D).map j.toMonoidHom).map j.symm.toMonoidHom = T := by
      rw [map_map]; simp
    rw [hc] at hf
    rw [hf, show τ.invariants = σ.invariants from reindex_invariants σ j.symm] at hs
    exact hs
  · intro a ha
    have h := central_quotient_involutions τ p hp hk hind hd (j a)
      ((j.orderOf_eq a).trans ha)
    have hc : (zpowers (j a)).map j.symm.toMonoidHom = zpowers a := by
      rw [MonoidHom.map_zpowers]; simp
    have hf := reindex_fixed σ j.symm (zpowers (j a))
    have hm := reindex_moved σ j.symm (zpowers (j a))
    rw [hc] at hf hm
    change subspaceCommutator τ ⊤ (zpowers (j a)) = subspaceCommutator σ ⊤ (zpowers a) at hm
    change fixedSpace τ (zpowers (j a)) = fixedSpace σ (zpowers a) at hf
    rw [hm, hf] at h
    exact h

/-- The full commutator-submodule source implication, with the given actor marking. -/
theorem earlierB48Three : SourceInduction.ExceptionalExtension.EarlierB48Three.{u,v} := by
  intro D _ _ U _ _ _ σ _ hi hd N hN e
  let j : D ≃* BinaryLinearThree.Group := e.groupEquiv
  let τ : Representation (ZMod 2) BinaryLinearThree.Group U :=
    σ.comp j.symm.toMonoidHom
  let M : Subrepresentation τ :=
    { toSubmodule := N.toSubmodule
      apply_mem_toSubmodule g v hv := N.apply_mem_toSubmodule (j.symm g) hv }
  let f : Representation.Equiv M.toRepresentation W :=
    Representation.Equiv.mk e.linearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      have h := e.intertwines (j.symm g) v
      change e.linearEquiv (M.toRepresentation g v) = W (j (j.symm g)) (e.linearEquiv v) at h
      change e.linearEquiv (M.toRepresentation g v) = W g (e.linearEquiv v)
      rw [j.apply_symm_apply] at h
      exact h)
  have hm : Coinvariants.ker τ ≤ M.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change σ (j.symm g) v - v ∈ N.toSubmodule
    apply hN.ge
    exact Submodule.subset_span ⟨j.symm g, mem_top _, v, Submodule.mem_top, rfl⟩
  have hind := reindex_indecomposable σ j.symm hi
  refine ⟨?_, ?_, ?_⟩
  · intro A
    have hb := reindex_best σ j.symm (A.map j.toMonoidHom)
    have hmap : (A.map j.toMonoidHom).map j.symm.toMonoidHom = A := by
      rw [map_map]; simp
    rw [hmap] at hb
    exact hb.symm.trans (natural_best_iff_fullAxis τ M f hm hind hd _)
  · rw [← reindex_ratio σ j.symm]
    exact natural_quadraticRatio τ M f hm hind hd
  · intro a ha
    have h := natural_submodule_involutions τ M f hm hind hd (j a)
      ((j.orderOf_eq a).trans ha)
    have hc : (zpowers (j a)).map j.symm.toMonoidHom = zpowers a := by
      rw [MonoidHom.map_zpowers]; simp
    have hf := reindex_fixed σ j.symm (zpowers (j a))
    have hmov := reindex_moved σ j.symm (zpowers (j a))
    rw [hc] at hf hmov
    change subspaceCommutator τ ⊤ (zpowers (j a)) = subspaceCommutator σ ⊤ (zpowers a) at hmov
    change fixedSpace τ (zpowers (j a)) = fixedSpace σ (zpowers a) at hf
    rw [hmov, hf] at h
    exact h
end CFSG.Quasithin.ChapterB.NaturalExtensions
