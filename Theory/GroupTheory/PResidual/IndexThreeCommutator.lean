module
public import Theory.GroupTheory.Commutator.ResidualNormalGeneration
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# Residual commutators in an index-three Sylow overgroup

A Sylow-normalized two-subgroup outside the two-core normally generates
the two-residual. Indeed, its normal closure cannot lie in the Sylow
subgroup; index three then makes that closure a supplement. Residual
normal generation gives the full commutator equality, including the
original kernel. A nontrivial moved residual image also forces escape, even
when the full homomorphism kernel has odd order. Conversely, an actor inside the two-core cannot generate
the nontrivial residual by commutators.

Source application: Aschbacher–Smith 13.4.7(4), printed pp.902–903.
The application to the original J₁(T) is in FixedCoreSource.Amalgam.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow-normalized actor outside the two-core moves the full two-residual. -/
theorem residual_commutator_of_index_three
    (S : Sylow 2 G) (hi : (S : Subgroup G).index = 3)
    (R : Subgroup G) (hRS : R ≤ S)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (hR : ¬ R ≤ pCore 2 G) : ⁅pResidual 2 G,R⁆ = pResidual 2 G := by
  let N := normalClosure (R : Set G)
  have hNS : ¬ N ≤ (S : Subgroup G) := by
    intro hh
    exact hR ((show R ≤ N from le_normalClosure).trans
      (le_sSup ⟨inferInstance,S.isPGroup'.to_le hh⟩))
  have hgen : N ⊔ (S : Subgroup G) = ⊤ := by
    rcases (isCoatom_of_index_three (S : Subgroup G) hi).le_iff.mp
      (show (S : Subgroup G) ≤ N ⊔ (S : Subgroup G) from le_sup_right) with ht | hs
    · exact ht
    · exact (hNS (le_sup_left.trans hs.le)).elim
  have hKN : pResidual 2 G ≤ N :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N (S : Subgroup G)
      S.isPGroup' hgen⟩
  exact (eq_commutator_of_normalClosure_contains (pResidual 2 G) (S : Subgroup G) R
    (pResidual_sup_sylow_eq_top S) (isPPerfect_pResidual 2)
    (S.isPGroup'.to_le hRS) hSR hKN).symm

/-- The two-core is exactly the obstruction to residual commutator generation. -/
theorem residual_commutator_iff_of_index_three
    (S : Sylow 2 G) (hi : (S : Subgroup G).index = 3)
    (R : Subgroup G) (hRS : R ≤ S)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G)) :
    ⁅pResidual 2 G,R⁆ = pResidual 2 G ↔ ¬ R ≤ pCore 2 G := by
  refine ⟨?_,residual_commutator_of_index_three S hi R hRS hSR⟩
  intro he hR
  have hK : pResidual 2 G ≤ (S : Subgroup G) :=
    (he.symm.le.trans ((commutator_mono le_rfl hR).trans
      (commutator_le_right (pResidual 2 G) (pCore 2 G)))).trans
      (pCore_isPGroup.le_sylow_of_normal S)
  have htop : (S : Subgroup G) = ⊤ := by
    simpa only [sup_eq_right.mpr hK] using pResidual_sup_sylow_eq_top S
  rw [htop,index_top] at hi
  omega
/-- Nontrivial residual movement in any homomorphic image suffices at
index three. No prime-group hypothesis on the full kernel is needed. -/
theorem residual_commutator_of_nontrivial_image_of_index_three
    {F : Type*} [Group F]
    (S : Sylow 2 G) (hi : (S : Subgroup G).index = 3)
    (R : Subgroup G) (hRS : R ≤ S)
    (hSR : (S : Subgroup G) ≤ normalizer (R : Set G))
    (f : G →* F) (hne : (pResidual 2 G).map f ≠ ⊥)
    (hm : ⁅(pResidual 2 G).map f,R.map f⁆ = (pResidual 2 G).map f) :
    ⁅pResidual 2 G,R⁆ = pResidual 2 G := by
  apply residual_commutator_of_index_three S hi R hRS hSR
  intro hR
  have hb : (pResidual 2 G).map f ≤ (pCore 2 G).map f := by
    rw [←hm,←map_commutator]
    exact map_mono ((commutator_mono le_rfl hR).trans
      (commutator_le_right (pResidual 2 G) (pCore 2 G)))
  have hp : IsPPerfect 2 ((pResidual 2 G).map f) :=
    (isPPerfect_pResidual 2).of_surjective (f.subgroupMap (pResidual 2 G))
      (f.subgroupMap_surjective _)
  apply hne
  apply le_bot_iff.mp
  apply le_normal_of_isPPerfect_of_le_sup_pGroup ((pResidual 2 G).map f)
    ⊥ ((pCore 2 G).map f) hp (pCore_isPGroup.map f)
  simpa only [bot_sup_eq] using hb

end Subgroup
