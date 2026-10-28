module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterMoved

/-!
# The fixed summand of the original local omega span

The original central Sylow seed generates U under H. Odd-index averaging
therefore writes U as [U,H] plus C_U(H). Since H=O²(H)T and T fixes the
seed, [U,H]=[U,O²(H)]. The fixed summand is exactly C_Z(O²(H)), with
Z=Ω₁Z(T). This identifies the fixed layers retained in 12.4.1's local action.
Source: Aschbacher–Smith B.2.14 and 12.4.1, printed pp.78,812.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

/-- Adjoining the Sylow supplement does not increase the moved subgroup. -/
theorem localModule_commutator_H_eq (hTH : (T : Subgroup G) ≤ H) :
    ⁅localModule T H,H⁆ = localMoved T H :=
  commutator_conjugateSpan_eq_of_fixed_supplement (sylowCenterSeed T) H H
    (localResidual H) (T : Subgroup G) ((sylowCenterSeed_le T).trans hTH)
    (map_subtype_le _) hTH H.le_normalizer (localResidual_normalized H)
    (map_subtype_le _) (localResidual_supplement hTH).symm.le (sylowCenterSeed_centralizes T)

/-- The fixed part of the whole omega span is the fixed part of the original seed. -/
theorem localModule_fixed_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    localModule T H ⊓ centralizer (H : Set G) =
      sylowCenterSeed T ⊓ centralizer (localResidual H : Set G) := by
  let := localModule_elementary h hH
  have hUT : localModule T H ≤ (T : Subgroup G) := by
    intro u hu
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)
      ((localModule_reduced h hH).le_pCore
        (show (⟨u,localModule_le hH.1.1.2 hu⟩ : H) ∈ (localModule T H).subgroupOf H from hu))
  apply le_antisymm
  · intro u hu
    refine ⟨?_,centralizer_le (map_subtype_le _) hu.2⟩
    rw [sylowCenterSeed_eq]
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hUT hu.1,centralizer_le hH.1.1.2 hu.2,
        elemPow_eq_one_of_isElementaryAbelian u hu.1⟩
  · intro z hz
    refine ⟨le_conjugateSpanBy _ _ hz.1,?_⟩
    have hc : H ≤ centralizer ({z} : Set G) := by
      rw [←localResidual_supplement hH.1.1.2]
      exact sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hz.2 k hk))
        (fun t ht => mem_centralizer_singleton_iff.mpr (sylowCenterSeed_centralizes T hz.1 t ht))
    exact fun a ha => mem_centralizer_singleton_iff.mp (hc ha)

/-- The full original U splits into its moved subgroup and the actual fixed seed. -/
theorem localModule_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    localModule T H = localMoved T H ⊔
      (sylowCenterSeed T ⊓ centralizer (localResidual H : Set G)) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let : IsElementaryAbelian 2 (conjugateSpanBy (sylowCenterSeed T) H) :=
    localModule_elementary h hH
  have he := conjugateSpan_split_of_sylow_fixed (T.subtype hTH)
    (show sylowCenterSeed T ≤ centralizer
      (((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype : Set G) by
      change sylowCenterSeed T ≤ centralizer
        (((T : Subgroup G).subgroupOf H).map H.subtype : Set G)
      rw [map_subgroupOf_eq_of_le hTH]
      exact sylowCenterSeed_centralizes T)
  change localModule T H = ⁅localModule T H,H⁆ ⊔
    (localModule T H ⊓ centralizer (H : Set G)) at he
  rwa [localModule_commutator_H_eq hH.1.1.2,localModule_fixed_eq h hH] at he
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
