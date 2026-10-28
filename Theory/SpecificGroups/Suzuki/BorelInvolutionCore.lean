module

public import Theory.SpecificGroups.Suzuki.RootOmega
public import BenderSuzuki.SE.InvolutionCore
public import Theory.PGroupCore

/-!
# The involution core and two-core of a Suzuki Borel

The root group is the normal Sylow two-subgroup of the concrete Borel.
Every Borel involution lies in that root group, so the ambient involution
core is exactly its first omega, the elementary center of order q.
The two-core is the entire root group, whose order is q².
The final transport lemmas retain the literal embedding and its Borel image.

Source: GLS, Volume 4, Chapter 4, Lemma 3.2(b,c), using the root
calculations of Huppert--Blackburn, Finite Groups III, XI.3.1 and XI.3.3.
-/

noncomputable section
open BenderSuzuki Subgroup PFAppendixIII
namespace BenderSuzuki.MatrixGroups

private theorem root_le_borel (m : ℕ) : SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m := by
  rw [suzukiBorelSubgroup_eq_sup]
  exact le_sup_left

public theorem suzukiBorel_root_isSylow (m : ℕ) (hm : 0 < m) :
    ∃ S : Sylow 2 (SuzukiBorelSubgroup m),
      (S : Subgroup (SuzukiBorelSubgroup m)) =
        (SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  refine ⟨P.subtype (hP ▸ root_le_borel m), ?_⟩
  rw [Sylow.coe_subtype, hP]

public theorem suzukiBorel_pCore (m : ℕ) (hm : 0 < m) :
    pCore 2 (SuzukiBorelSubgroup m) =
      (SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m) := by
  obtain ⟨S, hS⟩ := suzukiBorel_root_isSylow m hm
  have hn := suzukiRootSubgroup_normal_in_borel m
  have hp : IsPGroup 2 ((SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)) :=
    hS ▸ S.isPGroup'
  apply le_antisymm
  · rw [← hS]
    exact pCore_isPGroup.le_sylow_of_normal S
  · exact le_sSup ⟨hn, hp⟩

public theorem suzukiBorel_involutionCore_image (m : ℕ) (hm : 0 < m) :
    (involutionCore (SuzukiBorelSubgroup m)).map (SuzukiBorelSubgroup m).subtype =
      omegaOneAmbient (SuzukiRootSubgroup m) := by
  obtain ⟨S, hS⟩ := suzukiBorel_root_isSylow m hm
  have hn : (S : Subgroup (SuzukiBorelSubgroup m)).Normal :=
    hS ▸ suzukiRootSubgroup_normal_in_borel m
  let := hn
  apply le_antisymm
  · rw [map_le_iff_le_comap, involutionCore_eq_closure, closure_le]
    intro x hx
    have hxp := isPGroup_zpowers_of_involution hx
    have hxs : x ∈ (S : Subgroup (SuzukiBorelSubgroup m)) := by
      have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_left hxp) le_sup_left
      exact (sup_le_iff.mp he.le).2 (mem_zpowers x)
    have hxroot : (x : SuzukiMatrixGroup m) ∈ SuzukiRootSubgroup m := by
      rwa [hS] at hxs
    exact (omegaOneAmbient_le_iff (SuzukiRootSubgroup m) _).mp le_rfl (x : SuzukiMatrixGroup m) hxroot
      (congrArg Subtype.val (show x ^ 2 = 1 from hx.2))
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hsq
    by_cases hne : x = 1
    · exact hne ▸ one_mem _
    · have hxI : PFAppendixIII.IsInvolution
          (⟨x, root_le_borel m hx⟩ : SuzukiBorelSubgroup m) :=
        ⟨fun he => hne (congrArg Subtype.val he), Subtype.ext hsq⟩
      have hxC : (⟨x, root_le_borel m hx⟩ : SuzukiBorelSubgroup m) ∈
          involutionCore (SuzukiBorelSubgroup m) := by
        rw [involutionCore_eq_closure]
        exact subset_closure hxI
      exact ⟨⟨x, root_le_borel m hx⟩, hxC, rfl⟩

variable {G : Type*} [Group G] {m : ℕ}

public theorem suzukiBorel_involutionCore_map (hm : 0 < m) (f : SuzukiMatrixGroup m →* G)
    (hf : Function.Injective f) (B : Subgroup G)
    (hB : (SuzukiBorelSubgroup m).map f = B) :
    (involutionCore B).map B.subtype = (omegaOneAmbient (SuzukiRootSubgroup m)).map f := by
  let e : SuzukiBorelSubgroup m ≃* B :=
    ((SuzukiBorelSubgroup m).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hB)
  have he : B.subtype.comp e.toMonoidHom = f.comp (SuzukiBorelSubgroup m).subtype := by
    ext x
    rfl
  rw [← involutionCore_map_mulEquiv e, map_map, he, ← map_map, suzukiBorel_involutionCore_image m hm]

public theorem suzukiBorel_pCore_map (hm : 0 < m) (f : SuzukiMatrixGroup m →* G)
    (hf : Function.Injective f) (B : Subgroup G)
    (hB : (SuzukiBorelSubgroup m).map f = B) :
    (pCore 2 B).map B.subtype = (SuzukiRootSubgroup m).map f := by
  let e : SuzukiBorelSubgroup m ≃* B :=
    ((SuzukiBorelSubgroup m).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hB)
  have he : B.subtype.comp e.toMonoidHom = f.comp (SuzukiBorelSubgroup m).subtype := by
    ext x
    rfl
  rw [← pCore_map_iso 2 e, map_map, he, ← map_map, suzukiBorel_pCore m hm,
    Subgroup.map_subgroupOf_eq_of_le (root_le_borel m)]

public theorem suzukiBorel_pCore_isSylow_of_map [Finite G] (hm : 0 < m) (f : SuzukiMatrixGroup m →* G)
    (hf : Function.Injective f) (B : Subgroup G)
    (hB : (SuzukiBorelSubgroup m).map f = B) :
    ∃ S : Sylow 2 B, (S : Subgroup B) = pCore 2 B := by
  let e : SuzukiBorelSubgroup m ≃* B :=
    ((SuzukiBorelSubgroup m).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hB)
  obtain ⟨P, hP⟩ := suzukiBorel_root_isSylow m hm
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup (SuzukiBorelSubgroup m)).map e.toMonoidHom = _
  rw [hP, ← suzukiBorel_pCore m hm, pCore_map_iso]

end BenderSuzuki.MatrixGroups
