module
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Reducibility detected by a proper Sylow-fixed orbit span

In a finite family of complementary supports with cross-centralizing actors,
a two-group permutes any selected union of supports. If its fixed vectors lie
in a proper invariant subspace R, some missing support has an actor that moves
R. Otherwise the sum of missing supports is a stable complement to R and has
a nonzero fixed vector, contradicting the defining seed condition.

This gives the support-level reducibility step in Aschbacher--Smith 15.1.2,
printed p.1085, without assuming a transitive Sylow action on the supports.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.PermutedSupports
variable {G V ι : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Finite ι]
  (ρ : Representation (ZMod 2) G V)

theorem exists_missing_nonfixed_support
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (X : ι → Subgroup G) (U : ι → Submodule (ZMod 2) V)
    (hc : ∀ i, IsCompl (U i) (fixedSpace ρ (X i)))
    (hcross : ∀ i j, i ≠ j → U i ≤ fixedSpace ρ (X j))
    (O : Set ι) (W R : Submodule (ZMod 2) V)
    (hW : W = ⨆ j : O, U j.val)
    (hRS : S ≤ subspaceStabilizer ρ R)
    (hseed : fixedSpace ρ S ⊓ W ≤ R) (hproper : R < W)
    (hperm : ∀ s ∈ S, ∀ i ∈ O, ∃ j ∈ O, (U i).map (ρ s) = U j) :
    ∃ i ∈ O, ¬ U i ≤ R ∧ ¬ R ≤ fixedSpace ρ (X i) := by
  classical
  by_contra hnone
  have hn (i : ι) (hi : i ∈ O) (hnot : ¬ U i ≤ R) :
      R ≤ fixedSpace ρ (X i) := by
    by_contra hf
    exact hnone ⟨i,hi,hnot,hf⟩
  let J := {j : ι // j ∈ O ∧ ¬ U j ≤ R}
  let D : Submodule (ZMod 2) V := ⨆ j : J, U j.val
  have hDR : Disjoint D R := by
    have hcompl : IsCompl D (⨅ j : J, fixedSpace ρ (X j.val)) :=
      Submodule.isCompl_iSup_iInf_of_cross_le
        (fun j : J => U j.val) (fun j : J => fixedSpace ρ (X j.val))
        (fun j => hc j.val) (fun j k hjk => hcross j.val k.val
          (fun he => hjk (Subtype.ext he)))
    have hRf : R ≤ ⨅ j : J, fixedSpace ρ (X j.val) := by
      exact le_iInf fun j => hn j.val j.property.1 j.property.2
    exact hcompl.disjoint.mono_right hRf
  have hDW : D ≤ W := by
    rw [hW]
    exact iSup_le fun j => le_iSup (fun j : O => U j.val) ⟨j.val,j.property.1⟩
  have hDS : S ≤ subspaceStabilizer ρ D := by
    apply le_subspaceStabilizer
    intro s hs v hv
    change v ∈ ⨆ j : J, U j.val at hv
    refine Submodule.iSup_induction (fun j : J => U j.val)
      (motive := fun v => ρ s v ∈ D) hv ?_ ?_ ?_
    · intro j v hv
      obtain ⟨k,hk,he⟩ := hperm s hs j.val j.property.1
      have hkn : ¬ U k ≤ R := by
        intro hkR
        apply j.property.2
        intro w hw
        have hm := hkR (he ▸ Submodule.mem_map_of_mem (f := ρ s) hw)
        have hh := (hRS (S.inv_mem hs) (ρ s w)).2 hm
        simpa using hh
      exact (le_iSup (fun j : J => U j.val) ⟨k,hk,hkn⟩)
        (he ▸ Submodule.mem_map_of_mem (f := ρ s) hv)
    · simp
    · intro x y hx hy
      simpa only [map_add] using D.add_mem hx hy
  have hDne : D ≠ ⊥ := by
    intro hD
    apply (not_le_of_gt hproper)
    rw [hW]
    refine iSup_le fun j => ?_
    by_cases hj : U j.val ≤ R
    · exact hj
    · have hb := le_iSup (fun j : J => U j.val) ⟨j.val,j.property,hj⟩
      exact (hb.trans_eq hD).trans bot_le
  obtain ⟨v,hv,hv0,hvf⟩ := exists_nonzero_fixed ρ S hS D hDne hDS
  exact hv0 (Submodule.disjoint_def.mp hDR v hv (hseed ⟨hvf,hDW hv⟩))
end Representation.BinaryOffender.PermutedSupports
