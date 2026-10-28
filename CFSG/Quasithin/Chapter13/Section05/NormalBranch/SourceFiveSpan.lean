module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveModule
public import Theory.Representation.BinaryPermutation.GroupIrreducible

/-!
# The original line and commutator span the selected A₅ pair module

The exact five-point module restriction transfers irreducibility to
subgroups of the original V. The nontrivial original line therefore spans
V under K. The original seed V₃=[V,L₁], with L₁≤K, makes [V,K] nontrivial,
so [V,K]=V. Since the original two-core normalizes K and contains V,
this also proves V≤K. All maps retain the selected source pair.

This discharges the span field of the13.5.14 substitution. Its corrected
local Sylow and full G.2.4 hypothesis remain separate obligations.

Source: Aschbacher–Smith,13.5.14(3–4), printed p.919.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveSpan
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  {K : Subgroup G} (hK : K ≤ D.L) (a : alternatingGroup (Fin 6))
  (hi : (K.subgroupOf D.L).map (localMap d) =
    FivePair.five.map (MulAut.conj a.val).toMonoidHom)

include hK hi in
theorem invariant_subgroup (W : Subgroup G) (hWV : W ≤ D.V)
    (hn : K ≤ normalizer (W : Set G)) : W=⊥ ∨ W=D.V := by
  let ρ : K →* MulAut G := (MulAut.conj : G →* MulAut G).comp K.subtype
  have hMV : ∀k:K, ∀v∈D.V,ρ k v∈D.V := by
    intro k v hv
    exact (mem_normalizer_iff.mp (d.normalizes_V (mem_sup_left (hK k.property))) v).mp hv
  apply invariant_subgroup_of_fiveCore D.V ρ hMV (restrictedActor d hK a hi)
    (restrictedActor_surjective d hK a hi) (moduleEquiv d a) ?_ W hWV ?_
  · intro k v
    apply Multiplicative.toAdd.injective
    change SixFiveRestriction.conjugateModuleEquiv a.val (d.coordinate _).toAdd = _
    exact (congrArg (SixFiveRestriction.conjugateModuleEquiv a.val)
      (d.conjugation (inclusion hK k) v)).trans
        (SixFiveRestriction.conjugateModuleEquiv_equivariant a.val
          ⟨localMap d (inclusion hK k),hi ▸ mem_map_of_mem (localMap d) k.property⟩
          (d.coordinate v).toAdd)
  · intro k w hw
    exact (mem_normalizer_iff.mp (hn k.property) w).mp hw

include hK hi in
theorem point_span (h : D.Hypothesis) : conjugateSpanBy D.V₁ K=D.V := by
  have hle : conjugateSpanBy D.V₁ K ≤ D.V :=
    conjugateSpanBy_le (h.point_lt.le.trans h.plus_le)
      (hK.trans (le_sup_left.trans d.normalizes_V))
  rcases invariant_subgroup d hK a hi _ hle (le_normalizer_conjugateSpanBy D.V₁ K) with hz|he
  · have hp : D.V₁=⊥ := le_bot_iff.mp (hz ▸ le_conjugateSpanBy D.V₁ K)
    have hc := h.point_card
    rw [hp,card_bot] at hc
    contradiction
  · exact he

include hK hi in
theorem module_commutator (h : D.Hypothesis) (hL : D.L₁ ≤ K)
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) : ⁅D.V,K⁆=D.V := by
  have hnV : K ≤ normalizer (D.V : Set G) := hK.trans (le_sup_left.trans d.normalizes_V)
  have hle : ⁅D.V,K⁆ ≤ D.V := le_normalizer_iff_commutator_le_left.mp hnV
  have hn : K ≤ normalizer ((⁅D.V,K⁆ : Subgroup G) : Set G) :=
    normalizer_commutator_ge_right _ _
  rcases invariant_subgroup d hK a hi _ hle hn with hz|he
  · have hp : D.Vplus≤⊥ := hseed ▸ (commutator_mono le_rfl hL).trans_eq hz
    have hc := h.point_lt
    have he : D.Vplus=⊥ := le_bot_iff.mp hp
    rw [he] at hc
    exact (not_lt_bot hc).elim
  · exact he

include d in
theorem exists_original_spanning_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ g : D.L, g.val ∉ D.Gz ∧ NormalBranch.K D g.val ≤ D.L ∧
      D.L₁ ≤ NormalBranch.K D g.val ∧ IsPPerfect 2 (NormalBranch.K D g.val) ∧
      blockResidual D g.val = NormalBranch.K D g.val ∧
      conjugateSpanBy D.V₁ (NormalBranch.K D g.val) = D.V ∧
      ⁅D.V,NormalBranch.K D g.val⁆ = D.V ∧ D.V ≤ NormalBranch.K D g.val := by
  obtain ⟨a,g,hg,_,hK,hL,_,hp,hr,hi⟩ :=
    SourcePairResidual.exists_pair_with_local_residual d h e hseed hn hU
  have hc := module_commutator d hK a hi h hL hseed
  have hVQ : D.V ≤ D.LT.pCoreIn 2 := by
    simpa only [pCoreIn,map_subgroupOf_eq_of_le h.V_le_LT] using
      map_mono (f := D.LT.subtype) h.reduced.le_pCore
  have hv : D.V ≤ NormalBranch.K D g.val := by
    rw [←hc]
    exact le_normalizer_iff_commutator_le_right.mp
      (hVQ.trans (SourcePairResidual.twoCore_normalizes_pair h g))
  exact ⟨g,hg,hK,hL,hp,hr,point_span d hK a hi h,hc,hv⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveSpan
end
