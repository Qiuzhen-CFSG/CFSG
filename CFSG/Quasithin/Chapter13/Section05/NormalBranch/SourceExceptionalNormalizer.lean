module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizerBound
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

/-!
# The source exceptional centralizer normalizes the original pair

Let C=C_T(K) have order two. The exact core splitting Q=V×C implies
that O₂(L) centralizes C. The marked A₅ image is a point stabilizer and
hence maximal in A₆. The identity C_T(L)=1 excludes the full image, so
C_L(C)=K O₂(L). Taking the two-residual recovers the original K. Since
C_T(C) normalizes this centralizer, it normalizes K as well.

This supplies the normalization needed for the literal assertion
K∈L(C_G(C),C_T(C)) in Aschbacher–Smith13.5.15, printed p.920. Its inputs
are the already proved original split and local-centralizer conclusion,
not a normalizer assumption about the selected A₅ subgroup.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalNormalizer
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem pair_actor_eq_stabilizer (g : D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    ((NormalBranch.K D g.val).subgroupOf D.L).map (SourceSixBlock.actor d)=
      MulAction.stabilizer (alternatingGroup (Fin 6)) (a.val 5) := by
  ext s
  constructor
  · rintro ⟨k,hk,rfl⟩
    have hm : (SourceSixBlock.actor d k).val∈
        FivePair.five.map (MulAut.conj a.val).toMonoidHom := hi ▸ mem_map_of_mem (localMap d) hk
    obtain ⟨w,hw,he⟩:=hm
    change (SourceSixBlock.actor d k).val (a.val 5)=a.val 5
    rw [←he]
    change a.val (w (a.val.symm (a.val 5)))=a.val 5
    rw [a.val.symm_apply_apply]
    exact congrArg a.val hw.1
  · intro hs
    have hm : s.val∈FivePair.five.map (MulAut.conj a.val).toMonoidHom := by
      refine ⟨(a⁻¹*s*a).val,⟨?_,(a⁻¹*s*a).property⟩,?_⟩
      · change a.val.symm (s.val (a.val 5))=5
        change s.val (a.val 5)=a.val 5 at hs
        rw [hs,a.val.symm_apply_apply]
      · change a.val*(a.val⁻¹*s.val*a.val)*a.val⁻¹=s.val
        group
    rw [←hi] at hm
    obtain ⟨k,hk,he⟩:=hm
    exact ⟨k,hk,Subtype.ext he⟩

theorem pair_actor_isCoatom (g : D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    IsCoatom (((NormalBranch.K D g.val).subgroupOf D.L).map (SourceSixBlock.actor d)) := by
  rw [pair_actor_eq_stabilizer d g a hi]
  let : MulAction.IsPreprimitive (alternatingGroup (Fin 6)) (Fin 6) :=
    alternatingGroup.isPreprimitive_of_three_le_card _ (by simp)
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ _

theorem exceptional_local_centralizer
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hsplit : D.LT.pCoreIn 2=D.V⊔((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)))
    (hCL : (D.T:Subgroup G)⊓centralizer (D.L:Set G)=⊥)
    (hcard : Nat.card ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)=2) :
    D.L⊓centralizer (((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G):Set G)=
      NormalBranch.K D g.val⊔D.L.pCoreIn 2 := by
  let K:=NormalBranch.K D g.val
  let C:=(D.T:Subgroup G)⊓centralizer (K:Set G)
  let X:=D.L⊓centralizer (C:Set G)
  let f:=SourceSixBlock.actor d
  have hKC : K≤centralizer (C:Set G) := le_centralizer_iff.mp inf_le_right
  have hVC : D.V≤centralizer (C:Set G) := (hS ▸ pCoreIn_le 2 K).trans hKC
  let : IsCyclic C := isCyclic_of_prime_card (p:=2) hcard
  have hQC : D.LT.pCoreIn 2≤centralizer (C:Set G) := by
    rw [hsplit]
    exact sup_le hVC C.le_centralizer
  have hPX : D.L.pCoreIn 2≤X :=
    le_inf (pCoreIn_le 2 D.L) ((SourcePairResidual.local_core_le_LT_core h).trans hQC)
  have hKX : K≤X := le_inf hK hKC
  have hker : f.ker≤X.subgroupOf D.L := by
    rw [SourceSixBlock.actor_ker d e]
    intro x hx
    exact hPX (mem_map_of_mem D.L.subtype hx)
  have himage : (X.subgroupOf D.L).map f=(K.subgroupOf D.L).map f := by
    rcases (pair_actor_isCoatom d g a hi).le_iff.mp
      (map_mono (show K.subgroupOf D.L≤X.subgroupOf D.L from subgroupOf_mono D.L hKX)) with ht|he
    · have hX : X.subgroupOf D.L=⊤ := by
        rw [←comap_map_eq_self hker,ht,comap_top]
      have hLC : D.L≤centralizer (C:Set G) := by
        intro x hx
        have hm : (⟨x,hx⟩:D.L)∈X.subgroupOf D.L := hX ▸ mem_top _
        exact hm.2
      have hC : C=⊥ := bot_unique ((le_inf inf_le_left (le_centralizer_iff.mp hLC)).trans hCL.le)
      have hc := hcard
      change Nat.card C=2 at hc
      rw [hC,card_bot] at hc
      contradiction
    · exact he
  have hX : X.subgroupOf D.L=K.subgroupOf D.L⊔f.ker := by
    rw [←comap_map_eq_self hker,himage,comap_map_eq]
  have hm:=congrArg (map D.L.subtype) hX
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show X≤D.L from inf_le_left),
    map_subgroupOf_eq_of_le hK,SourceSixBlock.actor_ker d e] at hm
  exact hm

/-- The intrinsic residual identity also applies to the full maximal-local
centralizer, which is needed after passing to the exceptional quotient. -/
theorem exceptional_local_centralizer_residual
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hsplit : D.LT.pCoreIn 2=D.V⊔((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)))
    (hCL : (D.T:Subgroup G)⊓centralizer (D.L:Set G)=⊥)
    (hcard : Nat.card ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)=2) :
    let X:=D.L⊓centralizer
      (((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G):Set G)
    (pResidual 2 X).map X.subtype=NormalBranch.K D g.val := by
  rw [exceptional_local_centralizer d h e g hK a hi hS hsplit hCL hcard]
  exact embedded_pResidual_join_pGroup (NormalBranch.K D g.val) (D.L.pCoreIn 2)
    hp (isPGroup_pCoreIn 2 D.L)
    ((SourcePairResidual.local_core_le_LT_core h).trans (SourcePairResidual.twoCore_normalizes_pair h g))

theorem exceptional_sylow_centralizer_normalizes_pair
    (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L)≃*alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L) (hp : IsPPerfect 2 (NormalBranch.K D g.val))
    (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V)
    (hsplit : D.LT.pCoreIn 2=D.V⊔((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G)))
    (hCL : (D.T:Subgroup G)⊓centralizer (D.L:Set G)=⊥)
    (hcard : Nat.card ((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G)=2) :
    (D.T:Subgroup G)⊓centralizer
      (((D.T:Subgroup G)⊓centralizer (NormalBranch.K D g.val:Set G):Subgroup G):Set G)≤
      normalizer (NormalBranch.K D g.val:Set G) := by
  let K:=NormalBranch.K D g.val
  let C:=(D.T:Subgroup G)⊓centralizer (K:Set G)
  let X:=D.L⊓centralizer (C:Set G)
  have hres:(pResidual 2 X).map X.subtype=K :=
    exceptional_local_centralizer_residual d h e g hK hp a hi hS hsplit hCL hcard
  have hn : (D.T:Subgroup G)⊓centralizer (C:Set G)≤normalizer (X:Set G) :=
    (le_inf (inf_le_left.trans d.normalizes_L)
      (inf_le_right.trans (centralizer (C:Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hh:=hn.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X))
  rwa [hres] at hh

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceExceptionalNormalizer
end

