module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerPair

/-!
# The paired natural layers split the local two-core

The two original commuting A₅ blocks contribute complementary natural
layers.  This is the kernel decomposition used when assembling the two
restricted S₅ extensions into the Baumann direct product.
Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

@[expose] def SourceA5ZeroPairKernelSplit : Prop :=
  let H := localJoin T L
  ∃ t : H, (t : G) ∈ (T : Subgroup G) ∧
    let A := L.subgroupOf H
    let B := A.map (MulAut.conj t).toMonoidHom
    pCore 2 H = (blockU A).map A.subtype ⊔ (blockU B).map B.subtype

theorem source_a5_zero_pair_kernel_split
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    SourceA5ZeroPairKernelSplit (T := T) (L := L) := by
  let H := localJoin T L
  obtain ⟨t,ht,_,_,_,hsplit,_,_,_⟩ :=
    source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  exact ⟨t,ht,hsplit⟩

end CFSG.Quasithin.Chapter10
