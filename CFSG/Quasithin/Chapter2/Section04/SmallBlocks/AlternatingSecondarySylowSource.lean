module

public import Theory.GroupTheory.IndexTwoCentralizerUniqueness
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingMarkedSylowSource

/-!
# The secondary involution centralizer in the single alternating-five case

The marked natural-module involution has an index-two centralizer in the
ambient Sylow subgroup. Once its finite marked calculation identifies that
centralizer with its centralizer in M, two-local uniqueness controls its
normalizer and promotes it to Sylow in the ambient involution centralizer.
The original center of the Borel residual core lies in the Sylow center,
so centralizer orders exclude fusion of u into that center.

Source: Aschbacher–Smith (2.4.29), printed p.545. The marked finite
centralizer equality and index are retained for their independent producer.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_secondary_sylow_of_marked_centralizer
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (u : G) (hu2 : orderOf u = 2) (huT : u ∈ (T : Subgroup G))
    (hMu : M ⊓ centralizer ({u} : Set G) = (T : Subgroup G) ⊓ centralizer ({u} : Set G))
    (hi : ((T : Subgroup G) ⊓ centralizer ({u} : Set G)).relIndex (T : Subgroup G) = 2) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
    normalizer (Tu : Set G) ≤ M ∧
      (∃ S : Sylow 2 (centralizer ({u} : Set G)),
        (S : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype = Tu) ∧
      ∀ z ∈ (center P).map P.subtype, ¬ IsConj u z := by
  obtain ⟨hn,hs,hsep⟩ := secondary_centralizer_sylow_of_index_two T hu u hu2 huT hMu hi
  refine ⟨hn,hs,?_⟩
  intro z hz
  apply hsep z
  have hc := (d.single_alternating_sylow_geometry hG T hM hTM hu hST hsingle hA).2.1 hz
  obtain ⟨w,hw,hwz⟩ := hc
  intro t ht
  simp only [mem_centralizer_singleton_iff]
  rw [←hwz]
  exact congrArg Subtype.val ((mem_center_iff.mp hw) ⟨t,ht⟩)
end CFSG.Quasithin.Chapter2
