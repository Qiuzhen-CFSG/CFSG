module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixImages
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixFixed

/-!
# Fixed spaces for the actual ordinary A₇ replacement

Keep the natural-module comparison in the same source Thompson marking.
Functoriality maps Lᵥ onto the even pair-normalizer residual, whose cubic
permutations connect all six moved letters. Every replacement element
fixes the remaining letter, so its fixed space equals that of Lᵥ on W_K.
The constructed replacement retains its original Y_z membership.

Source: Aschbacher–Smith, Lemma 13.6.22, printed pp.932–933.
-/

public section
open scoped IsMulCommutative
open Subgroup Equiv Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open AlternatingBranches.OrdinarySeven SourcePlacement Marking ModuleComparison LocalResidual
variable {G : Type*} [Group G] [Finite G]

/-- Construct the source replacement and its full fixed-centralizer comparison
on the original elementary module, without a new block assumption. -/
theorem exists_replacement_with_fixed_comparison
    (K L T M S : Subgroup G) (z v : G)
    (hblock : ChapterC.IsAlternatingBlock K 7)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hS : S = ChapterB.baumann (Tv T v))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hUK : ⁅WK K L T z v, K⁆ =
      ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆)
    (hLM : Lv L v ≤ Mv M v) (hLn : ((Lv L v).subgroupOf (Mv M v)).Normal)
    (h65 : Gv v ⊓ normalizer (S : Set G) ≤ Mv M v)
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card (plusImage K L T z v hL hz (Lv L v)) →
      p = 2 ∨ p = 3)
    (P3 : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) (hP3 : Nat.card P3 = 3)
    (hzL : ⁅zpowers z, Lv L v⁆ ≠ ⊥) :
    ∃ e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      Lv L v ≤ replacement K e 6 ∧ replacement K e 6 ≤ K ∧
      Tv T v ≤ normalizer (replacement K e 6 : Set G) ∧
      replacement K e 6 ∈ Yz L T z v ∧
      WK K L T z v ⊓ centralizer (Lv L v : Set G) =
        WK K L T z v ⊓ centralizer (replacement K e 6 : Set G) := by
  obtain ⟨e, φ, hi, hc, hJ, hSJ, hcodim⟩ := exists_marking_with_comparison
    K L T S z v hL hz hK hLK hY hS hWT hR hblock hUK
  have hres := source_residual_eq K L T M S z v hblock hL hz hY hK hLK hS
    hLM hLn h65 e φ hi hc hJ hSJ h23 P3 hP3
  obtain ⟨hN, hT, hactor⟩ := placements_and_actor_of_plus_marking
    K L T S z v hL hz hK hS e φ hc hJ hSJ
  obtain ⟨hLB, hBK, hBn, _, _⟩ := replacement_spec K e 6 L T S z v hres hN hT hzL
  have hB := replacement_mem_Yz K L T S z v e 6 hY hres hN hT hzL hactor
  have hDimage := local_image_eq_residual K L T S z v hL hz hY hK hLK hS
    e φ hi hc hJ hSJ hres
  have hBimage := replacement_image_le_stabilizer K L T z v hL hz e φ hc
  refine ⟨e, hLB, hBK, hBn, hB, ?_⟩
  apply centralizer_eq_of_natural_fixedSpace K L T (replacement K e 6) z v
    hL hz hWT hLB hBK φ hcodim
  apply le_antisymm
  · intro w hw b
    apply SixFixed.natural_fixed_of_fix_six w
    · intro r hr
      have hm : r ∈ (plusImage K L T z v hL hz (Lv L v)).map φ := by rwa [hDimage]
      exact hw ⟨r, hm⟩
    · exact hBimage b.property
  · exact fixedSpace_antitone _ (map_mono (map_mono (comap_mono hLB)))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
