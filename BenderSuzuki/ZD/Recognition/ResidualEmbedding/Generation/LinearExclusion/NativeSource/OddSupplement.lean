module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.OddSupplement.LinearComplement
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.OddSupplement.SourceTransfer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.TwoStructure.ModelConsequences

/-!
# The original odd supplement in source Lemma 15.5

For J=C_G(L) with nontrivial two-core, the actual embedding into the marked
PSL₂ group puts J in a Borel and constructs an odd cyclic complement Y.
The source normalizer control and the index [C₀:J] give Burnside transfer
inside C₀=C_M(A), proving the actual carrier product C₀=O₂(M)Y.

The final theorem fills every field of CentralizerLocalTwoData: the
centralizer two-core is Sylow and elementary, contains every involution of
the pair stabilizer D, and is exactly D∩O₂(M). The sole earlier-source
premise is O₂(J)≠1, the conclusion of Lemma 15.4. The model embedding and
all complement and normalizer data are constructed from the original
Context, rather than supplied as additional hypotheses.

Source: refs/KGroup/GLS4/Chapter2.tex, the paragraph following Lemma 15.4
and Lemma 15.5, approximately lines 2692–2710.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "J" => (centralizer (L : Set G) : Subgroup G)
local notation "C₀" => (M ⊓ centralizer (A : Set G) : Subgroup G)
local notation "V" => Subgroup.map M.subtype (pCore 2 M)

/-- Source Lemma 15.5: the actual odd supplement of the point two-core in
C_M(A), with only the preceding nontrivial-centralizer-core conclusion. -/
public theorem Context.centralizer_odd_supplement (hne : pCore 2 J ≠ ⊥) :
    ∃ Y : Subgroup G, Y ≤ J ∧ Odd (Nat.card Y) ∧ IsCyclic Y ∧
      Nat.card Y ∣ 2 ^ n - 1 ∧ (C₀ : Set G) = (V : Set G) * (Y : Set G) := by
  obtain ⟨Y, hYJ, ho, hc, hd, _, hprod, hn⟩ := d.exists_linear_centralizer_complement hne
  exact ⟨Y, hYJ, ho, hc, hd, d.centralizer_product_of_odd_complement Y hYJ ho hprod hc hn⟩

/-- The literal source consumer: all earlier two-core fields needed by the
Lemma 15.6 count, without a separate model or odd-supplement premise. -/
public theorem Context.centralizerLocalTwoData_of_twoCore_ne_bot
    (hne : pCore 2 J ≠ ⊥) : CentralizerLocalTwoData d := by
  obtain ⟨hm⟩ := d.centralizerLocalModelData
  obtain ⟨Y, hYJ, ho, _, _, hprod⟩ := d.centralizer_odd_supplement hne
  exact {
    twoCore_ne_bot := hne
    twoCore_sylow := d.centralizer_twoCore_sylow hm hne
    twoCore_elementary := d.centralizer_twoCore_elementary hm
    pair_core_eq := d.pair_core_eq_of_odd_supplement hYJ ho hprod
    pair_involutions := fun _ hvD hv => d.pair_involutions_mem_twoCore hm hne hvD hv
    centralizer_odd_supplement := ⟨Y, hYJ, ho, hprod⟩ }

end BenderSuzuki.ZD.LinearExclusion
