module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.LinearThree
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.LinearThreeFourCover

/-!
# The two degree-three rows of the paired-cubic source

The original marked component is either a characteristic-two PSL₃ over an
unspecified even field or the exceptional central cover of PSL₃(4). The first
row collapses to PSL₃(2) using the intrinsic normal four-group; the second
contradicts the same normal-four geometry after its full central kernel is
retained. Earlier paired-cubic source geometry supplies the Thompson equality.

Source: Aschbacher–Smith, inspection before 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The exact two degree-three alternatives at the original marked source. -/
theorem SourceCentralizerGeometry.linear_three_rows_binary
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hmodels : (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL K 3 (2^f)) ∨
      (center K = pCore 2 K ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)) :
    Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
  rcases hmodels with ⟨f,hf,hfK⟩ | ⟨hc,hm⟩
  · exact g.psl3_even_binary hG (g.lemma115 hG hM hTM hu).2
      K hK α hα hinner ⟨f,by omega,hfK⟩
  · exact (g.linear_three_four_cover_from_original hG hM hTM hu hST hpair
      K hK α hα hinner hc hm).elim

end CFSG.Quasithin.Chapter2.DoubleA3
