module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.CoreGrowth.Counting
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.CoreGrowth.Dihedral
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.PairResidual.Dihedral

/-!
# The original source two-core growth theorem

If all involutions of V=O₂(M) lay in the proper root A<V, the two-group
case for J would already contradict that assertion. Otherwise the literal
K×Y action makes |J| coprime to q−1 and makes V a complement to D in M.
The intrinsic PSL₂ subgroup theorem identifies J as odd-dihedral. Its
cyclic outer quotient makes O²(D) proper, contradicting O²(M)=M through
the actual complement projection. This completes source Lemma 15.3.

Source: GLS IV, Chapter 2, Lemma 15.3,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- Source Lemma 15.3, on the original point two-core and distinguished root. -/
public theorem Context.twoCore_growth : CentralizerTwoCoreGrowth d := by
  intro hlt
  by_contra hno
  have hinv (v : M) (hv : v ∈ pCore 2 M) (hi : PFAppendixIII.IsInvolution v) :
      (v : G) ∈ closure (Z ∩ (M : Set G)) := by
    by_contra ha
    exact hno ⟨v, hv, hi, ha⟩
  have hnot : ¬ IsPGroup 2 (centralizer (residualGenerated M z t : Set G)) := by
    intro htwo
    obtain ⟨v, hv, hi, ha⟩ := d.twoCore_involution_outside_distinguished_of_isPGroup htwo
    exact ha (hinv v hv hi)
  have hinvG : ∀ v ∈ (pCore 2 M).map M.subtype, PFAppendixIII.IsInvolution v →
      v ∈ closure (Z ∩ (M : Set G)) := by
    rintro v ⟨w, hw, rfl⟩ hi
    exact hinv w hw (IsInvolution.subtype hi w.property)
  obtain ⟨r, hr, _, _, ⟨e⟩⟩ := d.centralizer_dihedral_of_coprime hnot
    (d.centralizer_coprime_split_of_involutions hinvG hlt)
  exact linearExclusion_of_pair_normalComplement d.reduction d.minimal.disconnected
    (pCore 2 M) inferInstance (d.point_twoCore_complement_of_involutions hinvG hlt hnot)
    (d.pairResidual_of_dihedral hr e)

end BenderSuzuki.ZD.LinearExclusion
