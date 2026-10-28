module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth.Torus

/-!
# Applying the local torus to core growth

The local split torus discharges the subgroup premise in the numerical
argument of GLS, Volume 4, Chapter 2, Proposition 17.6. The independent
Section 16 involution classification and Section 3 generation and regularity
premises remain explicit. No further model geometry is required here.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Core growth with the torus premise discharged by the actual local
PSL₂ construction. The remaining geometric inputs belong to the
independent involution and inverted-set arguments. -/
public theorem TwoCoreCountingData.core_growth_of_regular_inverted_set_local_torus
    (d : TwoCoreCountingData Z M) (h : IsProductDisconnected Z M)
    (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (hg : ResidualGeneration Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hclasses : ∀ v : G, orderOf v = 2 → v ∈ Z ∨ IsConj v ((d.u : M) : G))
    (hgen : (Subgroup.closure (coreGrowthInvertedSet M d.t)).map M.subtype =
      residualCommutator M d.t)
    (hregular : ∀ z : M, ∀ hz : (z : G) ∈ Z,
      Function.Bijective (coreGrowthConjugate h d.t z hz)) :
    d.q < Nat.card (pCore 2 M) ∧ ∃ k : ℕ, Nat.card (pCore 2 M) = d.q ^ k := by
  obtain ⟨A, _hcyclic, hcard, hI, _hclosure, hC⟩ :=
    d.exists_local_split_torus h r (fun Y hY => (hlocal Y hY).1)
  exact d.core_growth_of_regular_inverted_set h r ha hg hlocal hclasses hgen hregular
    A hcard hI hC

end BenderSuzuki.ZD
