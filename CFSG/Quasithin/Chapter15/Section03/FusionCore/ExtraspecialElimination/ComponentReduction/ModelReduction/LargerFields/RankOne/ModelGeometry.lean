module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.Multiplicity
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.LinearModels
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.SymplecticModel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.ExceptionalModel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.FourModels
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Reduction of the concrete component product to one SL₂ factor

The normalizer facts for the four actual carriers imply the whole
intrinsic reduction. Cubic Sylow control places C in a Borel of the
central product, forces even field degree, and bounds every factor's
Borel theta rank by one. This excludes SL₃, Sp₄ and G₂. The remaining
SL₂ factors are centerless, so their cubic torus elements contribute
independent dimensions to C. Hence the nonempty family has one factor,
which is the whole group and supplies the required multiplicative equivalence.

`collapse_of_four_models` supplies all four concrete normalizer calculations
over any finite field of characteristic two and order greater than two.
Its inputs are the actual commuting family, its generation of the ambient
group, its model equivalences and intrinsic cubic Sylow control. The earlier
`collapse_of_model_normalizers` remains available as a conditional interface.
The source application still has to construct the component family and its
four-model alternatives from the offender classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 after (k), printed p.1144.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
open ModelGeometry
variable {D : Type*} [Group D] [Finite D]
variable {F : Type} [Field F] [CharP F 2]

/-- Conditional assembly of the central-product reduction. The four concrete
normalizer calculations remain explicit until supplied by the model modules. -/
theorem collapse_of_model_normalizers {ι : Type*} [Finite ι] [Nonempty ι]
    (K : ι → Subgroup D)
    (hc : Pairwise fun i j => K i ≤ centralizer (K j : Set D))
    (hgen : iSup K = ⊤) (n : ℕ) (hmodels : ∀ i, FourModels (K i) F)
    (h2 : NormalizerData SL(2,F) n 1)
    (h3 : NormalizerData SL(3,F) n 2)
    (h4 : NormalizerData (Matrix.symplecticGroup (Fin 2) F) n 2)
    (hg : NormalizerData (Atlas.G2.Model F) n 2)
    (C : Subgroup D) (hC : CubicSylowControl D C) :
    (∀ i, K i = ⊤) ∧ Nonempty (D ≃* SL(2,F)) := by
  classical
  let _ := Fintype.ofFinite ι
  have hd (i : ι) : ∃ r : ℕ, 1 ≤ r ∧ NormalizerData (K i) n r := by
    rcases hmodels i with h | h | h | h
    · exact ⟨1, le_rfl, h2.of_equiv h.some⟩
    · exact ⟨2, by decide, h3.of_equiv h.some⟩
    · exact ⟨2, by decide, h4.of_equiv h.some⟩
    · exact ⟨2, by decide, hg.of_equiv h.some⟩
  choose r hr hdata using hd
  have he (i : ι) : Nonempty (K i ≃* SL(2,F)) := by
    rcases hmodels i with h | h | h | h
    · exact h
    · have := family_factor_rank_le_one K hc hgen n r hdata C hC i 2 (h3.of_equiv h.some)
      omega
    · have := family_factor_rank_le_one K hc hgen n r hdata C hC i 2 (h4.of_equiv h.some)
      omega
    · have := family_factor_rank_le_one K hc hgen n r hdata C hC i 2 (hg.of_equiv h.some)
      omega
  have hcenter (i : ι) : center (K i) = ⊥ := by
    obtain ⟨e⟩ := he i
    apply (center (K i)).eq_bot_iff_forall.mpr
    intro x hx
    have hz : e x ∈ center SL(2,F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e ((mem_center_iff.mp hx) z)
    rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot, mem_bot] at hz
    exact e.injective (hz.trans e.map_one.symm)
  have ht := family_eq_top K hc hgen hcenter n r hr hdata C hC
  refine ⟨ht, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨e⟩ := he i
  exact ⟨((topEquiv (G := D)).symm.trans (MulEquiv.subgroupCongr (ht i).symm)).trans e⟩

/-- A nonempty commuting family of the four concrete nonbinary models collapses
to one SL₂ factor under intrinsic cubic Sylow control. All Borel placement and
normalizer calculations are supplied by the concrete model theorems. -/
theorem collapse_of_four_models [Finite F] {ι : Type*} [Finite ι] [Nonempty ι]
    (K : ι → Subgroup D)
    (hc : Pairwise fun i j => K i ≤ centralizer (K j : Set D))
    (hgen : iSup K = ⊤) (n : ℕ) (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hmodels : ∀ i, FourModels (K i) F)
    (C : Subgroup D) (hC : CubicSylowControl D C) :
    (∀ i, K i = ⊤) ∧ Nonempty (D ≃* SL(2,F)) := by
  exact collapse_of_model_normalizers K hc hgen n hmodels
    (linearTwo_normalizerData F n hF hn)
    (linearThree_normalizerData F n hF hn)
    (symplectic_normalizerData hF hn)
    (g2_normalizerData hF hn) C hC
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
