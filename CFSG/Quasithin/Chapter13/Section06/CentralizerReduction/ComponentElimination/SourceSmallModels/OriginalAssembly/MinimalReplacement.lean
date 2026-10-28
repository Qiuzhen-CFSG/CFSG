module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.Transport

/-!
# The minimal component with the original faithful image

Finiteness gives a minimal member of the literal local family inside K Tᵥ
whose star image is K*. Choosing it below K preserves containment as well
as the faithful image. The source replacement observation then retains Y_z.
Once the earlier component-invariance theorem is applied to Y_z, the two
native plus quotients are identified through their original component maps.

This choice does not by itself assert shortness or intrinsic quasisimplicity.
Those structural conclusions belong to the source classification argument.

Source: Aschbacher--Smith, proof of 13.6.22, printed p.932, first paragraph.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.MinimalReplacement
open ComponentSelection
open SourceTransferFields.RankOneBorel SourceTransferFields.RankOneBorel.Replacement
variable {G : Type*} [Group G] [Finite G]

/-- The source minimum retains the same faithful image and belongs to Y_z.
Minimality is among all local members with that image, not only among
subgroups already known to lie in K. -/
theorem exists_minimal_same_star (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧
      Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v) ∧
        starImage z v D = starImage z v K) K₀ ∧
      K₀ ∈ Yz L T z v := by
  obtain ⟨K₀, hle, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v) ∧
      starImage z v D = starImage z v K) K ⟨⟨le_sup_left, hK.1.2⟩, rfl⟩
  exact ⟨K₀, hle, hmin, mem_Yz_of_starImage_eq L T z v hK
    ⟨hle.trans hK.1.1, hmin.1.1.2⟩ hmin.1.2⟩

/-- Application of the earlier invariance conclusion to the chosen source
minimum. The resulting model is on K₀'s literal plus quotient, with exactly
the original component-map marking on every representative. -/
theorem exists_minimal_same_star_marked
    (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    {M : Type*} [Group M]
    (e : plusImage K L T z v hL hz K ≃* M) :
    ∃ (K₀ : Subgroup G) (hle : K₀ ≤ K),
      Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v) ∧
        starImage z v D = starImage z v K) K₀ ∧
      K₀ ∈ Yz L T z v ∧ Tv T v ≤ normalizer (K₀ : Set G) ∧
      WK K₀ L T z v = WK K L T z v ∧
      ∃ e₀ : plusImage K₀ L T z v hL hz K₀ ≃* M,
        ∀ k : K₀, e₀ (componentMap K₀ L T z v hL hz k) =
          e (componentMap K L T z v hL hz (inclusion hle k)) := by
  obtain ⟨K₀, hle, hmin, hY⟩ := exists_minimal_same_star K L T z v hK
  have hn₀ := h14 K₀ hY
  have hnK := h14 K hK
  refine ⟨K₀, hle, hmin, hY, hn₀,
    WK_eq_of_starImage_eq K₀ K L T z v hY.1.1 hK.1.1 hn₀ hnK hmin.1.2, ?_⟩
  exact ⟨MinimalGeometry.modelOfEqualStarImage K₀ K L T z v hL hz
      hK.1.1 hle hn₀ hnK hmin.1.2 e,
    MinimalGeometry.modelOfEqualStarImage_mk K₀ K L T z v hL hz
      hK.1.1 hle hn₀ hnK hmin.1.2 e⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.MinimalReplacement
