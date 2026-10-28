module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.G2
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Tits
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Binary

/-!
# Source Borels for the binary exceptional Lie models

The concrete overlap must be the whole source group B₁B₂S. The checked
Sylow-normalizer calculations identify each local Borel with S in the
binary G₂ models, the Atlas Tits model, and the full binary Ree model.
For the Tits group we retain the source local factors O^{2′}(Pᵢ), using
the proved equalities with Pᵢ before computing their normalizers.

Source: Aschbacher--Smith, F.1.1, F.1.3 and F.1.12(I)(3), (5), (8), (9),
printed pp.259--263; Parrott (1972), pp.672, 683--684.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.ExceptionalModels
open Theory.GroupTheory
open scoped Pointwise

private theorem borel_eq_of_normalizer {G : Type*} [Group G] {P S : Subgroup G}
    (hSP : S ≤ P) (hN : Subgroup.normalizer (S : Set G) = S) :
    Source.borel P S = S := by
  rw [Source.borel, inf_eq_left.mpr hSP, hN, inf_eq_right.mpr hSP]

private theorem borel_eq_of_relative_normalizer {G : Type*} [Group G]
    {P S : Subgroup G} (hSP : S ≤ P)
    (hN : Subgroup.normalizer (S.subgroupOf P : Set P) = S.subgroupOf P) :
    Source.borel P S = S := by
  rw [← Subgroup.subgroupOf_normalizer_eq hSP] at hN
  rw [Source.borel, inf_eq_left.mpr hSP]
  ext g
  constructor
  · rintro ⟨hg, hgN⟩
    exact (show (⟨g, hg⟩ : P) ∈ S.subgroupOf P from hN ▸ hgN)
  · intro hg
    exact ⟨hSP hg, S.le_normalizer hg⟩

private theorem commonBorel_eq {G : Type*} [Group G] (P₁ P₂ S : Subgroup G)
    (h₁ : Source.borel P₁ S = S) (h₂ : Source.borel P₂ S = S) :
    Source.commonBorel ![P₁, P₂] S = S := by
  change Source.borel P₁ S ⊔ Source.borel P₂ S ⊔ S = S
  rw [h₁, h₂, sup_idem, sup_idem]

/-- The full G₂(2) overlap is literally the source B₁B₂S. -/
theorem g2_full_commonBorel :
    Source.commonBorel ![G2.fullL₁, G2.fullL₂] G2.fullS = G2.fullB := by
  have hN : Subgroup.normalizer (G2.fullB : Set G2.Full) = G2.fullB := by
    change Subgroup.normalizer (Atlas.G2.unipotent (K := ZMod 2) : Set G2.Full) = Atlas.G2.unipotent
    rw [Atlas.G2.SylowNormalizer.normalizer_unipotent,
      Atlas.G2.LieParabolicSetup.borel_eq_unipotent_of_card_two (by simp)]
  exact commonBorel_eq _ _ _
    (borel_eq_of_normalizer Atlas.G2.BinaryParabolicPair.commonSylow_le_first hN)
    (borel_eq_of_normalizer Atlas.G2.BinaryParabolicPair.commonSylow_le_second hN)

/-- The same source equality holds after restriction to the actual derived group. -/
theorem g2_derived_commonBorel :
    Source.commonBorel ![G2.derivedL₁, G2.derivedL₂] G2.derivedS = G2.derivedB :=
  commonBorel_eq _ _ _
    (borel_eq_of_normalizer Atlas.G2.BinaryParabolicPair.derivedSylow_le_first
      Atlas.G2.DerivedNormalizerSolvable.binary_normalizer_derivedSylow)
    (borel_eq_of_normalizer Atlas.G2.BinaryParabolicPair.derivedSylow_le_second
      Atlas.G2.DerivedNormalizerSolvable.binary_normalizer_derivedSylow)

/-- The Tits local residuals and the full source Borel have exactly the checked overlap. -/
theorem tits_commonBorel :
    Source.commonBorel
      ![Tits.ExceptionalParabolics.firstLocalFactor, Tits.ExceptionalParabolics.secondLocalFactor]
      Tits.ExceptionalParabolics.S = Tits.ExceptionalParabolics.overlap := by
  rw [Tits.ExceptionalParabolics.firstLocalFactor_eq,
    Tits.ExceptionalParabolics.secondLocalFactor_eq,
    Tits.ExceptionalParabolics.overlap_eq_sylow]
  exact commonBorel_eq _ _ _
    (borel_eq_of_relative_normalizer Tits.ExceptionalParabolics.sylow_le_first
      Tits.ExceptionalParabolics.first_sylow_normalizer)
    (borel_eq_of_relative_normalizer Tits.ExceptionalParabolics.sylow_le_second
      Tits.ExceptionalParabolics.second_sylow_normalizer)

/-- The full binary Ree root Borel is also the source B₁B₂S. -/
theorem binaryRee_commonBorel :
    Source.commonBorel
      ![Tits.ExceptionalParabolics.FullRee.first, Tits.ExceptionalParabolics.FullRee.second]
      Tits.ExceptionalParabolics.FullRee.S = Tits.ExceptionalParabolics.FullRee.B := by
  rw [Tits.ExceptionalParabolics.FullRee.borel_eq_sylow]
  exact commonBorel_eq _ _ _
    (borel_eq_of_normalizer Tits.ExceptionalParabolics.FullRee.sylow_le_first
      ReeF4.Parabolics.Binary.FixedGeometry.unipotent_normalizer_eq)
    (borel_eq_of_normalizer Tits.ExceptionalParabolics.FullRee.sylow_le_second
      ReeF4.Parabolics.Binary.FixedGeometry.unipotent_normalizer_eq)

end CFSG.Quasithin.ChapterF.GreenBook.ExceptionalModels
