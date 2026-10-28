module
public import CFSG.Quasithin.ChapterE.Section02.Structure.WreathBorel
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs

/-!
# The opposite Borel in the original H-star intersection

For the original C-component K₁ and S = T ∩ N(K₁), one has
S ∩ K₁ = T ∩ K₁. The intrinsic component-Borel placement in the actual
symmetric-five wreath quotient therefore applies to the literal F.1.1
Borel. Original 15.1.9 identifies its maximal Sylow overgroup with H ∩ M.
No new component is chosen and no marked normalizer premise is assumed.

Together with the residual/Sylow supplement H ∩ M = O²(H ∩ M)T and
the prepared module's residual centralizer bound, this puts the opposite
Borel in C_M(V)T for the source mixed-amalgam construction.

Source: Aschbacher--Smith 15.2.4, printed pp.1106--1107.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The same component and Sylow normalizer have their literal F.1.1 Borel in H ∩ M. -/
theorem source_HStar_symmetricFive_wreath_borel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H K1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K1 ∈ Chapter1.cComponentsIn H) :
    ChapterF.Source.borel K1 ((T : Subgroup G) ⊓ normalizer (K1 : Set G)) ≤ H ⊓ M := by
  obtain ⟨e⟩ := he
  obtain ⟨_,hP,hmax,_,_⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  have hmaxeq := ChapterB.minimalParabolicMax_unique (T.subtype hH.1.1.2) hP hmax
    (show ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ≤ (H ⊓ M).subgroupOf H from
      fun x hx => ⟨x.property,hM.1.2 hx⟩)
  have hb := ChapterE.Structure.minimalParabolicMax_borel_of_symmetricFive_wreath
    (T.subtype hH.1.1.2) hP e hK.2
  rw [← hmaxeq] at hb
  have hSK : ((T : Subgroup G) ⊓ normalizer (K1 : Set G)) ⊓ K1 = (T : Subgroup G) ⊓ K1 := by
    apply le_antisymm (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    exact le_inf (le_inf inf_le_left (inf_le_right.trans K1.le_normalizer)) inf_le_right
  change K1 ⊓ normalizer ((((T : Subgroup G) ⊓ normalizer (K1 : Set G)) ⊓ K1 : Subgroup G) : Set G) ≤ _
  rw [hSK]
  intro x hx
  have hxH : x ∈ H := hK.1 hx.1
  apply hb (show (⟨x,hxH⟩ : H) ∈ K1.subgroupOf H ⊓
      normalizer ((((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ⊓ K1.subgroupOf H) : Set H) from ?_)
  refine ⟨hx.1,?_⟩
  have hnorm : normalizer ((((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ⊓ K1.subgroupOf H) : Set H) =
      (normalizer (((T : Subgroup G) ⊓ K1 : Subgroup G) : Set G)).subgroupOf H := by
    rw [subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ K1 ≤ H from inf_le_right.trans hK.1)]
    rfl
  rw [hnorm]
  exact hx.2
end CFSG.Quasithin.Chapter15.Section01
