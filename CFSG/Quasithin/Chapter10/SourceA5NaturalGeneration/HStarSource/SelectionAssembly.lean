module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.SelectedBlockGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HStarSource.PairedHallNormalizer
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalCubic
/-!
# Compatible natural blocks and the prescribed Hall cubic

Select the paired field-four source once. Its canonical component and cubic
supply both intrinsic blocks through the common characteristic pair. Then
conjugate that same component and cubic by the Sylow element placing the
cubic in the prescribed Hall. The Hall normalizes the selected component,
including after conjugation, and its alpha fixed subgroup stays nontrivial.
This is the compatible input to the literal original torus-axis argument.

Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterC ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

/-- Both actual natural blocks, together with the same Hall cubic. -/
structure SourceNaturalHallPair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (C K P : Subgroup G) : Prop where
  original_block : IsBlock (L.subgroupOf (localJoin T L))
  original_natural : IsL2EvenBlock L 2
  original_core : pCore 2 L=blockU L
  baumann_le_orbit : baumann (T : Subgroup G) ≤ localOrbit T L
  baumann_sylow : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
    (localOrbit T L ⊔ baumann (T : Subgroup G))
  baumann_normalizes_original : baumann (T : Subgroup G) ≤ normalizer (L : Set G)
  selected_natural : IsL2EvenBlock K 2
  selected_core : pCore 2 K=blockU K
  selected_center : center K=⊥
  selected_sylow : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G) ⊓ K) K
  baumann_normalizes_selected : baumann (T : Subgroup G) ≤ normalizer (K : Set G)
  escapes : ¬ K ≤ D.maximalLocal
  hall_normalizes : C ≤ normalizer (K : Set G)
  cubic_hall : P ≤ C
  cubic_block : P ≤ K
  cubic_card : Nat.card P=3
  alpha_fixed : thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance selectionAssemblyFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
set_option backward.isDefEq.respectTransparency false in
theorem source_natural_hall_pair_of_three_hall
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hzL : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G)=⊥)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hB : IsPGroup 3 B) (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H)) :
    9 ∣ Nat.card B ∧ ∃ K P : Subgroup G, SourceNaturalHallPair D (B.map H.subtype) K P := by
  obtain ⟨d,E,hE,⟨c⟩,hexchange⟩ := source_hstar_paired_four_of_three_hall
    D e hn hH hZH hF f n hzL hzH B hBM hHall hB hlarge hCZ
  have h9 := source_hstar_paired_nine_dvd_hall D hH B hBM hHall d E hE c
  obtain ⟨K,hK,_,hcan,_,hBK,hlocal,_,_,⟨eK⟩,hgen,hcover,A,hAK,hA,hAB,s,hs,hAH,hAc,hfix⟩ :=
    source_hstar_paired_component_and_hall_cubic D e hn hH hZH hF f n
      hlarge hCZ B hHall d E hE c hexchange
  obtain ⟨AL,hAL,hALc,hALB⟩ := source_original_cubic_of_hstar_natural_four D e hn hH hZH hF f n
  have geom := source_both_natural_four_block_geometry D e hn hH hZH hF f n hlarge hCZ
    hzH hzL K hK hBK hlocal hgen (Or.inr (by obtain ⟨t,ht,hc⟩ := hcover; exact ⟨t,ht,hc⟩))
    AL hAL hALc hALB A hAK hA hAB hE eK
  let K' := (K.map H.subtype).map (MulAut.conj (s:G)).toMonoidHom
  let P := (A.map (MulAut.conj s).toMonoidHom).map H.subtype
  obtain ⟨hKn,hKc,hKz,hKS,hSK,hout⟩ := source_selected_block_ambient_conjugate D hH K hgen geom s hs
  have hKm : (K.map (MulAut.conj s).toMonoidHom).map H.subtype=K' := by
    rw [map_map,show H.subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s:G)).toMonoidHom.comp H.subtype from rfl,←map_map]
  have hBN : B.map H.subtype ≤ normalizer (K' : Set G) := by
    rw [←hKm]
    exact (map_mono ((source_hstar_paired_hall_normalizes D hH B hBM hHall d K hcan hcover).2 s)).trans
      ((K.map (MulAut.conj s).toMonoidHom).le_normalizer_map H.subtype)
  have hPK : P ≤ K' := by
    rw [←hKm]
    exact map_mono (map_mono hAK)
  have hPc : Nat.card P=3 := by
    rw [card_map_of_injective H.subtype_injective,hAc]
  exact ⟨h9,K',P,⟨geom.original_block,geom.original_natural,geom.original_core,
    geom.baumann_le_orbit,geom.baumann_sylow,geom.baumann_normalizes_original,
    hKn,hKc,hKz,hKS,hSK,hout,hBN,map_mono hAH,hPK,hPc,
    alpha_fixed_subtype_nontrivial T H hH.1.1.2 _ hfix⟩⟩
end CFSG.Quasithin.Chapter10
