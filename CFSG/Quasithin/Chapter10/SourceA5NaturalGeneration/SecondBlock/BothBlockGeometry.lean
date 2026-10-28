module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.SymmetricSource
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.OriginalGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.HStarBlockGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.BothBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.QuotientCardSixty
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.CharacteristicSource
/-!
# Both natural-four blocks with their original core and Sylow geometry

The intrinsic characteristic-pair assembly recovers both blocks and retains
some natural type for the same selected K. Its actual marked SL₂(4) quotient
has order sixty, forcing that natural type to have degree two. The original
and H* full-core arguments then supply both core equalities, both trivial
centers, and the exact common Baumann Sylow and normalization facts needed
by the terminal torus argument. No first-block or natural-type assumption
is added to the original source data.
Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterE Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

/-- Geometry on the same original L and selected intrinsic K. -/
structure SourceBothBlockGeometry (T : Sylow 2 G) (L H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (K : Subgroup H) : Prop where
  original_block : IsBlock (L.subgroupOf (localJoin T L))
  selected_block : IsBlock K
  original_natural : IsL2EvenBlock L 2
  selected_natural : IsL2EvenBlock K 2
  original_core : pCore 2 L=blockU L
  selected_core : pCore 2 K=blockU K
  original_center : center L=⊥
  selected_center : center K=⊥
  baumann_le_orbit : baumann (T : Subgroup G) ≤ localOrbit T L
  baumann_sylow : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
    (localOrbit T L ⊔ baumann (T : Subgroup G))
  baumann_normalizes_original : baumann (T : Subgroup G) ≤ normalizer (L : Set G)
  baumann_normalizes_selected : baumann (T.subtype hTH : Subgroup H) ≤ normalizer (K : Set H)
  selected_sylow : Chapter1.IsSylowIn 2 (baumann (T.subtype hTH : Subgroup H) ⊓ K) K

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance bothBlockGeometryFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
/-- The source characteristic pair and marked quotient supply both natural-four blocks. -/
theorem source_both_natural_four_block_geometry
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F = 4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hlarge : 1 < generationParameter H)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H))
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (hzL : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hBK : baumann (T.subtype hH.1.1.2 : Subgroup H) ≤ normalizer (K : Set H))
    (hlocal : GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T.subtype hH.1.1.2 : Subgroup H) ≤
        K ⊔ baumann (T.subtype hH.1.1.2 : Subgroup H) from le_sup_right)))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H)=⊤)
    (hR : pResidual 2 H=K ∨ ∃ t : H,
      t ∈ (T.subtype hH.1.1.2 : Subgroup H) ∧
        pResidual 2 H=K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (AL : Subgroup G) (hAL : AL ≤ L) (hALcard : Nat.card AL=3)
    (hALB : AL ≤ normalizer (baumann (T : Subgroup G) : Set G))
    (AK : Subgroup H) (hAK : AK ≤ K) (hAKcard : Nat.card AK=3)
    (hAKB : AK ≤ normalizer (baumann (T.subtype hH.1.1.2 : Subgroup H) : Set H))
    {E : Type*} [Field E] (hE : Nat.card E=4)
    (eK : (K ⧸ pCore 2 K) ≃* SL(2,E)) :
    SourceBothBlockGeometry T L H hH.1.1.2 K := by
  obtain ⟨hbL,hbK,m,hKm⟩ := source_both_blocks_of_intrinsic_localClass
    D e hn hH hZH hF f n hlarge hCZ hzH hzL K hK hBK hlocal hgen hR
    AL hAL hALcard hALB AK hAK hAKcard hAKB
  have hq : Nat.card (K ⧸ pCore 2 K)=60 := by
    let : Finite E := Nat.finite_of_card_ne_zero (hE ▸ (by decide : 4≠0))
    rw [Nat.card_congr eK.toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hE]
    norm_num
  have hKn : IsL2EvenBlock K 2 := hKm.four_of_quotient_card hq
  have hR' : pResidual 2 H=K ∨ ∃ t : H,
      pResidual 2 H=K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    rcases hR with h | ⟨t,_,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t,h⟩
  obtain ⟨hzK,hcoreK,hSK⟩ := source_hstar_block_core_and_sylow
    D e hn hH hZH hF f n hlarge hCZ hzH K hbK hR'
  obtain ⟨hLn,hcoreL,hzL',hBO,hBS,hBL⟩ := source_original_block_geometry_of_hstar_natural_four
    D e hn hbL hzL hH hZH hF f n
  exact ⟨hbL,hbK,hLn,hKn,hcoreL,hcoreK,hzL',hzK,hBO,hBS,hBL,hBK,hSK⟩
end CFSG.Quasithin.Chapter10
