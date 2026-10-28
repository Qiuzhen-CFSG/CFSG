module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.SymmetricSource
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.OriginalGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.HStarBlockGeometry
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.IntrinsicNatural
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.CharacteristicSource
/-!
# Both original components are blocks

The single characteristic pair returns the original L block or the same
selected H* component K with its natural type. In the first orientation,
the original cubic produces central elementary commutators in Baum(T),
and the intrinsic K local class recovers K and its natural type. In the
second orientation, the symmetric full-core argument recovers L. Thus both
blocks are established without changing the selected component, its exact
residual cover, or either actual cubic normalizer.
Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterE Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance bothBlocksFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
theorem source_both_blocks_of_intrinsic_alternative
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
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
    (hfirst : IsBlock (L.subgroupOf (localJoin T L)) ∨
      (IsBlock K ∧ ∃ m, IsL2EvenBlock K m))
    (hR : pResidual 2 H=K ∨ ∃ t : H,
      t ∈ (T.subtype hH.1.1.2 : Subgroup H) ∧
        pResidual 2 H=K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (AL : Subgroup G) (hAL : AL ≤ L) (hALcard : Nat.card AL=3)
    (hALB : AL ≤ normalizer (baumann (T : Subgroup G) : Set G))
    (AK : Subgroup H) (hAK : AK ≤ K) (hAKcard : Nat.card AK=3)
    (hAKB : AK ≤ normalizer (baumann (T.subtype hH.1.1.2 : Subgroup H) : Set H)) :
    IsBlock (L.subgroupOf (localJoin T L)) ∧ IsBlock K ∧ ∃ m, IsL2EvenBlock K m := by
  rcases hfirst with hbL | ⟨hbK,m,hKm⟩
  · obtain ⟨hLn,_,_,hBO,hBS,hBL⟩ := source_original_block_geometry_of_hstar_natural_four
      D e hn hbL hzL hH hZH hF f n
    have hc := source_original_common_baumann_commutator D e hn hbL hzL hH hZH
      AL hLn hBS hBO hAL hALcard hALB hBL
    exact ⟨hbL,source_intrinsic_component_natural_of_common_baumann_commutator
      T H hH.1.1.2 K hK hBK hlocal hc⟩
  · exact ⟨source_original_block_of_hstar_natural_block D e hn hH hZH hF f n
      hlarge hCZ hzH K hbK hKm hR AK hAK hAKcard hAKB,hbK,⟨m,hKm⟩⟩
theorem source_both_blocks_of_intrinsic_localClass
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
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
    (hAKB : AK ≤ normalizer (baumann (T.subtype hH.1.1.2 : Subgroup H) : Set H)) :
    IsBlock (L.subgroupOf (localJoin T L)) ∧ IsBlock K ∧ ∃ m, IsL2EvenBlock K m := by
  have hfirst := source_hstar_one_block_of_intrinsic_localClass D e hn hH hZH hF f n
    hzL hzH K hK hBK hlocal hgen
  exact source_both_blocks_of_intrinsic_alternative D e hn hH hZH hF f n
    hlarge hCZ hzH hzL K hK hBK hlocal hfirst hR AL hAL hALcard hALB
    AK hAK hAKcard hAKB

end CFSG.Quasithin.Chapter10
