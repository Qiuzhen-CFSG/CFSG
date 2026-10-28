module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.Original
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.FieldUniverse
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
/-!
# Second-block recovery from the original natural section

The original full natural section selects the genuine paired linear source.
Original HStar movement supplies its Thompson hypothesis, and nonsolvability
forces the selected binary field to be larger than two. The same full section
marks the first intrinsic natural block. The second-block consumer therefore
requires neither an independent paired marker nor a field-size or intrinsic
natural-block hypothesis.
Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747, using E.2.3.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type*} [Field F] [CharP F 2]
local instance secondBlockSourceFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The actual original natural-section branch recovers the second local block. -/
theorem source_original_second_block_of_hstar_natural_four
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsBlock (L.subgroupOf (localJoin T L)))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (A : Subgroup G) (hAL : A ≤ L) (hA : Nat.card A=3)
    (hAS : A ≤ normalizer (baumann (T : Subgroup G) : Set G))
    {K M : Subgroup G} (hKM : K ≤ M) (hK : (K.subgroupOf M).IsCComponent)
    (hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlocal : ChapterC.GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T : Subgroup G) ≤ K ⊔ baumann (T : Subgroup G) from le_sup_right))) :
    ChapterC.IsBlock (K.subgroupOf M) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker=C := QuotientGroup.ker_mk' C
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D hH hZH
  obtain ⟨d,E,⟨c⟩,hexchange⟩ :=
    source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hF f n
  have hE := ChapterC.RankOne.ChiProduct.SelectedRankOne.paired_linear_field_large
    S (source_a5_minimal_parabolic D e hn) U hU hJ q hq hk
      (source_join_not_solvable D) d E c
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq] at hE ⊢
    have hd : 2 ≤ E.degree := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
      norm_num at hp
      omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at hp
    omega
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hL : ChapterC.IsL2EvenBlock L 2 :=
    source_natural_block_of_identified_moved_section_any_universe L D.fullModule
      (ChapterC.RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hLH) hb.short)
      (source_original_blockU_eq_full_moved D hb) (e.trans f) hF n
  exact source_original_second_block_of_paired_linear D e hn hb hz hH hZH
    A hL hAL hA hAS hKM hK hBK hlocal hJ d E hlarge c hexchange
end CFSG.Quasithin.Chapter10
