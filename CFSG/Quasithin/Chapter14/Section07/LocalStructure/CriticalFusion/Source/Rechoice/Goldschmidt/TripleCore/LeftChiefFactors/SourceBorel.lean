module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.DualCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SectionCentralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.Sections
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# The original Borel images from the earlier upper-root marking

The actual map L₁T → H/O₂(H) has two-group kernel. Its two-core image is
the already marked upper root group of order four, while the original
quotient of L₁T by its two-core is S₃. Core lifting and kernel-image counting
therefore give image order twenty-four. Normality of the root image puts
that image inside the marked S₄ normalizer, so the two groups are equal.
Preservation of the two-residual then identifies the original L₁ image
with the marked A₄ Borel.

This constructs both fields of CompatibleBorel from Structural1222 and the
existing UpperMarking, with no separate local cubic actor or action-kernel
assumption. The original qH, flag and natural-module marking are retained.
The natural chief-count application also supplies the earlier section kernel
through Structural1222 and Uniqueness127. Constructing the earlier UpperMarking
and assembling the full five-factor argument remain source obligations.

This extension imports LeftChiefFactors and belongs above it; connect it
through a higher assembly module, without re-exporting it from that parent.

Source: Aschbacher--Smith, 14.7.65 and the proof of 14.7.70, printed
pp.1070 and1074; the original parabolic quotient in Notation12.8.2.
-/

noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors
open Matrix.SpecialLinearGroup
open Theory.SpecificGroups.Alternating
open LocalGeometry.Preparation
open scoped IsMulCommutative

private theorem marking_range (r : ChapterJ.L2FourAction) :
    (markingHom r).range = alternatingGroup (Fin 5) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (r.marking g).property
  · intro hx
    obtain ⟨g, hg⟩ := r.marking.surjective ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩

private theorem borel_eq_root_normalizer_inf (r : ChapterJ.L2FourAction) :
    borel r = alternatingGroup (Fin 5) ⊓ Subgroup.normalizer (root r : Set ChapterJ.S5) := by
  have hp : (Subgroup.normalizer (root r : Set ChapterJ.S5)).comap (markingHom r) = B0 := by
    change (Subgroup.normalizer (U0.map (markingHom r) : Set ChapterJ.S5)).comap (markingHom r) = B0
    rw [comap_normalizer_eq_of_le_range (map_le_range (markingHom r) U0)]
    rw [comap_map_eq_self_of_injective (markingHom_injective r)]
  calc
    borel r = B0.map (markingHom r) := rfl
    _ = ((Subgroup.normalizer (root r : Set ChapterJ.S5)).comap (markingHom r)).map
        (markingHom r) := congrArg (fun B : Subgroup SL => B.map (markingHom r)) hp.symm
    _ = _ := by rw [map_comap_eq, marking_range]

private theorem root_normalizer_eq (r : ChapterJ.L2FourAction) :
    Subgroup.normalizer (root r : Set ChapterJ.S5) = normalizer r := by
  apply le_antisymm _ (normalizer_le_root_normalizer r)
  intro g hg
  change g ∈ Subgroup.normalizer (borel r : Set ChapterJ.S5)
  rw [borel_eq_root_normalizer_inf]
  apply inf_normalizer_le_normalizer_inf
  constructor
  · rw [Subgroup.normalizer_eq_top]
    trivial
  · exact (Subgroup.normalizer (root r : Set ChapterJ.S5)).le_normalizer hg

private theorem root_card (r : ChapterJ.L2FourAction) : Nat.card (root r) = 4 := by
  rw [Nat.card_congr (rootCoordinates r).toEquiv]
  change Nat.card F = 4
  rw [Nat.card_eq_fintype_card, card_field]

private theorem normalizer_card (r : ChapterJ.L2FourAction) : Nat.card (normalizer r) = 24 := by
  obtain ⟨i, hi⟩ := borel_eq_even_stabilizer r
  have hN : normalizer r = MulAction.stabilizer ChapterJ.S5 i := by
    rw [normalizer, hi, FiveBorelCentralFactor.even_stabilizer_normalizer]
  have hindex : (MulAction.stabilizer ChapterJ.S5 i).index = 5 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hc := (MulAction.stabilizer ChapterJ.S5 i).card_mul_index
  have hS : Nat.card ChapterJ.S5 = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hindex, hS] at hc
  rw [hN]
  omega

private theorem normalizer_residual (r : ChapterJ.L2FourAction) :
    (pResidual 2 (normalizer r)).map (normalizer r).subtype = borel r := by
  have hBN : borel r ≤ normalizer r := (borel r).le_normalizer
  have hB : borel r = alternatingGroup (Fin 5) ⊓ normalizer r := by
    obtain ⟨i, hi⟩ := borel_eq_even_stabilizer r
    rw [normalizer, hi, FiveBorelCentralFactor.even_stabilizer_normalizer]
  have hp : IsPPerfect 2 (borel r) := by
    have hp0 : IsPPerfect 2 B0 := rankOneBorel_isPPerfect
      (by rw [Nat.card_eq_fintype_card, card_field])
    exact hp0.of_surjective (B0.equivMapOfInjective (markingHom r)
      (markingHom_injective r)).toMonoidHom
      (B0.equivMapOfInjective (markingHom r) (markingHom_injective r)).surjective
  apply le_antisymm
  · rw [hB]
    refine le_inf ?_ (map_subtype_le _)
    have h := map_pResidual_le 2 (normalizer r).subtype
    rwa [Equiv.Perm.twoResidual_eq_alternating] at h
  · have hp' : IsPPerfect 2 ((borel r).subgroupOf (normalizer r)) :=
      hp.of_surjective (subgroupOfEquivOfLe hBN).symm.toMonoidHom
        (subgroupOfEquivOfLe hBN).symm.surjective
    have h := map_mono (f := (normalizer r).subtype)
      (le_pResidual_of_isPPerfect ((borel r).subgroupOf (normalizer r)) hp')
    rwa [map_subgroupOf_eq_of_le hBN] at h

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
local notation "B" => (group F L)

private theorem source_map_node (S : Subgroup B) :
    ((S.map (B).subtype).subgroupOf F.H).map d.qH = S.map (sourceActorMap d) := by
  have he : (S.map (B).subtype).subgroupOf F.H = S.map (inclusion group_le_H) := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      exact ⟨b, hb, Subtype.ext hba⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  rw [he, map_map]
  rfl

private theorem source_core_image (mark : UpperMarking d) :
    (pCore 2 B).map (sourceActorMap d) = root d.naturalQuotient := by
  have he := source_map_node d (pCore 2 B)
  change ((F.Ri L 1).subgroupOf F.H).map d.qH =
    (pCore 2 B).map (sourceActorMap d) at he
  rw [← he]
  exact mark

private theorem source_map_kernel_isPGroup : IsPGroup 2 (sourceActorMap d).ker := by
  change IsPGroup 2 (d.qH.comp (inclusion group_le_H)).ker
  rw [← MonoidHom.comap_ker, d.qH_ker]
  exact (isPGroup_pCoreIn 2 F.H).comap_subtype.comap_of_injective _
    (inclusion_injective group_le_H)

private theorem source_image_card
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (mark : UpperMarking d) : Nat.card (sourceActorMap d).range = 24 := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let I : Subgroup ChapterJ.S5 := f.range
  let g : B →* I := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hk : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact source_map_kernel_isPGroup d
  have hp : (pCore 2 B).map g = pCore 2 I := by
    rw [← g.comap_pCore_of_ker_isPGroup hg hk]
    apply map_comap_eq_self
    rw [g.range_eq_top_of_surjective hg]
    exact le_top
  have hm : (pCore 2 I).map I.subtype = root d.naturalQuotient := by
    rw [← hp, map_map]
    exact source_core_image d mark
  have hpc : Nat.card (pCore 2 I) = 4 := by
    calc
      Nat.card (pCore 2 I) = Nat.card ((pCore 2 I).map I.subtype) :=
        (card_map_of_injective I.subtype_injective).symm
      _ = 4 := hm ▸ root_card d.naturalQuotient
  have hquot : Nat.card (B ⧸ pCore 2 B) = 6 := by
    rw [Nat.card_congr (leftQuotientEquiv d structural).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hquot, g.card_pCore_of_ker_isPGroup hg hk, hpc] at hc
  have hc' := card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv] at hc'
  apply Nat.mul_left_cancel (Nat.card_pos (α := g.ker))
  change Nat.card g.ker * Nat.card I = Nat.card g.ker * 24
  nlinarith [hc, hc']

/-- The earlier upper-root marking already forces both required Borel images. -/
public theorem compatibleBorel_of_upperMarking
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (mark : UpperMarking d) : CompatibleBorel d := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let N := normalizer d.naturalQuotient
  have hle : f.range ≤ N := by
    have h := le_normalizer_map (H := pCore 2 B) f
    have hcore : (pCore 2 B).map f = root d.naturalQuotient := source_core_image d mark
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, hcore,
      root_normalizer_eq] at h
    exact h
  have heq : f.range = N := eq_of_le_of_card_ge hle (by
    calc
      Nat.card N = 24 := normalizer_card d.naturalQuotient
      _ ≤ Nat.card f.range := (source_image_card d structural mark).ge)
  let q : B →* N := f.codRestrict N (fun b => heq ▸ MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  have hq : Function.Surjective q := by
    intro n
    obtain ⟨b, hb⟩ := (show n.val ∈ f.range from heq.symm ▸ n.property)
    exact ⟨b, Subtype.ext hb⟩
  have hres : (pResidual 2 B).map f = borel d.naturalQuotient := by
    calc
      (pResidual 2 B).map f = ((pResidual 2 B).map q).map N.subtype := by
        rw [map_map]
        rfl
      _ = (pResidual 2 N).map N.subtype := by rw [map_pResidual_of_surjective 2 q hq]
      _ = borel d.naturalQuotient := normalizer_residual d.naturalQuotient
  refine ⟨?_, heq⟩
  rw [← residual_group d structural, source_map_node]
  exact hres

/-- Apply the actual marking to the source natural chief-factor lower bound. -/
public theorem sourceNaturalChief_count_of_upperMarking
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : UpperMarking d)
    (s : NoncentralChiefRefinement.ChiefSeries (group F L))
    (hs0 : s.head = sourcePointNode (F := F) (L := L))
    (hsl : s.last = sourceUNode d) : 2 ≤ s.noncentralTwoCount :=
  sourceNaturalChief_count_of_earlier_setup d structural uniqueness
    (compatibleBorel_of_upperMarking d structural mark) s hs0 hsl

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
