module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Remarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SourceBorel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.PermittedChoice.ActorOrbits
public import Theory.SpecificGroups.Alternating.FiveOrderTwentyFour

/-!
# A compatible upper-root marking of the original natural quotient

Let I be the image of the actual L₁T map into the original H/O₂(H) ≃ S₅.
Its kernel is a two-group. The genuine structural theorem identifies
L₁T/O₂(L₁T) with S₃, so core lifting gives |I| = 6|O₂(I)|. The original
Sylow subgroup maps onto a Sylow subgroup of S₅ inside I, of order eight.
Since |I| divides120 and |O₂(I)| is a power of two, |I| =24 and |O₂(I)| =4.
None of these calculations assumes an upper marking.

The five-point action identifies I with a point stabilizer. Conjugating the
old marked normalizer onto this stabilizer and transporting its two-core
aligns the original R₁-image with the upper root. Data.remark changes the
natural target marking, target action and projection together. It keeps
qH, the source action, the original filtration and all actual subgroups.
A single chosen conjugator is used in every application below.

The checked SourceBorel implications now give the actual L₁ Borel image
and the natural chief-count bound on the original point-to-U interval.
Lifting a nontrivial diagonal gives both the cubic actor and LocalCubic
(with upper parameter zero) for the same chosen datum. LocalActors retains
the genuine earlier seed-fixing identity [V,R₁] ≤ V₁ as an explicit premise;
its earlier producer and final discharge remain with source assembly.
Structural1222 and Uniqueness127 retain their original Chapter12 producers.
The duality, commutator and full five-factor assembly are separate branches.

This extension belongs above LeftChiefFactors and does not alter its exports.
Source: Aschbacher–Smith, Remark14.7.64, Lemma14.7.65 and the proof of14.7.70,
printed pp.1069–1074 (PDF pp.1086–1091).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
local notation "B" => (group F L)

private theorem source_kernel : IsPGroup 2 (sourceActorMap d).ker := by
  change IsPGroup 2 (d.qH.comp (inclusion group_le_H)).ker
  rw [← MonoidHom.comap_ker, d.qH_ker]
  exact (isPGroup_pCoreIn 2 F.H).comap_subtype.comap_of_injective _
    (inclusion_injective group_le_H)

/-- Core lifting counts the original image without choosing an upper marking. -/
theorem source_image_ratio
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Nat.card (sourceActorMap d).range = 6 * Nat.card (pCore 2 (sourceActorMap d).range) := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let I : Subgroup ChapterJ.S5 := f.range
  let g : B →* I := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hk : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact source_kernel d
  have hquot : Nat.card (B ⧸ pCore 2 B) = 6 := by
    rw [Nat.card_congr (leftQuotientEquiv d structural).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hquot, g.card_pCore_of_ker_isPGroup hg hk] at hc
  have hc' := card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hg).toEquiv] at hc'
  apply Nat.mul_left_cancel (Nat.card_pos (α := g.ker))
  change Nat.card g.ker * Nat.card I = Nat.card g.ker * (6 * Nat.card (pCore 2 I))
  nlinarith [hc, hc']

private theorem eight_dvd_source_image : 8 ∣ Nat.card (sourceActorMap d).range := by
  let TH : Sylow 2 F.H := T.subtype (F.invariant 1)
  let P : Sylow 2 ChapterJ.S5 := TH.mapSurjective d.qH_surjective
  have hP : (P : Subgroup ChapterJ.S5) ≤ (sourceActorMap d).range := by
    rw [Sylow.coe_mapSurjective, sourceActorMap_range]
    apply map_mono
    exact subgroupOf_mono F.H (le_sup_right : (T : Subgroup G) ≤ B)
  have hc : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    decide +kernel
  rw [← hc]
  exact card_dvd_of_le hP

/-- The actual parabolic image has order24 and its two-core has order4. -/
theorem source_image_card_unmarked
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Nat.card (sourceActorMap d).range = 24 ∧
      Nat.card (pCore 2 (sourceActorMap d).range) = 4 := by
  have hc := source_image_ratio d structural
  have h8 := eight_dvd_source_image d
  have hd : Nat.card (sourceActorMap d).range ∣ 120 := by
    convert (sourceActorMap d).range.card_subgroup_dvd_card using 1
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := (sourceActorMap d).range)).exists_card_eq
  have hb := Nat.le_of_dvd (by decide : 0 < 120) hd
  have hnle : n ≤ 4 := by
    by_contra h
    have hp : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hn] at hc
    norm_num at hp
    omega
  interval_cases n <;> norm_num at hn <;> simp_all

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08 LocalGeometry.Preparation
open Theory.SpecificGroups.Alternating
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
local notation "B" => (group F L)

private theorem source_core_image_unmarked :
    ((F.Ri L 1).subgroupOf F.H).map d.qH = (sourceActorMap d).range.pCoreIn 2 := by
  let f : B →* ChapterJ.S5 := sourceActorMap d
  let I : Subgroup ChapterJ.S5 := f.range
  let g : B →* I := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  have hk : IsPGroup 2 g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact source_kernel d
  have hp : (pCore 2 B).map g = pCore 2 I := by
    rw [← g.comap_pCore_of_ker_isPGroup hg hk]
    apply map_comap_eq_self
    rw [g.range_eq_top_of_surjective hg]
    exact le_top
  have he : ((pCore 2 B).map (B).subtype).subgroupOf F.H =
      (pCore 2 B).map (inclusion group_le_H) := by
    ext a
    constructor
    · rintro ⟨b, hb, hba⟩
      exact ⟨b, hb, Subtype.ext hba⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  change (((pCore 2 B).map (B).subtype).subgroupOf F.H).map d.qH = _
  rw [he, map_map]
  change (pCore 2 B).map f = (pCore 2 I).map I.subtype
  rw [← hp, map_map]
  rfl

private theorem root_remark (k : ChapterJ.S5) :
    root (d.remark k).naturalQuotient =
      (root d.naturalQuotient).map (MulAut.conj k).toMonoidHom := by
  rw [root, root, map_map]
  rfl

/-- Align the upper root by changing only the natural target coordinates. -/
theorem exists_upperMarking_remark
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ∃ k : ChapterJ.S5, UpperMarking (d.remark k) := by
  obtain ⟨i, hi⟩ := FivePointTwentyFour.exists_eq_stabilizer
    (sourceActorMap d).range (source_image_card_unmarked d structural).1
  obtain ⟨j, hj⟩ := borel_eq_even_stabilizer d.naturalQuotient
  have hN : normalizer d.naturalQuotient = MulAction.stabilizer ChapterJ.S5 j := by
    rw [normalizer, hj, FiveBorelCentralFactor.even_stabilizer_normalizer]
  let k : ChapterJ.S5 := Equiv.swap j i
  have hNI : (normalizer d.naturalQuotient).map (MulAut.conj k).toMonoidHom =
      (sourceActorMap d).range := by
    rw [hN, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hi]
    congr 1
    exact Equiv.swap_apply_left j i
  have hk : IsPGroup 2 (MulAut.conj k).toMonoidHom.ker := by
    rw [(MulAut.conj k).toMonoidHom.ker_eq_bot_iff.mpr (MulAut.conj k).injective]
    exact IsPGroup.of_bot
  refine ⟨k, ?_⟩
  change ((F.Ri L 1).subgroupOf F.H).map d.qH = root (d.remark k).naturalQuotient
  rw [root_remark, ← normalizer_twoCore,
    map_pCoreIn_of_ker_isPGroup _ hk, hNI]
  exact source_core_image_unmarked d
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Chapter12.Section08 LocalGeometry.Preparation
open Matrix.SpecialLinearGroup
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

@[simp] theorem sourceActorMap_remark (k : ChapterJ.S5) :
    sourceActorMap (d.remark k) = sourceActorMap d := rfl

@[simp] theorem sourceUNode_remark (k : ChapterJ.S5) :
    sourceUNode (d.remark k) = sourceUNode d := rfl

@[simp] theorem sourceCentralizerNode_remark (k : ChapterJ.S5) :
    sourceCentralizerNode (d.remark k) = sourceCentralizerNode d := rfl

@[simp] theorem sourceFiltration_remark (k : ChapterJ.S5) (hc : d.SectionCentralizer) :
    sourceFiltration (d.remark k) hc = sourceFiltration d hc := rfl

/-- One conjugator, used for all subsequent source applications. -/
def upperConjugator
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) : ChapterJ.S5 :=
  Classical.choose (exists_upperMarking_remark d structural)

/-- One coordinated datum, with the original quotient map and source action. -/
def upperRemark
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    Data T L V F W := d.remark (upperConjugator d structural)

theorem upperRemark_upperMarking
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    UpperMarking (upperRemark d structural) :=
  Classical.choose_spec (exists_upperMarking_remark d structural)

/-- Both Borel identities for the same chosen target coordinates. -/
theorem upperRemark_compatibleBorel
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    CompatibleBorel (upperRemark d structural) :=
  compatibleBorel_of_upperMarking (upperRemark d structural) structural
    (upperRemark_upperMarking d structural)

/-- The actual natural chief-count bound on the original source interval. -/
theorem sourceNaturalChief_count_of_structural
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (s : NoncentralChiefRefinement.ChiefSeries (group F L))
    (hs0 : s.head = sourcePointNode (F := F) (L := L))
    (hsl : s.last = sourceUNode d) : 2 ≤ s.noncentralTwoCount :=
  sourceNaturalChief_count_of_upperMarking (upperRemark d structural) structural uniqueness
    (upperRemark_upperMarking d structural) s hs0 hsl

/-- Lift a diagonal from the actual L₁ image; its preimage need not have order three. -/
theorem exists_diagonal_of_compatibleBorel (h : CompatibleBorel d) :
    ∃ l : F.H, (l : G) ∈ F.Li L 1 ∧ ∃ a : SL2FourNatural.F,
      ∃ ha : a ≠ 0, a ≠ 1 ∧
        d.qH l = alternatingActor d.naturalQuotient (diag2 a ha) := by
  obtain ⟨a, ha, ha1⟩ : ∃ a : SL2FourNatural.F, a ≠ 0 ∧ a ≠ 1 := by decide +kernel
  have hm : alternatingActor d.naturalQuotient (diag2 a ha) ∈ borel d.naturalQuotient :=
    mem_map.mpr ⟨diag2 a ha, diag_mem_rankOneBorel a ha, rfl⟩
  rw [← h.left_image] at hm
  obtain ⟨l, hl, he⟩ := hm
  exact ⟨l, hl, a, ha, ha1, he⟩

/-- The earlier seed-fixing identity is retained as its own genuine source input. -/
theorem upperRemark_localActors
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (seed_fixed : ∀ r : F.H, (r : G) ∈ F.Ri L 1 → ∀ v : F.U, (v : G) ∈ V →
      d.action r (d.conjugationSection.coordinates v).toAdd =
        (d.conjugationSection.coordinates v).toAdd) :
    MarkedSpans.LocalActors (upperRemark d structural) :=
  ⟨seed_fixed, exists_diagonal_of_compatibleBorel (upperRemark d structural)
    (upperRemark_compatibleBorel d structural)⟩

/-- The same diagonal supplies the permitted-choice cubic with upper parameter zero. -/
theorem upperRemark_localCubic
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    PermittedChoice.ActorOrbits.LocalCubic (upperRemark d structural) := by
  obtain ⟨l, hl, a, ha, ha1, he⟩ := exists_diagonal_of_compatibleBorel
    (upperRemark d structural) (upperRemark_compatibleBorel d structural)
  refine ⟨l, hl, a, ha, ha1, 0, ?_⟩
  have h0 : SL2FourNatural.upper 0 = 1 := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [SL2FourNatural.upper]
  simpa only [h0, one_mul, inv_one, mul_one] using he
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
