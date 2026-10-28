module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightForward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BaumannImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FourOffenderImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PairExclusion

/-!
# Excluding the two-transposition small mover above distance four

The surviving image-eight radical has a unique order-four small mover.
Every maximum elementary image lies in that mover, so its elementary
Thompson image equals the mover image. Fixed-space control on the whole
moved cover gives the same Baumann image. Their supplements by the entire
two-core are therefore the actual small mover, and Thompson and Baumann
heredity lift its image normalizer to the literal characteristic subgroups.

For the two-transposition mover, an overlapping cubic gives a preimage
with an index-three Sylow whose Baumann subgroup is the original Baumann
subgroup. An explicit fixed vector in each of the natural and augmentation
covers has a cubic translate moved by the original Thompson subgroup.
This constructs the cubic local class. Normalizer generation and C.1.18
then give either a forbidden characteristic subgroup normal in the whole
overgroup or a short component by C.1.21. The latter forces distance two,
contradicting distance greater than four.

Consequently the mixed and even mover branches exhaust every distance
above four. The existing radius-escape and strict small-image arguments
now have no mover-model premise. Their literal original-radical consumer
retains index two over the selected replacement edge core and the same
transporter for both initial vertices and every overlapping walk vertex.
Both cover orders, sixteen and thirty-two, and full central attachments
are retained; no exceptional-graph identification is made.

The large-critical-image strict bound, image-eight terminal contradiction
and general distance-four estimates remain necessary for LargeDistanceInput.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.1), printed pp.912--913, and (5.7)--(5.9), pp.919--922;
Aschbacher--Smith C.1.18 and C.1.21, printed pp.127--129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightBaumann
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)

private theorem elementary_card_le_four (E A : Subgroup S)
    (hE : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hAE : A ≤ E) (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 4 := by
  have hneq : A ≠ E := fun he => hne (he ▸ hA)
  have hi : 1 < A.relIndex E := by
    have hp : 0 < A.relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn : A.relIndex E ≠ 1 := fun he => hneq (le_antisymm hAE (relIndex_eq_one.mp he))
    omega
  have hm := relIndex_mul_relIndex (⊥ : Subgroup S) A E bot_le hAE
  rw [relIndex_bot_left,relIndex_bot_left,hE] at hm
  nlinarith

private theorem offender_le_cube (E A : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hE : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hAE : A ≤ E) (ho : IsOffender ρ A) :
    A ≤ E ⊓ (D 6).map (MulAut.conj u).toMonoidHom := by
  have hc := elementary_card_le_four E A hE hne hAE ho.1.2
  by_cases hlarge : 4 ≤ Nat.card A
  · have hr : rank A = 2 := by rw [rank,show Nat.card A = 4 by omega]; decide
    exact ((EightSmallMovers.conjugate_eight_model E u hES hE hne).2
      A hAE hlarge (ho.2.trans_eq hr)).le
  · have hr : rank A ≤ 1 := by
      unfold rank
      interval_cases hh : Nat.card A <;> norm_num at *
    exact le_inf hAE ((SylowSmallMovers.small_image_centralized A u
      (hAE.trans hES) (ho.2.trans hr)).1)

private abbrev pairCore : core (Fin 6) :=
  ⟨![1,1,0,0,0,0], by norm_num [mem_core,Fin.sum_univ_succ]⟩
private abbrev swap : S := Equiv.swap 0 1

private theorem pair_core_fixed (a : S) (ha : a ∈ disjointTranspositions 6 2) :
    coreRepresentation (Fin 6) a pairCore = pairCore := by
  obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (2 : Fin 4) a).mp ha
  exact (by decide +kernel : ∀ i : Fin 4,
    coreRepresentation (Fin 6) (initialWords 2 i) pairCore = pairCore) i

private theorem pair_natural_moved :
    ρ swap (ρ PairExclusion.c (coreToNatural (Fin 6) pairCore)) ≠
      ρ PairExclusion.c (coreToNatural (Fin 6) pairCore) := by
  have he : coreToNatural (Fin 6) pairCore =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 0 1 := by
    apply Subtype.ext
    apply congrArg (Submodule.mkQ (constants (Fin 6)))
    ext i
    fin_cases i <;> decide
  rw [he]
  open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry in
    rw [pairVector_map,pairVector_map]
  change Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 0 4 ≠
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 1 4
  intro hh
  have heq := (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector_eq_iff
    (by decide : (0 : Fin 6) ≠ 4) (by decide : (1 : Fin 6) ≠ 4)).mp hh
  exact (by decide +kernel : Theory.SpecificGroups.SymmetricSix.pair 0 4 ≠
    Theory.SpecificGroups.SymmetricSix.pair 1 4) heq

private theorem pair_cover_choice {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) S V) (hσ : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (g : S) :
    ∃ v : V,
      (∀ b ∈ (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom, σ b v = v) ∧
      σ ((MulAut.conj g) swap) (σ ((MulAut.conj g) PairExclusion.c) v) ≠
        σ ((MulAut.conj g) PairExclusion.c) v := by
  have hex : ∃ v : V, (∀ b ∈ disjointTranspositions 6 2, σ b v = v) ∧
      σ swap (σ PairExclusion.c v) ≠ σ PairExclusion.c v := by
    rcases hσ with ⟨E,hE⟩ | ⟨E,hE⟩
    · refine ⟨E.symm (coreToNatural (Fin 6) pairCore),?_,?_⟩
      · intro b hb
        apply E.injective
        rw [hE,E.apply_symm_apply]
        simp only [MonoidHom.id_apply,←coreToNatural_equivariant,pair_core_fixed b hb]
      · intro hh
        apply pair_natural_moved
        have hh' := congrArg E hh
        simpa only [hE,MonoidHom.id_apply,E.apply_symm_apply] using hh'
    · refine ⟨E.symm pairCore,?_,?_⟩
      · intro b hb
        apply E.injective
        simpa only [hE,MonoidHom.id_apply,E.apply_symm_apply] using pair_core_fixed b hb
      · intro hh
        apply pair_natural_moved
        have hh' := congrArg (fun v => coreToNatural (Fin 6) (E v)) hh
        simpa only [hE,MonoidHom.id_apply,E.apply_symm_apply,coreToNatural_equivariant] using hh'
  obtain ⟨v,hv,hm⟩ := hex
  have conjugate (a : S) (v : V) : σ ((MulAut.conj g) a) (σ g v) = σ g (σ a v) := by
    simp only [MulAut.conj_apply,map_mul,Module.End.mul_apply,σ.inv_self_apply]
  refine ⟨σ g v,?_,?_⟩
  · rintro b ⟨a,ha,rfl⟩
    change σ ((MulAut.conj g) a) (σ g v) = σ g v
    rw [conjugate,hv a ha]
  · simp only [conjugate]
    intro he
    have hh := congrArg (σ g⁻¹) he
    exact hm (by simpa only [σ.inv_self_apply] using hh)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Both characteristic control groups have exactly the actual small-mover image.
The whole two-core is retained in the resulting supplements. -/
theorem characteristic_images_knownSimple (hb : 4 < replacementDistance h d) :
    let π := SourceReduction.projection h e hz hn d
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    (Stellmacher.elementaryAbelianMaxJ d.radical).map π = J.map π ∧
      (ChapterB.baumann d.radical).map π = J.map π ∧
      pCore 2 d.overgroup ⊔ Stellmacher.elementaryAbelianMaxJ d.radical = J ∧
      pCore 2 d.overgroup ⊔ ChapterB.baumann d.radical = J := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let π := s.projection
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  let A := (Stellmacher.elementaryAbelianMaxJ d.radical).map π
  let B := (ChapterB.baumann d.radical).map π
  let E := d.radical.map π
  obtain ⟨u,hN,_,_,hJ,hQi,_,hJfix,_⟩ := EightSmallMovers.radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  obtain ⟨_,hne,_,hE⟩ := SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hne hE
  have hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom :=
    (map_mono d.radical.le_normalizer).trans_eq hN
  have hJcard : Nat.card (J.map π) = 4 := by
    rw [←s.projection_kernel,relIndex_ker] at hQi
    rw [s.projection_kernel] at hQi
    exact hQi
  have hAJ : A ≤ J.map π := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro F hF
    by_cases hFQ : F ≤ pCore 2 d.overgroup
    · intro f hf
      change π f ∈ J.map π
      have he : π f = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [s.projection_kernel]
        exact hFQ hf
      rw [he]; exact one_mem _
    · have ho := SourceReduction.Cover.maxElementary_natural_offender h e hz hn d F hF hFQ
      rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at ho
      have hh := offender_le_cube E (F.map π) u hES hE hne (map_mono hF.1) ho
      rw [←hJ] at hh
      exact map_le_iff_le_comap.mp hh
  have hJA : J.map π = A := by
    apply (eq_of_le_of_card_ge hAJ ?_).symm
    rw [hJcard]
    have hh := large_distance_thompson_image_four_le_knownSimple
      (e := e) (hz := hz) (hn := hn) (d := d) (by omega : 2 < replacementDistance h d)
    rwa [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hh
  have hAB : A ≤ B := map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann d.radical)
  have hBE : B ≤ E := map_mono inf_le_left
  have hBcard : 4 ≤ Nat.card B := by
    rw [←hJcard,hJA]
    exact card_le_of_le hAB
  let := replacementMoved_normal h d
  have hpow : 2 ^ fixedCodim (coverAction s) (J.map π) = 4 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) π s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hJfix
    exact hJfix
  have hJco : fixedCodim (coverAction s) A ≤ 2 := by
    rw [←hJA]
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow.le
  have hdim := Submodule.finrank_mono (cover_thompson_fixed_le_baumann_fixed s)
  have hAdim := fixedCodim_add_finrank (coverAction s) A
  have hBdim := fixedCodim_add_finrank (coverAction s) B
  have hBco : fixedCodim (coverAction s) B ≤ 2 := by
    change Module.finrank (ZMod 2) (fixedSpace (coverAction s) A) ≤
      Module.finrank (ZMod 2) (fixedSpace (coverAction s) B) at hdim
    omega
  have hnat : fixedCodim ρ B ≤ 2 := by
    simpa only [map_id] using ((cover_model s).fixedCodim_bounds B).1.trans hBco
  have hBJ : B = J.map π := by
    rw [hJ]
    exact (EightSmallMovers.conjugate_eight_model E u hES hE hne).2 B hBE hBcard hnat
  have hkJ : π.ker ≤ J := by
    rw [s.projection_kernel]
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  have supplement (C : Subgroup d.overgroup) (hC : C.map π = J.map π) :
      pCore 2 d.overgroup ⊔ C = J := by
    have hh := congrArg (Subgroup.comap π) hC
    rw [comap_map_eq,comap_map_eq,sup_eq_left.mpr hkJ,s.projection_kernel] at hh
    exact (sup_comm _ _).trans hh
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  exact ⟨hJA.symm,hBJ,supplement _ hJA.symm,supplement _ hBJ⟩

include e hz hn in
/-- The full preimage of the mover-image normalizer is the actual normalizer
of each characteristic control subgroup, even when the core is not contained
in those subgroups. -/
theorem characteristic_normalizers_knownSimple (hb : 4 < replacementDistance h d) :
    let π := SourceReduction.projection h e hz hn d
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    normalizer (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) =
        normalizer (J : Set d.overgroup) ∧
      normalizer (ChapterB.baumann d.radical : Set d.overgroup) =
        normalizer (J : Set d.overgroup) ∧
      normalizer (J : Set d.overgroup) = (normalizer (J.map π : Set S)).comap π := by
  let π := SourceReduction.projection h e hz hn d
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hπ : Function.Surjective π := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using s.surjective
  have hkR : π.ker ≤ d.radical := by
    rw [SourceReduction.projection_kernel]
    exact replacement_core_le_radical h d
  obtain ⟨hA,_,hQA,hQB⟩ := characteristic_images_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hkJ : π.ker ≤ J := by
    rw [SourceReduction.projection_kernel]
    exact le_sup_left.trans_eq hQA
  have hN : normalizer (J : Set d.overgroup) = (normalizer (J.map π : Set S)).comap π := by
    rw [comap_normalizer_eq_of_surjective _ hπ,comap_map_eq,sup_eq_left.mpr hkJ]
  have hAN : normalizer (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) =
      normalizer (J : Set d.overgroup) := by
    rw [hN,←hA,Stellmacher.normalizer_comap_map_maxJ d.radical π hπ hkR]
  have hBhered : ChapterB.baumann J = ChapterB.baumann d.radical :=
    Stellmacher.baumann_eq_of_intermediate d.radical J (le_sup_right.trans_eq hQB)
      (SmallMover.join_le _ _ _ _)
  have hAhered : Stellmacher.elementaryAbelianMaxJ (ChapterB.baumann d.radical) =
      Stellmacher.elementaryAbelianMaxJ d.radical :=
    Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate d.radical _
      (ChapterB.elementaryAbelianMaxJ_le_baumann d.radical) inf_le_left
  refine ⟨hAN,le_antisymm ?_ ?_,hN⟩
  · have hh := Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ (ChapterB.baumann d.radical)
    rwa [hAhered,hAN] at hh
  · rw [←hBhered]
    exact Stellmacher.normalizer_le_normalizer_baumann J

include e hz hn in
/-- In the two-transposition mover branch, a cubic preimage has an actual
index-three Sylow whose Baumann subgroup maps onto the original Baumann
subgroup. Its residual and that Baumann normalizer generate the overgroup. -/
private theorem pair_local_selection_knownSimple
    (hb : 4 < replacementDistance h d) (g : S)
    (hpair : (SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (SourceReduction.projection h e hz hn d) =
        (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom) :
    ∃ (F : Subgroup d.overgroup) (W : Sylow 2 F) (z : S),
      pCore 2 d.overgroup ≤ F ∧
      (W : Subgroup F).index = 3 ∧
      (ChapterB.baumann (W : Subgroup F)).map F.subtype = ChapterB.baumann d.radical ∧
      (pResidual 2 F).map F.subtype ⊔ normalizer
        (ChapterB.baumann d.radical : Set d.overgroup) = ⊤ ∧
      Stellmacher.SectionTwo.Hypotheses F ∧ orderOf z = 3 ∧
      ((pResidual 2 F).map F.subtype).map (SourceReduction.projection h e hz hn d) = zpowers z ∧
      (W : Subgroup F).map F.subtype =
        SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 ∧
      z = (MulAut.conj g) PairExclusion.c := by
  let π := SourceReduction.projection h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  let B := J.map π
  let z := (MulAut.conj g) PairExclusion.c
  have hπ : Function.Surjective π := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using s.surjective
  have hk : π.ker = pCore 2 d.overgroup := SourceReduction.projection_kernel h e hz hn d
  obtain ⟨_,_,_,hQB⟩ := characteristic_images_knownSimple (e := e) (hz := hz) (hn := hn) hb
  have hQJ : pCore 2 d.overgroup ≤ J := le_sup_left.trans_eq hQB
  have hJR : J ≤ d.radical := SmallMover.join_le _ _ _ _
  have hBJ : ChapterB.baumann J = ChapterB.baumann d.radical :=
    Stellmacher.baumann_eq_of_intermediate d.radical J (le_sup_right.trans_eq hQB) hJR
  have hpJ : IsPGroup 2 J := (replacement_radical_isPGroup h d).to_le hJR
  change B = (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom at hpair
  have hB : Nat.card B = 4 := by
    rw [hpair,card_map_of_injective (MulAut.conj g).injective]
    exact card_disjointTranspositions (2 : Fin 4)
  obtain ⟨hz3,hnB,hcard,hgen⟩ := PairExclusion.conjugate_local g
  change orderOf z = 3 at hz3
  rw [←hpair] at hnB hcard hgen
  let D := zpowers z ⊔ B
  let F := D.comap π
  have hJF : J ≤ F := fun r hr => mem_sup_right (mem_map_of_mem π hr)
  have hQF : pCore 2 d.overgroup ≤ F := hQJ.trans hJF
  have hF : F.map π = D := map_comap_eq_self_of_surjective hπ D
  have hindex : (J.subgroupOf F).index = 3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup S) B D bot_le le_sup_right
    rw [relIndex_bot_left,relIndex_bot_left,hB,hcard] at hh
    have hi := relIndex_map_map π J F
    rw [hk,sup_eq_left.mpr hQJ,sup_eq_left.mpr hQF,hF] at hi
    change J.relIndex F = 3
    change B.relIndex D = J.relIndex F at hi
    omega
  let W := hpJ.comap_subtype.toSylow (show ¬2 ∣ (J.subgroupOf F).index by rw [hindex]; decide)
  let Y := (pResidual 2 F).map F.subtype
  have hW : (W : Subgroup F).map F.subtype = J := map_subgroupOf_eq_of_le hJF
  have hBW : (ChapterB.baumann (W : Subgroup F)).map F.subtype = ChapterB.baumann d.radical := by
    rw [ChapterC.RankOne.SymmetricSix.baumann_map F F.subtype F.subtype_injective,hW,hBJ]
  have hgenF : F ⊔ normalizer (ChapterB.baumann d.radical : Set d.overgroup) = ⊤ := by
    have hn := (characteristic_normalizers_knownSimple (e := e) (hz := hz) (hn := hn) hb).2
    have hN : normalizer (ChapterB.baumann d.radical : Set d.overgroup) =
        (normalizer (B : Set S)).comap π := hn.1.trans hn.2
    have hm : (F ⊔ normalizer (ChapterB.baumann d.radical : Set d.overgroup)).map π = ⊤ := by
      rw [Subgroup.map_sup,hF,hN,map_comap_eq_self_of_surjective hπ]
      apply top_unique
      rw [←hgen]
      exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
    have hh := congrArg (Subgroup.comap π) hm
    rwa [comap_map_eq,hk,sup_eq_left.mpr (hQF.trans le_sup_left),comap_top] at hh
  have hYJ : Y ⊔ J = F := by
    have hh := congrArg (Subgroup.map F.subtype) (pResidual_sup_sylow_eq_top W)
    rwa [Subgroup.map_sup,hW,←MonoidHom.range_eq_map,range_subtype] at hh
  have hJN : J ≤ normalizer (ChapterB.baumann d.radical : Set d.overgroup) := by
    rw [←hBJ]
    exact J.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann J)
  have hgenY : Y ⊔ normalizer (ChapterB.baumann d.radical : Set d.overgroup) = ⊤ := by
    rw [←hgenF,←hYJ,sup_assoc,sup_of_le_right hJN]
  have hsolv : Group.IsSolvable F := by
    let : Group.IsNilpotent (W : Subgroup F) := W.isPGroup'.isNilpotent
    exact (W : Subgroup F).isSolvable_of_index_le_four (by change (J.subgroupOf F).index ≤ 4; omega)
  let f := π.subgroupComap D
  have hf : Function.Surjective f := π.subgroupComap_surjective_of_surjective D hπ
  have heven : Even (Nat.card F) := by
    apply even_iff_two_dvd.mpr
    have hh := card_dvd_of_surjective f hf
    change Nat.card D ∣ Nat.card F at hh
    rw [hcard] at hh
    exact (by decide : 2 ∣ 12).trans hh
  have hself := centralizer_pCore_le_of_pCore_le F (replacement_self_centralizing h d) hQF
  refine ⟨F,W,z,hQF,hindex,hBW,hgenY,⟨hsolv,heven,hself⟩,hz3,?_,hW,rfl⟩
  let C := (zpowers z).subgroupOf D
  let E := B.subgroupOf D
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le (zpowers z).le_normalizer hnB)
  have hC : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro t _
    apply mem_pResidual_of_orderOf_coprime
    have hc : Nat.card C = 3 := (Nat.card_congr (subgroupOfEquivOfLe
      (show zpowers z ≤ D from le_sup_left)).toEquiv).trans (by rw [Nat.card_zpowers,hz3])
    exact (show Nat.Coprime 2 (Nat.card C) by rw [hc]; decide).of_dvd_right (orderOf_dvd_natCard t)
  have hE : IsPGroup 2 E := (hpJ.map π).comap_subtype
  have hCE : C ⊔ E = ⊤ := by
    rw [←subgroupOf_sup (show zpowers z ≤ D from le_sup_left) (show B ≤ D from le_sup_right)]
    exact subgroupOf_self D
  have hres : pResidual 2 D = C := pResidual_eq_of_isPPerfect_sup C E hC hE hCE
  have he : π.comp F.subtype = D.subtype.comp f := rfl
  rw [map_map,he,←map_map,map_pResidual_of_surjective 2 f hf,hres]
  exact map_subgroupOf_eq_of_le (show zpowers z ≤ D from le_sup_left)

include e hz hn in
private theorem pair_local_movement (hb : 4 < replacementDistance h d) (g : S)
    (hpair : (SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (SourceReduction.projection h e hz hn d) =
        (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom)
    (F : Subgroup d.overgroup) (W : Sylow 2 F)
    (hQF : pCore 2 d.overgroup ≤ F)
    (hW : (W : Subgroup F).map F.subtype =
      SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4)
    (hzF : (MulAut.conj g) PairExclusion.c ∈ F.map (SourceReduction.projection h e hz hn d)) :
    ¬ Stellmacher.elementaryAbelianMaxJ (W : Subgroup F) ≤ centralizer
      (normalClosure (Stellmacher.omegaOneCenterAmbient (W : Subgroup F) : Set F) : Set F) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let π := s.projection
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  have hpair' : J.map π = (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom := by
    dsimp only [π,J]
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨hA,_,hQA,_⟩ := characteristic_images_knownSimple (e := e) (hz := hz) (hn := hn) hb
  have hAJ : Stellmacher.elementaryAbelianMaxJ d.radical ≤ J := le_sup_right.trans_eq hQA
  have hQJ : pCore 2 d.overgroup ≤ J := le_sup_left.trans_eq hQA
  have hhered : Stellmacher.elementaryAbelianMaxJ J = Stellmacher.elementaryAbelianMaxJ d.radical :=
    Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate d.radical J hAJ (SmallMover.join_le _ _ _ _)
  change (W : Subgroup F).map F.subtype = J at hW
  have hA' : (Stellmacher.elementaryAbelianMaxJ d.radical).map π = J.map π := by
    dsimp only [π,J]
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hJW : (Stellmacher.elementaryAbelianMaxJ (W : Subgroup F)).map (π.comp F.subtype) =
      (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom := by
    rw [←map_map,←Stellmacher.elementaryAbelianMaxJ_map_injective F.subtype F.subtype_injective,
      hW,hhered,hA',hpair']
  obtain ⟨v,hv,hm⟩ := pair_cover_choice (coverAction s) (cover_model s) g
  have hUQ : replacementMoved d ≤ pCore 2 d.overgroup := fun x hx =>
    ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hx)).1
  let u : F := ⟨v.toMul,hQF (hUQ v.toMul.property)⟩
  have huW : u ∈ (W : Subgroup F) := by
    have hh : (u : d.overgroup) ∈ (W : Subgroup F).map F.subtype := by
      rw [hW]; exact hQJ (hUQ v.toMul.property)
    obtain ⟨w,hw,he⟩ := hh
    exact (show w = u from Subtype.ext he) ▸ hw
  have huZ : u ∈ Stellmacher.omegaOneCenterAmbient (W : Subgroup F) := by
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨huW,?_,?_⟩
    · apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian _ v.toMul.property
    · intro a ha
      apply Subtype.ext
      have hai : π (a : d.overgroup) ∈ (disjointTranspositions 6 2).map
          (MulAut.conj g).toMonoidHom := by
        rw [←hpair',←hW,map_map]
        exact mem_map_of_mem (π.comp F.subtype) ha
      have hh := congrArg (fun v : Additive (replacementMoved d) => (v.toMul : d.overgroup))
        (hv _ hai)
      dsimp only [π] at hh
      rw [coverAction_conjugate] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  have hzF' : (MulAut.conj g) PairExclusion.c ∈ F.map π := by
    dsimp only [π]
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨y,hy,hyπ⟩ := hzF'
  let yF : F := ⟨y,hy⟩
  let w : F := yF*u*yF⁻¹
  have hw : w ∈ normalClosure (Stellmacher.omegaOneCenterAmbient (W : Subgroup F) : Set F) :=
    normalClosure_normal.conj_mem _ (subset_normalClosure huZ) yF
  have hr : (MulAut.conj g) swap ∈
      (Stellmacher.elementaryAbelianMaxJ (W : Subgroup F)).map (π.comp F.subtype) := by
    rw [hJW]
    exact mem_map_of_mem _ ((mem_disjointTranspositions_iff (2 : Fin 4) _).mpr ⟨1,rfl⟩)
  obtain ⟨a,ha,haπ⟩ := hr
  change s.projection (a : d.overgroup) = _ at haπ
  intro hcent
  have haw : (a : d.overgroup) * (w : d.overgroup) * (a : d.overgroup)⁻¹ = (w : d.overgroup) := by
    have hh := congrArg (fun x : F => (x : d.overgroup)) (hcent ha w hw)
    change (w : d.overgroup) * (a : d.overgroup) = (a : d.overgroup) * (w : d.overgroup) at hh
    rw [←hh,mul_inv_cancel_right]
  apply hm
  apply Additive.toMul.injective
  apply Subtype.ext
  have hyv : ((coverAction s ((MulAut.conj g) PairExclusion.c) v).toMul : d.overgroup) =
      (w : d.overgroup) := by
    rw [←hyπ,coverAction_conjugate]
    rfl
  rw [←haπ,coverAction_conjugate,hyv]
  exact haw

include e hz hn in
/-- The two-transposition small mover is impossible above distance four.
The cubic local class is built on the original Baumann subgroup, retaining
its core supplement and both whole moved covers. -/
theorem pair_mover_false_knownSimple (hb : 4 < replacementDistance h d)
    (hpair : IsConjugateTo
      ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
        (SourceReduction.projection h e hz hn d)) (disjointTranspositions 6 2)) : False := by
  obtain ⟨g,hg⟩ := hpair
  obtain ⟨F,W,z,hQF,hi,hBW,hgen,hF,hz3,hYπ,hW,hzsel⟩ :=
    pair_local_selection_knownSimple (e := e) (hz := hz) (hn := hn) hb g hg
  let Y := (pResidual 2 F).map F.subtype
  let B := ChapterB.baumann (W : Subgroup F)
  let H := pResidual 2 F ⊔ B
  let i := F.subtype.comp H.subtype
  have hzF : (MulAut.conj g) PairExclusion.c ∈ F.map (SourceReduction.projection h e hz hn d) := by
    rw [←hzsel]
    exact (map_mono (map_subtype_le _)) (hYπ.symm ▸ mem_zpowers z)
  have hmove := pair_local_movement (e := e) (hz := hz) (hn := hn) hb g hg F W hQF hW hzF
  have hfit : generalizedFitting F = pCore 2 F :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 hF.centralizer_twoCore_le
  have hlocal := ChapterC.RankOne.FiveBlockSource.cubic_omega_inLocalClass W hi hfit hmove
  let S₀ := ChapterB.baumann d.radical
  let f : B →* S₀ := (F.subtype.comp B.subtype).codRestrict S₀
    (fun x => by
      change F.subtype (x : F) ∈ ChapterB.baumann d.radical
      rw [←hBW]
      exact mem_map_of_mem _ x.property)
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : S₀ => (z : d.overgroup)) he
    · intro b
      have hb : (b : d.overgroup) ∈ B.map F.subtype := by rw [hBW]; exact b.property
      obtain ⟨x,hx,he⟩ := hb
      exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let E := (MulEquiv.ofBijective f hf).symm
  let emb : S₀ →* H := (inclusion (show B ≤ H from le_sup_right)).comp E.toMonoidHom
  have hemb : i.comp emb = S₀.subtype := by
    apply MonoidHom.ext
    intro b
    exact congrArg (fun z : S₀ => (z : d.overgroup)) ((MulEquiv.ofBijective f hf).apply_symm_apply b)
  have hloc : ChapterC.GlaubermanNiles.InLocalClass emb := hlocal.precomp_equiv E
  have hir : i.range = Y ⊔ S₀ := by
    rw [MonoidHom.range_comp,range_subtype,Subgroup.map_sup,hBW]
  have hres : (pResidual 2 H).map i = Y := by
    let C := (pResidual 2 F).subgroupOf H
    let D := B.subgroupOf H
    have hc : IsPPerfect 2 C := (isPPerfect_pResidual 2).of_surjective
      (subgroupOfEquivOfLe (show pResidual 2 F ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show pResidual 2 F ≤ H from le_sup_left)).symm.surjective
    have hd : IsPGroup 2 D := (W.isPGroup'.to_le (show B ≤ (W : Subgroup F) from inf_le_left)).comap_subtype
    have hCD : C ⊔ D = ⊤ := by
      rw [←subgroupOf_sup (show pResidual 2 F ≤ H from le_sup_left) (show B ≤ H from le_sup_right),subgroupOf_self]
    have hh := pResidual_eq_of_isPPerfect_sup C D hc hd hCD
    rw [←map_map,hh,map_subgroupOf_eq_of_le (show pResidual 2 F ≤ H from le_sup_left)]
  have hgen' : i.range ⊔ normalizer (S₀ : Set d.overgroup) = ⊤ := by
    rw [hir,sup_assoc,sup_of_le_right S₀.le_normalizer]
    exact hgen
  let := replacementComponent_normal h d
  let := h.relative_core_quasisimple e
  let fL := subgroupOfEquivOfLe (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  let : IsQuasisimple ((replacementComponent d) ⧸ pCore 2 (replacementComponent d)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ fL (pCore_map_iso 2 fL)).symm
  have hcomp : (replacementComponent d).IsCComponent :=
    h.component.subgroupOf (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
  have hp : IsPPerfect 2 (replacementComponent d) := by
    have he : pResidual 2 d.overgroup = replacementComponent d := replacement_residual h d
    rw [←he]
    exact isPPerfect_pResidual 2
  have hfL := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (subnormal_core_selfCentralizing (replacement_self_centralizing h d)
      (replacementComponent d) hcomp.subnormal)
  have hYL : Y ≤ replacementComponent d := (map_pResidual_le 2 F.subtype).trans_eq (replacement_residual h d)
  have hQY : pCore 2 d.overgroup ≤ normalizer (Y : Set d.overgroup) :=
    hQF.trans (F.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F (pResidual 2 F)))
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hnc := ChapterC.RankOne.SymmetricSix.cubic_not_central_in_component
    (replacementComponent d) Y hcomp.subnormal hYL s.projection s.projection_kernel.symm.le
    s.component_image z hz3 (by rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s])
  let : Nontrivial S₀ := (nontrivial_iff_ne_bot _).mpr
    (ChapterC.RankOne.SymmetricSix.baumann_ne_bot d.radical (replacement_radical_isPGroup h d)
      (replacement_radical_ne_bot h d))
  have hpS : IsPGroup 2 S₀ := (replacement_radical_isPGroup h d).to_le inf_le_left
  obtain ⟨D,hD⟩ := ChapterC.GlaubermanNiles.exists_universal_characteristicPair.{u,u}
    hpS (ChapterC.RankOne.SymmetricSix.baumann_intrinsic_fixed d.radical)
  have halt := ChapterC.RankOne.GlaubermanArgument.embedded_local_seed_alternative
    S₀ (replacementComponent d) emb i (F.subtype_injective.comp H.subtype_injective)
    hemb hloc D hD hgen' (by rw [hres]; exact hYL) hcomp.subnormal hp hfL
    (by rw [hres]; exact hQY) (by rw [hres]; exact hnc)
  rcases halt with hnormal | hblock
  · exact no_normal_characteristic_baumann (h := h) hnormal
  · have heq := distance_eq_two_of_short_component (e := e) (hz := hz) (hn := hn) hblock.short
    omega

include e hz hn in
/-- Only the mixed and even movers survive above four. -/
theorem three_duad_mover_knownSimple (hb : 4 < replacementDistance h d) :
    EightSelection.ThreeDuadMover h e hz hn d :=
  (EightSelection.radical_mover_image_cases_knownSimple (e := e) (hz := hz) (hn := hn) hb).resolve_left
    (pair_mover_false_knownSimple (e := e) (hz := hz) (hn := hn) hb)

include e hz hn in
/-- Every critical radius escapes its predecessor core on the actual
replacement graph, with no small-mover branch premise. -/
theorem criticalEscape_knownSimple (hb : 4 < replacementDistance h d) :
    Factorization.CriticalEscape d.radical (replacementGeometry h d) :=
  EightStrictShift.three_duad_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn)
    hb (three_duad_mover_knownSimple (e := e) (hz := hz) (hn := hn) hb)

include e hz hn in
/-- The forward bound for every small critical image, at every component
vertex, now has no mover-selection premise. -/
theorem small_forward_slice_strict_knownSimple (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4) :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) :=
  EightForward.three_duad_small_forward_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
    (three_duad_mover_knownSimple (e := e) (hz := hz) (hn := hn) hb) p hsmall

include e hz hn in
/-- The literal original radical keeps index two over the selected edge core;
the same conjugator gives both initial vertices and all overlapping walk vertices. -/
theorem original_radical_strict_backward_knownSimple (hb : 4 < replacementDistance h d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ x ∈ stabilizer d.radical (alpha d.radical),
      let c := act d.radical x (p.walk.getVert 2)
      let t := act d.radical x (beta d.radical)
      (Q d.radical t).relIndex (T.map (MulAut.conj x⁻¹).toMonoidHom) = 2 ∧
        Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i :=
  EightForward.original_radical_three_duad_strict_backward_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
    (three_duad_mover_knownSimple (e := e) (hz := hz) (hn := hn) hb) p hsmall hfirst

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightBaumann
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
