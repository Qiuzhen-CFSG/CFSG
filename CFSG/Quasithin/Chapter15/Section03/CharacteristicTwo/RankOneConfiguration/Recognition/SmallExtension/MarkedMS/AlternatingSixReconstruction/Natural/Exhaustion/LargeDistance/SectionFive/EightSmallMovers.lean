module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowWholeCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage

/-!
# Small movers in the surviving non-elementary image-eight branch

The image-sixteen and elementary exclusions leave quotient image eight
above distance four. Its intersection with the Sylow three-pair subgroup
has order four. Any subgroup of order at least four with small fixed
codimension contains the unique nontrivial Sylow square. Two independent
fixed duad vectors then force it into that intersection. This proves
uniqueness of the maximum small mover, without enumerating subgroups or
identifying the replacement radical with its larger Sylow normalizer.

The literal radical's small mover is the intersection with the normalizer's
small mover. It has quotient order four, radical index two and fixed index
four on either whole moved cover; the entire radical has fixed index eight.
Transport gives the same statements on every actual replacement edge,
quadratic action, and control of the full critical kernel. Unequal adjacent
movers generate the edge core, have intersection index four, and have fixed
index eight on the opposite whole cover. When the critical line moves, an
actual neighboring-mover element gives a second critical path whose full
kernels generate the starting seed.

The original-radical application retains its literal embedding and records
small-mover index four in the restricted original Sylow. Both moving covers
and all central attachments remain. The image-eight backward selection and
terminal contradiction, and the distance-four whole-core bounds, are still
required for the unconditional distance-two conclusion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the small-mover family in (5.0), (5.5)--(5.7), printed pp.912,917--919.
The six-letter coordinates use the existing B.3.2--4 offender model. The
private imports reuse local model, cover and graph transports without
changing their public interfaces.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)
private abbrev z : S := kleinFirst 6 (by decide)

private theorem square_in_large_subgroup (E A : Subgroup S)
    (hES : E ≤ sylowCarrier) (hE : Nat.card E = 8)
    (hne : ¬ IsElementaryAbelian 2 E) (hAE : A ≤ E) (hA : 4 ≤ Nat.card A) :
    z ∈ A := by
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hsq⟩ := hex
  obtain ⟨i,hi⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  have hxz : x^2=z := (hi ▸ NonsylowImage.sylow_square_certificate i).resolve_left hsq
  have hm := relIndex_mul_relIndex (⊥ : Subgroup S) A E bot_le hAE
  rw [relIndex_bot_left,relIndex_bot_left,hE] at hm
  have hp : 0 < A.relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hi : A.relIndex E = 1 ∨ A.relIndex E = 2 := by
    have hh : A.relIndex E ≤ 2 := by nlinarith
    omega
  rcases hi with hi | hi
  · exact relIndex_eq_one.mp hi (hxz ▸ E.pow_mem hx 2)
  · let : (A.subgroupOf E).Normal := normal_of_index_eq_two hi
    have hh := (A.subgroupOf E).pow_index_mem ⟨x,hx⟩
    change x ^ A.relIndex E ∈ A at hh
    rwa [hi,hxz] at hh

private theorem small_with_square_le_cube (A : Subgroup S) (hAS : A ≤ sylowCarrier)
    (hz : z ∈ A) (hsmall : fixedCodim ρ A ≤ 2) : A ≤ D 6 := by
  have hdim : 2 ≤ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    have hh := fixedCodim_add_finrank ρ A
    rw [finrank_natural_even (Fin 6) (by decide),Fintype.card_fin] at hh
    omega
  have hne : fixedSpace ρ A ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hdim
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw : ∃ w ∈ fixedSpace ρ A, w ∉ Submodule.span (ZMod 2) {v} := by
    by_contra! hh
    have hle : fixedSpace ρ A ≤ Submodule.span (ZMod 2) {v} := hh
    have hh' : Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 1 :=
      (Submodule.finrank_mono hle).trans
        (by simpa using finrank_span_le_card (R := ZMod 2) ({v} : Set (natural (Fin 6))))
    omega
  obtain ⟨w,hw,hwv⟩ := hw
  obtain h0 | ⟨d,rfl⟩ := vector_cases v
  · exact (hv0 h0).elim
  obtain h0 | ⟨e,rfl⟩ := vector_cases w
  · exact (hwv (h0 ▸ Submodule.zero_mem _)).elim
  have hde : d ≠ e := by
    intro he
    exact hwv (he ▸ Submodule.subset_span (Set.mem_singleton _))
  have hd := SylowSmallMovers.fixed_duad A d hv z hz
  have he := SylowSmallMovers.fixed_duad A e hw z hz
  intro x hx
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hAS hx)
  have cert : ∀ d e : Duad, d ≠ e →
      SylowSmallMovers.fixesDuad z d → SylowSmallMovers.fixesDuad z e →
      ∀ i : Fin 16, SylowSmallMovers.fixesDuad (sylowWords i) d →
        SylowSmallMovers.fixesDuad (sylowWords i) e →
        ∃ j : Fin 8, dWords j = sylowWords i := by decide +kernel
  exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr
    (cert d e hde hd he i (SylowSmallMovers.fixed_duad A d hv _ hx)
      (SylowSmallMovers.fixed_duad A e hw _ hx))

private theorem cube_intersection_card (E : Subgroup S) (hES : E ≤ sylowCarrier)
    (hE : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E) : Nat.card (E ⊓ D 6 : Subgroup S) = 4 := by
  have hD : Nat.card (D 6) = 8 := card_disjointTranspositions 3
  have hi : (D 6).relIndex sylowCarrier = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup S) (D 6) sylowCarrier bot_le D_le_sylowCarrier
    rw [relIndex_bot_left,relIndex_bot_left,hD,card_sylowCarrier] at hh
    omega
  have hb : (D 6).relIndex E ≤ 2 := by
    simpa only [hi] using relIndex_le_of_le_right (H := D 6) hES (by rw [hi]; decide)
  have hp : 0 < (D 6).relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hn : (D 6).relIndex E ≠ 1 := by
    intro he
    let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions 3
    exact hne (IsElementaryAbelian.of_injective
      (inclusion (relIndex_eq_one.mp he)) (inclusion_injective _))
  have hh := relIndex_mul_relIndex (⊥ : Subgroup S) (E ⊓ D 6) E bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hE,
    show (D 6).relIndex E = 2 by omega] at hh
  omega

private theorem small_eight_image_eq (E A : Subgroup S) (hES : E ≤ sylowCarrier)
    (hE : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hAE : A ≤ E) (hA : 4 ≤ Nat.card A) (hsmall : fixedCodim ρ A ≤ 2) : A = E ⊓ D 6 := by
  have hAD := small_with_square_le_cube A (hAE.trans hES)
    (square_in_large_subgroup E A hES hE hne hAE hA) hsmall
  exact eq_of_le_of_card_ge (le_inf hAE hAD) ((cube_intersection_card E hES hE hne) ▸ hA)

private theorem conjugate_eight_model (E : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hE : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E) :
    Nat.card (E ⊓ (D 6).map (MulAut.conj u).toMonoidHom : Subgroup S) = 4 ∧
      ∀ A : Subgroup S, A ≤ E → 4 ≤ Nat.card A → fixedCodim ρ A ≤ 2 →
        A = E ⊓ (D 6).map (MulAut.conj u).toMonoidHom := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (B : Subgroup S) : (B.map (MulAut.conj u).toMonoidHom).map f = B := by
    rw [map_map]
    have he : f.comp (MulAut.conj u).toMonoidHom = MonoidHom.id S := by ext x; simp [f]
    rw [he,map_id]
  have hES' : E.map f ≤ sylowCarrier := (map_mono hES).trans_eq (back _)
  have hE' : Nat.card (E.map f) = 8 := by
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective,hE]
  have hn' : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro hh
    let := hh
    apply hne
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj u⁻¹).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  constructor
  · rw [←card_map_of_injective (f := f) (MulAut.conj u⁻¹).injective,
      map_inf _ _ _ (MulAut.conj u⁻¹).injective,back]
    exact cube_intersection_card _ hES' hE' hn'
  · intro A hAE hA hs
    apply (map_injective (f := f) (MulAut.conj u⁻¹).injective)
    rw [map_inf _ _ _ (MulAut.conj u⁻¹).injective,back]
    exact small_eight_image_eq _ _ hES' hE' hn' (map_mono hAE)
      (by rwa [card_map_of_injective (MulAut.conj u⁻¹).injective])
      (by rwa [fixedCodim_map_conj])

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Above four, the actual radical has a unique maximum small mover of
quotient order four and radical index two. The larger normalizer's mover
restricts to this subgroup; both full covers are retained. -/
theorem radical_small_movers_knownSimple (hb : 4 < replacementDistance h d) :
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    let N := normalizer (d.radical : Set d.overgroup)
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
    ∃ u : S,
      N.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom ∧
      J = d.radical ⊓ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 ∧
      SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 = {J} ∧
      J.map s.projection = d.radical.map s.projection ⊓
        (D 6).map (MulAut.conj u).toMonoidHom ∧
      (pCore 2 d.overgroup).relIndex J = 4 ∧ J.relIndex d.radical = 2 ∧
      (centralizer (J : Set d.overgroup)).relIndex (replacementMoved d) = 4 ∧
      (centralizer (d.radical : Set d.overgroup)).relIndex (replacementMoved d) = 8 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let N := normalizer (d.radical : Set d.overgroup)
  obtain ⟨_,hne,_,hE⟩ := SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hE' : Nat.card (d.radical.map s.projection) = 8 := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨u,hN,_,hJN,hJNmap,_,_,hJNfixed⟩ :=
    SylowSmallMovers.normalizer_small_movers_knownSimple
      (e := e) (hz := hz) (hn := hn) hb
  let D' := (D 6).map (MulAut.conj u).toMonoidHom
  let F := d.radical ⊓ D'.comap s.projection
  have hFmap : F.map s.projection = d.radical.map s.projection ⊓ D' := by
    apply le_antisymm
    · exact le_inf (map_mono inf_le_left) ((map_mono inf_le_right).trans (map_comap_le _ _))
    · rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      exact mem_map_of_mem s.projection ⟨hx,hy⟩
  have hES : d.radical.map s.projection ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom :=
    (map_mono d.radical.le_normalizer).trans_eq hN
  have hmodel := conjugate_eight_model _ u hES hE' hne'
  have hFcard : Nat.card (F.map s.projection) = 4 := by rw [hFmap]; exact hmodel.1
  have hk : s.projection.ker ≤ d.radical := s.projection_kernel ▸ replacement_core_le_radical h d
  have hkF : s.projection.ker ≤ F := le_inf hk (ker_le_comap _ _)
  have hFi : (pCore 2 d.overgroup).relIndex F = 4 := by
    rw [←s.projection_kernel,relIndex_ker,hFcard]
  have hFfix : (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) ≤ 4 := by
    have hle : F ≤ N ⊓ D'.comap s.projection :=
      le_inf (inf_le_left.trans d.radical.le_normalizer) inf_le_right
    exact (relIndex_le_of_le_left (centralizer_le hle) index_ne_zero_of_finite).trans_eq hJNfixed
  have hbds (A : Subgroup d.overgroup) :
      2 ^ fixedCodim ρ (A.map s.projection) ≤
        (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) := by
    let := replacementMoved_normal h d
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)]
    have hh := (cover_model s).fixedCodim_bounds (A.map s.projection)
    simp only [map_id] at hh
    exact Nat.pow_le_pow_right (by decide) hh.1
  have hsmall : SmallMover.Admissible (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 F :=
    ⟨inf_le_left,hFi ▸ hFfix,hFfix⟩
  have himage (A : Subgroup d.overgroup)
      (ha : SmallMover.Admissible (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 A)
      (hcard : 4 ≤ Nat.card (A.map s.projection)) : A.map s.projection = F.map s.projection := by
    rw [hFmap]
    exact hmodel.2 _ (map_mono ha.1) hcard
      ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((hbds A).trans ha.2.2))
  have hfix : replacementMoved d ≤ centralizer (s.projection.ker : Set d.overgroup) := by
    rw [s.projection_kernel,←moved_centralizer s]
    exact le_centralizer_iff.mpr le_rfl
  have hmax : SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 = {F} := by
    ext A
    rw [←s.projection_kernel,SmallMover.maximal_iff_image_maximal
      s.projection (replacementMoved d) d.radical 4 hk hfix]
    constructor
    · rintro ⟨ha,hkA,hm⟩
      rw [s.projection_kernel] at ha hm
      have hc : 4 ≤ Nat.card (A.map s.projection) := hFcard ▸ hm F hsmall
      exact Set.mem_singleton_iff.mpr (map_injective_of_ker_le s.projection hkA hkF (himage A ha hc))
    · rintro rfl
      refine ⟨s.projection_kernel ▸ hsmall,hkF,?_⟩
      intro A ha
      rw [s.projection_kernel] at ha
      by_cases hc : 4 ≤ Nat.card (A.map s.projection)
      · rw [himage A ha hc]
      · rw [hFcard]; omega
  have hj : SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4 = F := by
    rw [SmallMover.join,hmax,sSup_singleton]
  have hFfixeq : (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) = 4 := by
    have hlo : 2 ≤ fixedCodim ρ (F.map s.projection) := by
      by_contra! hh
      have hFn : F.map s.projection ≠ ⊥ := by intro he; rw [he,card_bot] at hFcard; omega
      have hle : fixedCodim ρ (F.map s.projection) ≤ 1 := by omega
      obtain ⟨t,_,ht,he⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
        _ hFn hle
      rw [he,Nat.card_zpowers,ht.orderOf] at hFcard
      omega
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlo
    have hh := hbds F
    omega
  have hidx : F.relIndex d.radical = 2 := by
    have hh := relIndex_mul_relIndex s.projection.ker F d.radical hkF inf_le_left
    rw [s.projection_kernel,hFi,←s.projection_kernel,relIndex_ker,hE'] at hh
    omega
  have hlarge : 4 < (centralizer (d.radical : Set d.overgroup)).relIndex (replacementMoved d) := by
    by_contra! hh
    have he := himage d.radical ⟨le_rfl,by
      rw [←s.projection_kernel,relIndex_ker,hE']; omega,hh⟩ (by rw [hE']; decide)
    have hc := congrArg (fun A : Subgroup S => Nat.card A) he
    rw [hE',hFcard] at hc
    omega
  refine ⟨u,hN,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hj,hJN,←inf_assoc,inf_eq_left.mpr d.radical.le_normalizer]
  · rwa [hj]
  · rw [hj]; exact hFmap
  · rw [hj]; exact hFi
  · rw [hj]; exact hidx
  · rw [hj]; exact hFfixeq
  · exact SylowKernelMovement.cover_two_group_fixed_index_eight s d.radical
      (replacement_radical_isPGroup h d) hlarge

include e hz hn in
/-- On every actual edge, the source small mover is the intersection of
the edge core with the larger normalizer's small mover. It has four images,
index two and quadratic action on the whole moved cover. -/
theorem edge_small_mover_knownSimple (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    J = Q d.radical t ⊓ SmallMover.join (U d.radical a) (Q d.radical a) T 4 ∧
      SmallMover.Maximal (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = {J} ∧
      Q d.radical a ≤ J ∧ J ≤ Q d.radical t ∧
      (Q d.radical a).relIndex J = 4 ∧ J.relIndex (Q d.radical t) = 2 ∧
      Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,J⁆,J⁆ = ⊥ ∧
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4 ∧
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 := by
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc ha hat
  let N := normalizer (d.radical : Set d.overgroup)
  let F := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hj : F.map i = J := by
    rw [SmallMover.join_map i hinj,hiU,hiQ,hiR]
  obtain ⟨u,_,hF,hmax,hFmap,hQi,hFi,hfix,hRfix⟩ :=
    radical_small_movers_knownSimple (e := e) (hz := hz) (hn := hn) hb
  change F = _ at hF
  have hiN : N.map i = normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  have hQF : pCore 2 d.overgroup ≤ F := by
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    apply SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
    rw [←moved_centralizer s]
    exact le_centralizer_iff.mpr le_rfl
  have hFle : F ≤ d.radical := SmallMover.join_le _ _ _ _
  have hJT : J ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hJi : J.relIndex (Q d.radical t) = 2 := by
    rw [←hj,←hiR,relIndex_map_map_of_injective _ _ hinj]
    exact hFi
  refine ⟨?_,?_,?_,hJT,?_,hJi,?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map i) hF
    rwa [hj,map_inf _ _ _ hinj,SmallMover.join_map i hinj,hiU,hiQ,hiR,hiN] at hh
  · have hh := SylowSmallMovers.maximal_map_singleton i hinj _ _ _ _ hmax
    rwa [hiU,hiQ,hiR,hj] at hh
  · change Q d.radical a ≤ J
    rw [←hj,←hiQ]; exact map_mono hQF
  · change (Q d.radical a).relIndex J = 4
    rw [←hj,←hiQ,relIndex_map_map_of_injective _ _ hinj]; exact hQi
  · exact (normal_subgroupOf_iff_le_normalizer hJT).mp (normal_of_index_eq_two hJi)
  · have hle : F ≤ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 :=
      hF.le.trans inf_le_right
    have hh : ⁅⁅replacementMoved d,F⁆,F⁆ ≤
        ⁅⁅replacementMoved d,SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4⁆,
          SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4⁆ :=
      commutator_mono (commutator_mono le_rfl hle) hle
    have hzero := SylowAdjacent.normalizer_small_mover_quadratic_knownSimple
      (e := e) (hz := hz) (hn := hn) hb
    have hz : ⁅⁅replacementMoved d,F⁆,F⁆ = ⊥ := bot_unique (hh.trans_eq hzero)
    have hm := congrArg (Subgroup.map i) hz
    rwa [map_commutator,map_commutator,hiU,hj,Subgroup.map_bot] at hm
  · change (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4
    rw [←hj,←hiU,SmallMover.centralizer_index_map i hinj]; exact hfix
  · rw [←hiR,←hiU,SmallMover.centralizer_index_map i hinj]; exact hRfix

include e hz hn in
/-- The radical's own small mover fixes the critical line and normalizes
the full critical kernel. If that line moves under the edge core, its
kernel normalizer inside the edge core is exactly this mover. -/
theorem critical_kernel_small_mover_knownSimple (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let T := Q d.radical (p.walk.getVert 1)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    J ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      J ≤ normalizer ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((¬ T ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set _)) →
        T ⊓ normalizer ((Z d.radical a ⊓ Q d.radical a' :
          Subgroup (FreeAmalgam d.radical)) : Set _) = J) := by
  let T := Q d.radical (p.walk.getVert 1)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨hJ,_,_,hJT,_,hJi,_⟩ := edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hk := SylowSmallMovers.small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hJ hk ⊢
  have hJC := hJ.le.trans (inf_le_right.trans hk.2.1)
  have hJN := hJ.le.trans (inf_le_right.trans hk.2.2.1)
  refine ⟨hJC,hJN,?_⟩
  intro hmove
  have hmoveN : ¬ (normalizer (T : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a) ≤
      centralizer ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hh
    exact hmove ((le_inf T.le_normalizer (fun _ hx => hx.2 a (adjacent_symm d.radical hat))).trans hh)
  rw [hJ,←hk.2.2.2 hmoveN,←inf_assoc,
    inf_eq_left.mpr (le_inf T.le_normalizer (fun _ hx => hx.2 a (adjacent_symm d.radical hat)))]

include e hz hn in
/-- Distinct neighboring movers generate the entire actual edge core,
with intersection index four. -/
theorem unequal_neighbor_generation_knownSimple (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    J ⊔ E = Q d.radical t ∧ (J ⊓ E).relIndex (Q d.radical t) = 4 := by
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hct
    rw [ha] at hh
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  obtain ⟨_,_,_,hJT,_,hJi,_⟩ := edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat
  obtain ⟨_,_,_,hET,_,hEi,_⟩ := edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hc hct
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical a from
      fun _ hx => hx.2 a (adjacent_symm d.radical hat))) (inclusion_injective _)
  exact SylowKernelPair.two_hyperplanes (Q d.radical t) _ _ hJT hET hJi hEi hne.symm

include e hz hn in
/-- An unequal neighboring mover supplies an actual element moving the
critical line and its full kernel, while remaining in the original edge. -/
theorem unequal_neighbor_moves_line_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hct : Adjacent d.radical c (p.walk.getVert 1))
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ∃ x ∈ SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical (p.walk.getVert 1)) 4,
      x ∈ Q d.radical (p.walk.getVert 1) ∧
      x ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∉ normalizer ((Z d.radical a ⊓ Q d.radical a' :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  classical
  let t := p.walk.getVert 1
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hpair := unequal_neighbor_generation_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat hct hne
  have hk := critical_kernel_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hEC : ¬ E ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    intro hh
    exact hmove (hpair.1 ▸ sup_le hk.1 hh)
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp hEC
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  refine ⟨x,hx,hET hx,hxc,?_⟩
  intro hxn
  have hJx : x ∈ J := by
    change x ∈ SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
    rw [←hk.2.2 hmove]
    exact ⟨hET hx,hxn⟩
  exact hxc (hk.1 hJx)
include e hz hn in
/-- An unequal neighboring mover has at least four images modulo the
starting core and fixes a subgroup of index exactly eight in the full
starting cover. No containment of the starting core in the neighbor is assumed. -/
theorem unequal_neighbor_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    4 ≤ (Q d.radical a).relIndex E ∧
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8 := by
  let S₀ := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S₀
  let Q₀ := (Q d.radical a).subgroupOf S₀
  let T₀ := (Q d.radical t).subgroupOf S₀
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
  let J₀ := J.subgroupOf S₀
  let E₀ := E.subgroupOf S₀
  let := finite_stabilizer d.radical a
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hct
    rw [ha] at hh
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  obtain ⟨_,_,hQJ,hJT,hQi,hJi,_⟩ := edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb ha hat
  obtain ⟨_,_,_,hET,_,hEi,_⟩ := edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hc hct
  have hUS : U d.radical a ≤ S₀ := (DistanceEight.U_le_Z d.radical a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S₀ := fun _ hx => hx.1
  have hTS : Q d.radical t ≤ S₀ := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S₀ := hJT.trans hTS
  have hES : E ≤ S₀ := hET.trans hTS
  have hjoin : SmallMover.join U₀ Q₀ T₀ 4 = J₀ := by
    apply map_injective S₀.subtype_injective
    rw [SmallMover.join_map S₀.subtype S₀.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hQS,
      map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hJS]
  have hcard' : Nat.card J₀ = Nat.card E₀ := by
    rw [←card_map_of_injective S₀.subtype_injective (K := J₀),
      ←card_map_of_injective S₀.subtype_injective (K := E₀),
      map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES]
    have hj := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) J (Q d.radical t) bot_le hJT
    have he := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) E (Q d.radical t) bot_le hET
    rw [relIndex_bot_left,relIndex_bot_left,hJi] at hj
    rw [relIndex_bot_left,relIndex_bot_left,hEi] at he
    omega
  have hlarge : Q₀.relIndex J₀ = 4 := by
    have hh := relIndex_map_map_of_injective Q₀ J₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hJS] at hh
    exact hh.symm.trans hQi
  have hEl : 4 ≤ Q₀.relIndex E₀ := by
    rw [←hlarge]
    exact SmallMover.relIndex_le_of_card_eq_of_le Q₀ J₀ E₀ (comap_mono hQJ) hcard'
  have hstrict : 4 < (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    by_contra hnidx
    have hi : (centralizer (E₀ : Set S₀)).relIndex U₀ ≤ 4 := by
      have hh := SmallMover.centralizer_index_map S₀.subtype S₀.subtype_injective U₀ E₀
      rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES] at hh
      rw [←hh]
      exact le_of_not_gt hnidx
    have he := SmallMover.eq_join_of_card_eq_of_index_le U₀ Q₀ T₀ 4 (by decide)
      (hjoin.symm ▸ comap_mono hQJ) (by rw [hjoin,hlarge])
      E₀ (comap_mono hET) (hjoin.symm ▸ hcard') hi
    rw [hjoin] at he
    have hh := congrArg (Subgroup.map S₀.subtype) he
    rw [map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hJS] at hh
    exact hne hh

  refine ⟨?_,?_⟩
  · have hh := relIndex_map_map_of_injective Q₀ E₀ S₀.subtype_injective
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hES] at hh
    rwa [hh]
  · let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
    obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hcent ha hat
    have hm : (E.comap i).map i = E := map_comap_eq_self (hES.trans_eq hir.symm)
    have hER : E.comap i ≤ d.radical := by
      have hh := comap_mono (f := i) (show E ≤ Q d.radical t from hET)
      rwa [←hiR,comap_map_eq_self_of_injective hinj] at hh
    have hidx := SmallMover.centralizer_index_map i hinj (replacementMoved d) (E.comap i)
    rw [hiU,hm] at hidx
    change (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 8
    rw [hidx]
    exact SylowKernelMovement.cover_two_group_fixed_index_eight s _
      ((replacement_radical_isPGroup h d).of_injective (inclusion hER)
        (inclusion_injective hER)) (by rwa [←hidx])


include e hz hn in
/-- The unequal mover at the second vertex supplies a literal new critical
path with the same first three vertices. Its two full critical kernels
span the starting seed and have invariant intersection of index four. -/
theorem second_mover_critical_path_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hne : SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
      (Q d.radical (p.walk.getVert 1)) 4 ≠
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (p.walk.getVert 1)) 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ∃ x ∈ SmallMover.join (U d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 2))
        (Q d.radical (p.walk.getVert 1)) 4,
      x ∈ Q d.radical (p.walk.getVert 1) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x⁻¹ a'),
        (∀ i, q.walk.getVert i = act d.radical x⁻¹ (p.walk.getVert i)) ∧
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = p.walk.getVert 2 ∧
        (Q d.radical (act d.radical x⁻¹ a')).relIndex (Z d.radical a) = 2 ∧
        let K := Z d.radical a ⊓ Q d.radical a'
        let K' := Z d.radical a ⊓ Q d.radical (act d.radical x⁻¹ a')
        K ⊔ K' = Z d.radical a ∧ (K ⊓ K').relIndex (Z d.radical a) = 4 ∧
          Q d.radical (p.walk.getVert 1) ≤ normalizer ((K ⊓ K' :
            Subgroup (FreeAmalgam d.radical)) : Set _) ∧
          (Q d.radical a ⊔ Z d.radical a') ⊓
            (Q d.radical a ⊔ Z d.radical (act d.radical x⁻¹ a')) = Q d.radical a := by
  have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt,hxc,_⟩ := unequal_neighbor_moves_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hct hne hmove
  have hxT : x ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a := ⟨(Q d.radical _).le_normalizer hxt,
        hxt.2 a (adjacent_symm d.radical hat)⟩
  obtain ⟨q,hq,_,hi,hjoin,hidx,hnorm,hcore⟩ := SylowKernelPair.small_moving_kernel_path_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall x hxT hxc
  have hnorm' := (le_inf (Q d.radical (p.walk.getVert 1)).le_normalizer
    (show Q d.radical (p.walk.getVert 1) ≤ stabilizer d.radical a from
      fun _ hx => hx.2 a (adjacent_symm d.radical hat))).trans hnorm
  refine ⟨x,hx,hxt,q,hq,?_,?_,hi,hjoin,hidx,hnorm',hcore⟩
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 1)).inv_mem hxt.1
  · rw [hq]
    exact (stabilizer d.radical (p.walk.getVert 2)).inv_mem
      (hxt.2 _ (adjacent_symm d.radical hct))

include e hz hn in
/-- In the literal original-radical embedding the small mover has index
four in the restricted original Sylow, and its full critical-kernel
normalizer is obtained by intersecting with the replacement edge core. -/
theorem original_radical_mover_kernel_knownSimple (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let J := SmallMover.join (U d.radical (alpha d.radical))
      (Q d.radical (alpha d.radical)) (Q d.radical (beta d.radical)) 4
    J = Q d.radical (beta d.radical) ⊓ SmallMover.join
        (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical)) T 4 ∧
      (Q d.radical (alpha d.radical)).relIndex J = 4 ∧ J.relIndex T = 4 ∧
      J ≤ centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      J ≤ normalizer ((Z d.radical (alpha d.radical) ⊓ Q d.radical a' :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((¬ Q d.radical (beta d.radical) ≤ centralizer
          ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
            Subgroup (FreeAmalgam d.radical)) : Set _)) →
        Q d.radical (beta d.radical) ⊓ normalizer
          ((Z d.radical (alpha d.radical) ⊓ Q d.radical a' :
            Subgroup (FreeAmalgam d.radical)) : Set _) = J) := by
  let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
  let J := SmallMover.join (U d.radical (alpha d.radical))
    (Q d.radical (alpha d.radical)) (Q d.radical (beta d.radical)) 4
  obtain ⟨hj,_,_,hJQ,hQi,hJi,_⟩ := edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) (a := alpha d.radical) (t := beta d.radical)
      hb rfl (base_adjacent d.radical)
  rw [SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hj
  have hk := critical_kernel_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hk
  rw [hfirst] at hk
  refine ⟨hj,hQi,?_,hk⟩
  have hQT : Q d.radical (beta d.radical) ≤ T := by
    rw [Q_beta]
    exact map_mono (comap_mono (map_subtype_le d.subgroup))
  have hi : (Q d.radical (beta d.radical)).relIndex T = 2 := by
    rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
    exact (SylowWholeCore.four_lt_original_sylow_eight_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb).2.2.1
  have hh := relIndex_mul_relIndex J (Q d.radical (beta d.radical)) T hJQ hQT
  rw [hJi,hi] at hh
  exact hh.symm

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightSmallMovers
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
