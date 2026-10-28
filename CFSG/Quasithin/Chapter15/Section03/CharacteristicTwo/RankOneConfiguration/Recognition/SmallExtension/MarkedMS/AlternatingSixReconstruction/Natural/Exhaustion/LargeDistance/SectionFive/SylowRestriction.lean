module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OriginalRadical
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Original Sylow restriction and the order-four replacement images

At large critical distance the actual ambient natural action is onto S₆.
An original Sylow radical maps to a Sylow subgroup of order sixteen. The
canonical Sylow's unique nontrivial square has centralizer of order sixteen,
so that Sylow is self-normalizing. Pullback proves that the original radical
is self-normalizing and that its original MS2(a) witness is the radical itself.

The restriction of this original Sylow to the replacement overgroup is again
Sylow. It normalizes the characteristic replacement radical, but need not
equal it. Their exact relative index times the order of the replacement
image is sixteen. The existing order-four offender bound restricts that
index to one, two or four.

When the replacement image has order four, its Thompson image fills it.
The actual offender catalogue and the odd permutation supplied by the
component-radical product leave precisely the two-transposition and mixed
planes. Each has a unique double transposition, so its normalizer has order
at most sixteen. The original Sylow restriction supplies the lower bound.
Thus the replacement radical, its elementary Thompson subgroup and its
Baumann subgroup have the same Sylow normalizer, with radical index four.
The last application identifies the corresponding normalizer inside the
starting stabilizer of the literal free-amalgam graph.

These are local normalizer and index calculations for the remaining Sylow
branch, not its distance exclusion. They retain both moved covers, all
central attachments, and the distinction between the original radical and
its minimum characteristic replacement. The distance-four residual bounds
and the unconditional large-distance conclusion remain open.

Source: Aschbacher--Smith C.1.31 (MS2)(a), printed p.135, and B.3.4,
pp.84--85; Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the Thompson/edge analysis in Section 5, pp.912--927, and the
characteristic replacement in Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowRestriction
local notation "S" => Equiv.Perm (Fin 6)
private abbrev z : S := kleinFirst 6 (by decide)

private theorem centralizer_card : Nat.card (centralizer ({z} : Set S)) = 16 := by
  have ht : z.cycleType = {2,2} := by decide +kernel
  rw [Equiv.Perm.nat_card_centralizer,ht]
  norm_num

private theorem square_table : ∀ i : Fin 16,
    (sylowWords i)^2 = 1 ∨ (sylowWords i)^2 = z := by decide +kernel

private theorem canonical_normalizer : normalizer (sylowCarrier : Set S) = sylowCarrier := by
  have hw : ∃ i : Fin 16, (sylowWords i)^2 = z := by decide +kernel
  obtain ⟨i,hi⟩ := hw
  have hle : normalizer (sylowCarrier : Set S) ≤ centralizer ({z} : Set S) := by
    intro g hg
    have hx : g*sylowWords i*g⁻¹ ∈ sylowCarrier :=
      (mem_normalizer_iff.mp hg _).mp ((mem_sylowCarrier_iff _).mpr ⟨i,rfl⟩)
    obtain ⟨j,hj⟩ := (mem_sylowCarrier_iff _).mp hx
    have hs : (g*sylowWords i*g⁻¹)^2 = (MulAut.conj g) z := by
      change ((MulAut.conj g) (sylowWords i))^2 = _
      rw [←map_pow,hi]
    have he : (MulAut.conj g) z = z := by
      rcases square_table j with h1 | hz
      · have he := hs.symm.trans (hj ▸ h1)
        have hz1 : z=1 := (MulAut.conj g).injective (he.trans (map_one _).symm)
        exact (by decide : z≠1) hz1 |>.elim
      · exact hs.symm.trans (hj ▸ hz)
    apply mem_centralizer_singleton_iff.mpr
    exact mul_inv_eq_iff_eq_mul.mp he
  apply (eq_of_le_of_card_ge sylowCarrier.le_normalizer ?_).symm
  rw [card_sylowCarrier]
  exact (card_le_of_le hle).trans_eq centralizer_card

private theorem sylow_normalizer (P : Sylow 2 S) :
    normalizer ((P : Subgroup S) : Set S) = (P : Subgroup S) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P sylow
  have hm : (P : Subgroup S).map (MulAut.conj g).toMonoidHom = sylowCarrier :=
    congrArg (fun P : Sylow 2 S => (P : Subgroup S)) hg
  apply (map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,hm,canonical_normalizer]

private theorem four_model_normalizer_bound (A : Subgroup S)
    (hA : A = disjointTranspositions 6 2 ∨ A = plus) :
    Nat.card (normalizer (A : Set S)) ≤ 16 := by
  have hzA : z ∈ A := by
    rcases hA with rfl | rfl
    · exact (mem_disjointTranspositions_iff (2 : Fin 4) _).mpr ⟨3,by decide⟩
    · exact subset_closure (by simp)
  have huniq : ∀ x ∈ A, x.support.card = 4 → x = z := by
    intro x hx hc
    rcases hA with rfl | rfl
    · obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (2 : Fin 4) _).mp hx
      exact (by decide +kernel : ∀ i : Fin 4,
        (initialWords 2 i).support.card=4 → initialWords 2 i=z) i hc
    · obtain ⟨i,rfl⟩ := (mem_plus_iff _).mp hx
      exact (by decide +kernel : ∀ i : Fin 4,
        (planeWords 0 i).support.card=4 → planeWords 0 i=z) i hc
  have hn : normalizer (A : Set S) ≤ centralizer ({z} : Set S) := by
    intro g hg
    have he := huniq (g*z*g⁻¹) ((mem_normalizer_iff.mp hg z).mp hzA)
      (by rw [Equiv.Perm.card_support_conj]; decide)
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  exact (card_le_of_le hn).trans_eq centralizer_card

private theorem conjugate_four_normalizer_bound (A : Subgroup S)
    (hA : A = disjointTranspositions 6 2 ∨ A = plus) (g : S) :
    Nat.card (normalizer (A.map (MulAut.conj g).toMonoidHom : Set S)) ≤ 16 := by
  rw [←map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
    card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact four_model_normalizer_bound A hA

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)

include s in
private theorem original_image_sylow (P : Sylow 2 M) (hP : (P : Subgroup M) = T) :
    ∃ W : Sylow 2 S, (W : Subgroup S) = (T).map (OriginalRadical.ambientProjection h e hz hn) := by
  exact ⟨P.mapSurjective (OriginalRadical.ambientProjection_surjective h e hz hn s),
    congrArg (Subgroup.map (OriginalRadical.ambientProjection h e hz hn)) hP⟩

include s in
/-- The original Sylow radical is self-normalizing in the original ambient group. -/
theorem original_normalizer (P : Sylow 2 M) (hP : (P : Subgroup M) = T) :
    normalizer (T : Set M) = T := by
  let q := OriginalRadical.ambientProjection h e hz hn
  obtain ⟨W,hW⟩ := original_image_sylow s P hP
  have hn : normalizer ((T).map q : Set S) = (T).map q := by rw [←hW,sylow_normalizer]
  apply le_antisymm _ (T).le_normalizer
  have hm := le_normalizer_map q (H := T)
  have hh : (normalizer (T : Set M)).map q ≤ (T).map q := hm.trans_eq hn
  have hc := map_le_iff_le_comap.mp hh
  rw [comap_map_eq,OriginalRadical.ambientProjection_kernel,
    sup_eq_left.mpr h.relative_radical.twoCore_le] at hc
  exact hc

include s in
/-- Its MS2(a) witness is the original radical itself, without any assertion
that the characteristic replacement is Sylow. -/
theorem original_odd_witness (P : Sylow 2 M) (hP : (P : Subgroup M) = T)
    (H : Subgroup M) (hcore : H.pCoreIn 2 = T) : H = T := by
  have hn : H ≤ normalizer (T : Set M) := by
    rw [←hcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  rw [original_normalizer s P hP] at hn
  exact le_antisymm hn (hcore ▸ pCoreIn_le 2 H)

private theorem restricted_image :
    ((T).subgroupOf d.overgroup).map s.projection =
      (T).map (OriginalRadical.ambientProjection h e hz hn) := by
  rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,
    ←OriginalRadical.ambientProjection_restriction,←map_map,subgroupOf_map_subtype]
  apply le_antisymm (map_mono inf_le_left)
  rintro _ ⟨t,ht,rfl⟩
  obtain ⟨x,hx⟩ := s.surjective (OriginalRadical.ambientProjection h e hz hn t)
  have hx' : OriginalRadical.ambientProjection h e hz hn x.val =
      OriginalRadical.ambientProjection h e hz hn t := by
    rw [←hx,SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact DFunLike.congr_fun (OriginalRadical.ambientProjection_restriction h e hz hn d) x
  have hxt : x.val*t⁻¹ ∈ pCore 2 M := by
    rw [←OriginalRadical.ambientProjection_kernel h e hz hn]
    change OriginalRadical.ambientProjection h e hz hn (x.val*t⁻¹)=1
    rw [map_mul,map_inv,hx',mul_inv_cancel]
  have hxT : x.val ∈ T := by
    have hh := (T).mul_mem (h.relative_radical.twoCore_le hxt) ht
    simpa only [inv_mul_cancel_right] using hh
  exact ⟨x.val,⟨hxT,x.property⟩,hx'⟩

include s in
private theorem restricted_sylow (P : Sylow 2 M) (hP : (P : Subgroup M) = T) :
    ∃ W : Sylow 2 d.overgroup, (W : Subgroup d.overgroup) = (T).subgroupOf d.overgroup := by
  obtain ⟨W,hW⟩ := original_image_sylow s P hP
  have hp : IsPGroup 2 s.projection.ker := by rw [s.projection_kernel]; exact pCore_isPGroup
  let W₀ := W.comapOfKerIsPGroup s.projection hp
    (by rw [MonoidHom.range_eq_top.mpr s.surjective]; exact le_top)
  refine ⟨W₀,?_⟩
  change (W : Subgroup S).comap s.projection = _
  rw [hW,←restricted_image s,comap_map_eq]
  apply sup_eq_left.mpr
  rw [s.projection_kernel,replacement_core h d]
  exact comap_mono h.relative_radical.twoCore_le

private theorem restricted_image_card (P : Sylow 2 M) (hP : (P : Subgroup M) = T) :
    Nat.card (((T).subgroupOf d.overgroup).map s.projection) = 16 := by
  obtain ⟨W,hW⟩ := original_image_sylow s P hP
  rw [restricted_image s,←hW]
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S W sylow
  have hh := congrArg (fun W : Sylow 2 S => Nat.card (W : Subgroup S)) hg
  change Nat.card ((W : Subgroup S).map (MulAut.conj g).toMonoidHom) = Nat.card sylowCarrier at hh
  rwa [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,card_sylowCarrier] at hh

omit [Finite G] in
private theorem radical_le_restricted : d.radical ≤ (T).subgroupOf d.overgroup :=
  comap_mono (map_subtype_le d.subgroup)

omit [Finite G] in
private theorem restricted_normalizes_radical :
    (T).subgroupOf d.overgroup ≤ normalizer (d.radical : Set d.overgroup) := by
  let := d.characteristic
  have hn : T ≤ normalizer (d.ambient : Set M) :=
    (T).le_normalizer.trans (normalizer_le_normalizer_characteristic_image T d.subgroup)
  exact (comap_mono hn).trans (le_normalizer_comap d.overgroup.subtype)

private theorem restricted_index_formula (P : Sylow 2 M) (hP : (P : Subgroup M) = T) :
    Nat.card (d.radical.map s.projection) * d.radical.relIndex ((T).subgroupOf d.overgroup) = 16 := by
  have hk := replacement_core_le_radical h d
  have hkT := hk.trans (radical_le_restricted (d := d))
  have hi : (d.radical.map s.projection).relIndex (((T).subgroupOf d.overgroup).map s.projection) =
      d.radical.relIndex ((T).subgroupOf d.overgroup) := by
    rw [relIndex_map_map,s.projection_kernel,sup_eq_left.mpr hk,sup_eq_left.mpr hkT]
  have hh := relIndex_mul_relIndex (⊥ : Subgroup S) (d.radical.map s.projection)
    (((T).subgroupOf d.overgroup).map s.projection) bot_le
    (map_mono (f := s.projection) (radical_le_restricted (d := d)))
  rw [relIndex_bot_left,relIndex_bot_left] at hh
  rwa [hi,restricted_image_card s P hP] at hh

section KnownSimple
variable {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}

/-- A Sylow original radical restricts to a Sylow subgroup of the replacement,
with the actual replacement radical normal in it. Its index is one, two or four. -/
theorem original_sylow_restriction_knownSimple
    (hb : 2 < replacementDistance h d) (P : Sylow 2 M) (hP : (P : Subgroup M) = T) :
    (∃ W : Sylow 2 d.overgroup, (W : Subgroup d.overgroup) = (T).subgroupOf d.overgroup) ∧
      (T).subgroupOf d.overgroup ≤ normalizer (d.radical : Set d.overgroup) ∧
      Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) *
        d.radical.relIndex ((T).subgroupOf d.overgroup) = 16 ∧
      (d.radical.relIndex ((T).subgroupOf d.overgroup) = 1 ∨
        d.radical.relIndex ((T).subgroupOf d.overgroup) = 2 ∨
        d.radical.relIndex ((T).subgroupOf d.overgroup) = 4) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hf := restricted_index_formula s P hP
  rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hf
  refine ⟨restricted_sylow s P hP,restricted_normalizes_radical,hf,?_⟩
  let A := d.radical.map (SourceReduction.projection h e hz hn d)
  have hlo : 4 ≤ Nat.card A := large_distance_radical_image_four_le_knownSimple hb
  let i := d.radical.relIndex ((T).subgroupOf d.overgroup)
  have hprod : Nat.card A * i = 16 := hf
  have hi : i ≤ 4 := by nlinarith
  have hdiv : i ∣ 16 := ⟨Nat.card A,by simpa only [Nat.mul_comm] using hprod.symm⟩
  change i=1 ∨ i=2 ∨ i=4
  interval_cases i <;> norm_num at *

/-- Every remaining image of order four is literally a two-transposition
plane or a mixed plane; its Thompson image fills that same plane. -/
theorem four_image_models_knownSimple
    (hb : 2 < replacementDistance h d)
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) :
    (Stellmacher.elementaryAbelianMaxJ d.radical).map
        (SourceReduction.projection h e hz hn d) =
      d.radical.map (SourceReduction.projection h e hz hn d) ∧
    ∃ g : S,
      d.radical.map (SourceReduction.projection h e hz hn d) =
        (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom ∨
      d.radical.map (SourceReduction.projection h e hz hn d) =
        plus.map (MulAut.conj g).toMonoidHom := by
  let π := SourceReduction.projection h e hz hn d
  let E := d.radical.map π
  let J := (Stellmacher.elementaryAbelianMaxJ d.radical).map π
  have hcardPair : Nat.card (disjointTranspositions 6 2) = 4 :=
    card_disjointTranspositions (2 : Fin 4)
  have hJE : J ≤ E := map_mono (sSup_le fun _ hA => hA.1)
  have hJ : J=E := eq_of_le_of_card_ge hJE
    (hfour ▸ large_distance_thompson_image_four_le_knownSimple hb)
  refine ⟨hJ,?_⟩
  have hodd : ¬ E ≤ alternatingGroup (Fin 6) := by
    intro he
    let s := fullSymmetricAction_knownSimple h e hz hn d hb
    obtain ⟨x,hx⟩ := s.surjective Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap01
    obtain ⟨k,hk,r,hr,hkr⟩ := replacement_product h d x
    have hk' : s.projection k ∈ alternatingGroup (Fin 6) := by
      rw [←s.component_image]
      exact mem_map_of_mem _ hk
    have hr' : s.projection r ∈ alternatingGroup (Fin 6) := by
      rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
      exact he (mem_map_of_mem π hr)
    have hh := (alternatingGroup (Fin 6)).mul_mem hk' hr'
    rw [←map_mul,hkr,hx] at hh
    exact (by decide : Theory.SpecificGroups.SymmetricSix.BinaryFlags.swap01 ∉
      alternatingGroup (Fin 6)) hh
  obtain ⟨g,hg|hg|hg⟩ := large_distance_thompson_four_models_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  · refine ⟨g,Or.inl ?_⟩
    exact (eq_of_le_of_card_ge (hg.trans hJE) (by
      rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,hfour,
        hcardPair])).symm
  · have he : (evenPart 6).map (MulAut.conj g).toMonoidHom=E :=
      eq_of_le_of_card_ge (hg.trans hJE) (by
        rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,card_evenPart,hfour])
    have hA : (alternatingGroup (Fin 6)).map (MulAut.conj g).toMonoidHom =
        alternatingGroup (Fin 6) :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
    exact (hodd (he.symm.le.trans ((map_mono inf_le_right).trans_eq hA))).elim
  · refine ⟨g,Or.inr ?_⟩
    exact (eq_of_le_of_card_ge (hg.trans hJE) (by
      rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,card_plus,hfour])).symm

/-- In every order-four image branch the radical normalizer is the restriction
of the original Sylow radical, and the replacement radical has index four in it. -/
theorem four_image_normalizer_knownSimple
    (hb : 2 < replacementDistance h d)
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) :
    normalizer (d.radical : Set d.overgroup) = (T).subgroupOf d.overgroup ∧
      (∃ W : Sylow 2 d.overgroup, (W : Subgroup d.overgroup) =
        normalizer (d.radical : Set d.overgroup)) ∧
      d.radical.relIndex (normalizer (d.radical : Set d.overgroup)) = 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  obtain ⟨_,g,hg⟩ := four_image_models_knownSimple hb hfour
  have hP : ∃ P : Sylow 2 M, (P : Subgroup M)=T := by
    rcases hg with hg | hg
    · exact large_distance_pair_original_sylow_knownSimple hb g hg
    · exact large_distance_mixed_original_sylow_knownSimple hb g hg
  obtain ⟨P,hP⟩ := hP
  have hnorm : Nat.card (normalizer (d.radical.map s.projection : Set S)) ≤ 16 := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    rcases hg with hg | hg
    · rw [hg]; exact conjugate_four_normalizer_bound _ (Or.inl rfl) g
    · rw [hg]; exact conjugate_four_normalizer_bound _ (Or.inr rfl) g
  have hN : (T).subgroupOf d.overgroup ≤ normalizer (d.radical : Set d.overgroup) :=
    restricted_normalizes_radical
  have himage : (normalizer (d.radical : Set d.overgroup)).map s.projection =
      ((T).subgroupOf d.overgroup).map s.projection := by
    apply (eq_of_le_of_card_ge (map_mono (f := s.projection) hN) ?_).symm
    rw [restricted_image_card s P hP]
    exact (card_le_of_le (le_normalizer_map s.projection (H := d.radical))).trans hnorm
  have he : normalizer (d.radical : Set d.overgroup) = (T).subgroupOf d.overgroup := by
    have hh := congrArg (Subgroup.comap s.projection) himage
    rw [comap_map_eq,comap_map_eq,s.projection_kernel,
      sup_eq_left.mpr ((replacement_core_le_radical h d).trans d.radical.le_normalizer),
      sup_eq_left.mpr ((replacement_core_le_radical h d).trans radical_le_restricted)] at hh
    exact hh
  refine ⟨he,?_,?_⟩
  · rw [he]; exact restricted_sylow s P hP
  · have hf := restricted_index_formula s P hP
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfour] at hf
    rw [he]
    omega

/-- Both characteristic control subgroups have exactly this same Sylow
normalizer. Their quotient images are not used as substitutes for the subgroups. -/
theorem four_image_characteristic_normalizers_knownSimple
    (hb : 2 < replacementDistance h d)
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) :
    normalizer (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) =
      (T).subgroupOf d.overgroup ∧
    normalizer (CFSG.Quasithin.ChapterB.baumann d.radical : Set d.overgroup) =
      (T).subgroupOf d.overgroup := by
  let π := SourceReduction.projection h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hπ : Function.Surjective π := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using s.surjective
  have hk : π.ker ≤ d.radical := by
    rw [SourceReduction.projection_kernel]; exact replacement_core_le_radical h d
  have hJ : normalizer (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) =
      normalizer (d.radical : Set d.overgroup) := by
    rw [←Stellmacher.normalizer_comap_map_maxJ d.radical π hπ hk,
      (four_image_models_knownSimple hb hfour).1,
      comap_normalizer_eq_of_surjective _ hπ,comap_map_eq,sup_eq_left.mpr hk]
  have hB : normalizer (CFSG.Quasithin.ChapterB.baumann d.radical : Set d.overgroup) =
      normalizer (d.radical : Set d.overgroup) := by
    have hhered : Stellmacher.elementaryAbelianMaxJ (CFSG.Quasithin.ChapterB.baumann d.radical) =
        Stellmacher.elementaryAbelianMaxJ d.radical :=
      Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate d.radical _
        (CFSG.Quasithin.ChapterB.elementaryAbelianMaxJ_le_baumann d.radical) inf_le_left
    have hn := Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ
      (CFSG.Quasithin.ChapterB.baumann d.radical)
    rw [hhered,hJ] at hn
    exact le_antisymm hn (Stellmacher.normalizer_le_normalizer_baumann d.radical)
  have he := (four_image_normalizer_knownSimple hb hfour).1
  exact ⟨hJ.trans he,hB.trans he⟩

/-- On the actual amalgam edge, the normalizer inside the starting stabilizer
is the embedded restriction of the original Sylow radical. The edge kernel
has index four there; no larger graph normalizer is identified with it. -/
theorem four_image_edge_normalizer_knownSimple
    (hb : 2 < replacementDistance h d)
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) :
    normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical) =
      ((T).subgroupOf d.overgroup).map (embedM d.radical) ∧
    (Q d.radical (beta d.radical)).relIndex
      (((T).subgroupOf d.overgroup).map (embedM d.radical)) = 4 := by
  have he := four_image_normalizer_knownSimple hb hfour
  have hm : (normalizer (d.radical : Set d.overgroup)).map (embedM d.radical) =
      normalizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical) := by
    have hc : (normalizer (d.radical.map (embedM d.radical) : Set (FreeAmalgam d.radical))).comap
        (embedM d.radical) = normalizer (d.radical : Set d.overgroup) := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
        comap_map_eq_self_of_injective (embedM_injective d.radical)]
    rw [←hc,map_comap_eq,←Q_beta]
    have hbase : stabilizer d.radical (alpha d.radical) = (embedM d.radical).range :=
      stabilizer_m_base d.radical
    rw [hbase,inf_comm]
  refine ⟨hm.symm.trans (congrArg (Subgroup.map (embedM d.radical)) he.1),?_⟩
  rw [Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical),←he.1]
  exact he.2.2

end KnownSimple

end SylowRestriction
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
