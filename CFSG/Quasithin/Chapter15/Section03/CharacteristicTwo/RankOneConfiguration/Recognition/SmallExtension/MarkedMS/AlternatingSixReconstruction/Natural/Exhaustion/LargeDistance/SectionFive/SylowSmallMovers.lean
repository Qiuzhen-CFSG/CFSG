module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Structure.Basic
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Dimensions
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.GroupTheory.SmallMoverFamily
public import Theory.Representation.BinaryPermutationSixCover.Movement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer

/-!
# Small movers in the original Sylow and full critical-kernel normalizers

Above distance four, the radical normalizer is the restricted original
Sylow. We identify its maximum-order small-mover family, using the literal
indices of MS93 (5.0) and unrestricted subgroups. The unique maximum is the
preimage of the three-transposition subgroup in its marked six-letter
Sylow image. Its image has order eight, its normalizer index is two, and its
fixed index on the entire moved cover is four.

The model calculation uses two independent fixed natural vectors, represented
by distinct duads. A checked finite table identifies their sufficiently large
common stabilizer inside the canonical Sylow. Kernel saturation transfers
maximum order to image order. The natural and augmentation fixed-codimension
bounds give the same result on both moving covers, of orders sixteen and
thirty-two.

Every actor of fixed index at most two in the edge core lies in this maximum
and commutes with it modulo the starting two-core. On a small critical path,
the maximum therefore fixes the critical commutator line and preserves the
full critical seed kernel. If the full relative normalizer moves the line,
the kernel normalizer has index two and equals this small-mover maximum.
The actual endpoint seed lies in the maximum and supplies a generating
neighbor through the existing critical generation theorem.

All statements transport through the literal graph embeddings. For radical
image order sixteen, the previously proved equality between the relative
normalizer and edge core gives the actual source small-mover family and a
generating edge. The final application retains the restricted original Sylow
as its own carrier. No such equality is asserted for radical image order
eight. The non-elementary backward critical shift, terminal exclusions and
distance-four obligations remain with the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.0), (5.4)--(5.8), printed pp.912, 915--920, and the small-line
branch of (5.11), pp.923--924.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix (pair)
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)

private def fixesDuad (g : S) (d : Duad) : Prop :=
  pair (g d.val.1) (g d.val.2) = pair d.val.1 d.val.2

private instance (g : S) (d : Duad) : Decidable (fixesDuad g d) := inferInstanceAs
  (Decidable (pair (g d.val.1) (g d.val.2) = pair d.val.1 d.val.2))

private def pairWords (d e : Duad) : Finset (Fin 16) :=
  Finset.univ.filter (fun i => fixesDuad (sylowWords i) d ∧ fixesDuad (sylowWords i) e)

private theorem pair_certificate : ∀ d e : Duad, d ≠ e →
    8 ≤ (pairWords d e).card → ∀ i ∈ pairWords d e,
      ∃ j : Fin 8, dWords j = sylowWords i := by
  decide +kernel

private theorem fixed_duad (A : Subgroup S) (d : Duad)
    (hd : duadVector d ∈ fixedSpace ρ A) (g : S) (hg : g ∈ A) : fixesDuad g d := by
  have hh : ρ g (duadVector d) = duadVector d := hd ⟨g,hg⟩
  rw [duadVector,pairVector_map] at hh
  exact (pairVector_eq_iff (g.injective.ne (ne_of_lt d.property))
    (ne_of_lt d.property)).mp hh

private theorem large_small_eq (A : Subgroup S) (hA : A ≤ sylowCarrier)
    (hc : 8 ≤ Nat.card A) (hd : fixedCodim ρ A ≤ 2) : A = D 6 := by
  classical
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
  have hword (g : A) : ∃ i : pairWords d e, sylowWords i.val = g.val := by
    obtain ⟨i,hi⟩ := (mem_sylowCarrier_iff g.val).mp (hA g.property)
    refine ⟨⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩,hi⟩
    rw [hi]
    exact ⟨fixed_duad A d hv _ g.property,fixed_duad A e hw _ g.property⟩
  let f : A → pairWords d e := fun g => (hword g).choose
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact ((hword x).choose_spec.symm.trans (congrArg (fun i : pairWords d e =>
      sylowWords i.val) hxy)).trans (hword y).choose_spec
  have hcard : 8 ≤ (pairWords d e).card := by
    have hh := Nat.card_le_card_of_injective f hf
    exact hc.trans (by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hh)
  have hle : A ≤ D 6 := by
    intro g hg
    obtain ⟨i,hi⟩ := hword ⟨g,hg⟩
    obtain ⟨j,hj⟩ := pair_certificate d e hde hcard i.val i.property
    exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨j,hj.trans hi⟩
  exact eq_of_le_of_card_ge hle (by
    change Nat.card (disjointTranspositions 6 3) ≤ Nat.card A
    rw [show Nat.card (disjointTranspositions 6 3) = 8 from card_disjointTranspositions 3]
    exact hc)

private theorem large_small_conjugate (A : Subgroup S) (u : S)
    (hA : A ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hc : 8 ≤ Nat.card A) (hd : fixedCodim ρ A ≤ 2) :
    A = (D 6).map (MulAut.conj u).toMonoidHom := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (B : Subgroup S) : (B.map (MulAut.conj u).toMonoidHom).map f = B := by
    rw [map_map]
    have he : f.comp (MulAut.conj u).toMonoidHom = MonoidHom.id S := by
      ext x
      simp [f]
    rw [he,map_id]
  have he := large_small_eq (A.map f) ((map_mono hA).trans_eq (back _))
    (by rwa [card_map_of_injective (MulAut.conj u⁻¹).injective])
    (by rwa [fixedCodim_map_conj])
  apply (map_injective (f := f) (MulAut.conj u⁻¹).injective)
  rw [he,back]

private theorem sylow_small_movers {H : Type*} [Group H] [Finite H]
    (T U : Subgroup H) (f : H →* S) (u : S) (hk : f.ker ≤ T)
    (hfix : U ≤ centralizer (f.ker : Set H))
    (hT : T.map f = sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hbounds : ∀ A : Subgroup H,
      2 ^ fixedCodim ρ (A.map f) ≤ (centralizer (A : Set H)).relIndex U ∧
      (centralizer (A : Set H)).relIndex U ≤
        2 ^ fixedCodim (coreRepresentation (Fin 6)) (A.map f)) :
    let F := T ⊓ ((D 6).map (MulAut.conj u).toMonoidHom).comap f
    SmallMover.Maximal U f.ker T 4 = {F} ∧
      SmallMover.join U f.ker T 4 = F ∧ f.ker.relIndex F = 8 := by
  let D' := (D 6).map (MulAut.conj u).toMonoidHom
  let F := T ⊓ D'.comap f
  have hD : D' ≤ T.map f := by
    rw [hT]
    exact map_mono D_le_sylowCarrier
  have hF : F.map f = D' := by
    apply le_antisymm
    · exact (map_mono inf_le_right).trans (map_comap_le _ _)
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := hD hy
      exact mem_map_of_mem f ⟨hx,hy⟩
  have hkF : f.ker ≤ F := le_inf hk (ker_le_comap _ _)
  have hDc : Nat.card D' = 8 := by
    rw [card_map_of_injective (MulAut.conj u).injective]
    exact card_disjointTranspositions 3
  have hFi : f.ker.relIndex F = 8 := by rw [relIndex_ker,hF,hDc]
  have hFsmall : SmallMover.Admissible U f.ker T 4 F := by
    have hb := (hbounds F).2
    rw [hF,fixedCodim_map_conj,fixedCodim_D.2.2.1] at hb
    exact ⟨inf_le_left,by rw [hFi]; exact hb.trans (by decide),hb⟩
  have hbound (A : Subgroup H) (ha : SmallMover.Admissible U f.ker T 4 A) :
      Nat.card (A.map f) ≤ 8 := by
    by_cases h8 : 8 ≤ Nat.card (A.map f)
    · have hc : fixedCodim ρ (A.map f) ≤ 2 := by
        have hh := (hbounds A).1.trans ha.2.2
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
      rw [large_small_conjugate _ u ((map_mono ha.1).trans_eq hT) h8 hc]
      exact hDc.le
    · omega
  have hmax : SmallMover.Maximal U f.ker T 4 = {F} := by
    ext A
    rw [SmallMover.maximal_iff_image_maximal f U T 4 hk hfix]
    constructor
    · rintro ⟨ha,hkA,hm⟩
      have h8 : 8 ≤ Nat.card (A.map f) := by
        simpa only [hF,hDc] using hm F hFsmall
      have hc : fixedCodim ρ (A.map f) ≤ 2 :=
        (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((hbounds A).1.trans ha.2.2)
      have he : A.map f = F.map f :=
        (large_small_conjugate _ u ((map_mono ha.1).trans_eq hT) h8 hc).trans hF.symm
      exact Set.mem_singleton_iff.mpr (map_injective_of_ker_le f hkA hkF he)
    · rintro rfl
      exact ⟨hFsmall,hkF,fun B hB => (hbound B hB).trans_eq (hF ▸ hDc).symm⟩
  exact ⟨hmax,by rw [SmallMover.join,hmax,sSup_singleton],hFi⟩


open scoped IsMulCommutative

private theorem small_image_le_cube (A : Subgroup S) (hA : A ≤ sylowCarrier)
    (hsmall : fixedCodim ρ A ≤ 1) : A ≤ D 6 := by
  by_cases he : A = ⊥
  · rw [he]; exact bot_le
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers A he hsmall
  obtain ⟨i,hi⟩ := (mem_sylowCarrier_iff t).mp (hA ht)
  have hc : (sylowWords i).support.card = 2 := hi ▸ Equiv.Perm.card_support_eq_two.mpr hs
  have hcert : ∀ i : Fin 16, (sylowWords i).support.card = 2 →
      ∃ j : Fin 8, dWords j = sylowWords i := by decide +kernel
  obtain ⟨j,hj⟩ := hcert i hc
  rw [he]
  exact zpowers_le.mpr ((mem_disjointTranspositions_iff (3 : Fin 4) t).mpr ⟨j,hj.trans hi⟩)

private theorem small_image_centralized (A : Subgroup S) (u : S)
    (hA : A ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hsmall : fixedCodim ρ A ≤ 1) :
    A ≤ (D 6).map (MulAut.conj u).toMonoidHom ∧
      (D 6).map (MulAut.conj u).toMonoidHom ≤ centralizer (A : Set S) := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  let g := (MulAut.conj u).toMonoidHom
  have back (B : Subgroup S) : (B.map g).map f = B := by
    rw [map_map]
    have he : f.comp g = MonoidHom.id S := by ext x; simp [f,g]
    rw [he,map_id]
  have hAD : A.map f ≤ D 6 := small_image_le_cube _
    ((map_mono hA).trans_eq (back _)) (by rwa [fixedCodim_map_conj])
  have hAD' : A ≤ (D 6).map g := by
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj u⁻¹).injective).mp
    rwa [back]
  let : IsElementaryAbelian 2 (D 6) := elementary_disjointTranspositions (3 : Fin 4)
  let : IsElementaryAbelian 2 ((D 6).map g) := IsElementaryAbelian.map _
  exact ⟨hAD',fun x hx y hy => setLike_mul_comm (hAD' hy) hx⟩

private theorem maximal_map_singleton {H K : Type*} [Group H] [Group K]
    (i : H →* K) (hi : Function.Injective i) (U Q T F : Subgroup H)
    (hm : SmallMover.Maximal U Q T 4 = {F}) :
    SmallMover.Maximal (U.map i) (Q.map i) (T.map i) 4 = {F.map i} := by
  ext E
  constructor
  · intro hE
    have hEr : E ≤ i.range := hE.1.1.trans (map_le_range _ _)
    have hEm : (E.comap i).map i = E := map_comap_eq_self hEr
    have he : E.comap i ∈ SmallMover.Maximal U Q T 4 :=
      (SmallMover.maximal_map_iff i hi U Q T _ 4).mp (hEm.symm ▸ hE)
    rw [hm,Set.mem_singleton_iff] at he
    exact Set.mem_singleton_iff.mpr (hEm.symm.trans (congrArg (Subgroup.map i) he))
  · rintro rfl
    exact (SmallMover.maximal_map_iff i hi U Q T F 4).mpr (hm.symm ▸ Set.mem_singleton _)

open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- The literal radical normalizer has one maximum-order small mover,
with image order eight, normalizer index two and moved-cover fixed index four. -/
theorem normalizer_small_movers_knownSimple
    (hb : 4 < replacementDistance h d) :
    let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    let N := normalizer (d.radical : Set d.overgroup)
    ∃ u : S,
      N.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom ∧
      let F := N ⊓ ((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection
      SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) N 4 = {F} ∧
      SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 = F ∧
      F.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom ∧
      (pCore 2 d.overgroup).relIndex F = 8 ∧ F.relIndex N = 2 ∧
      (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) = 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let N := normalizer (d.radical : Set d.overgroup)
  obtain ⟨_,⟨W,hW⟩,_⟩ := SylowSmallNormalizer.four_lt_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  let P := W.mapSurjective s.surjective
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq S sylow P
  have hN : N.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    have hh := congrArg (fun W : Sylow 2 S => (W : Subgroup S)) hu
    change sylowCarrier.map (MulAut.conj u).toMonoidHom =
      (W : Subgroup d.overgroup).map s.projection at hh
    rw [hW] at hh
    exact hh.symm
  have hk : s.projection.ker ≤ N := by
    rw [s.projection_kernel]
    exact (replacement_core_le_radical h d).trans d.radical.le_normalizer
  have hfix : replacementMoved d ≤ centralizer (s.projection.ker : Set d.overgroup) := by
    rw [s.projection_kernel,←moved_centralizer s]
    exact le_centralizer_iff.mpr le_rfl
  have hbds (A : Subgroup d.overgroup) :
      2 ^ fixedCodim ρ (A.map s.projection) ≤
        (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ∧
      (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤
        2 ^ fixedCodim (coreRepresentation (Fin 6)) (A.map s.projection) := by
    let := replacementMoved_normal h d
    rw [centralizer_index_eq_fixedCodim (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)]
    have hh := (cover_model s).fixedCodim_bounds (A.map s.projection)
    simp only [Subgroup.map_id] at hh
    exact ⟨Nat.pow_le_pow_right (by decide) hh.1,Nat.pow_le_pow_right (by decide) hh.2⟩
  let F := N ⊓ ((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection
  have hm := sylow_small_movers N (replacementMoved d) s.projection u hk hfix hN hbds
  dsimp only at hm
  rw [s.projection_kernel] at hm
  have hD : (D 6).map (MulAut.conj u).toMonoidHom ≤ N.map s.projection := by
    rw [hN]
    exact map_mono D_le_sylowCarrier
  have hF : F.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    apply le_antisymm ((map_mono inf_le_right).trans (map_comap_le _ _))
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hD hy
    exact mem_map_of_mem s.projection ⟨hx,hy⟩
  have hkF : s.projection.ker ≤ F := le_inf hk (ker_le_comap _ _)
  have hidx : F.relIndex N = 2 := by
    have hi := relIndex_mul_relIndex s.projection.ker F N hkF inf_le_left
    rw [s.projection_kernel,hm.2.2] at hi
    have hNi : (pCore 2 d.overgroup).relIndex N = 16 := by
      rw [←s.projection_kernel,relIndex_ker,hN,
        card_map_of_injective (MulAut.conj u).injective,card_sylowCarrier]
    rw [hNi] at hi
    omega
  refine ⟨u,hN,hm.1,hm.2.1,hF,hm.2.2,hidx,?_⟩
  have hh := hbds F
  rw [hF,fixedCodim_map_conj,fixedCodim_map_conj,
    fixedCodim_D.2.2.1,fixedCodim_D.2.2.2] at hh
  change (centralizer (F : Set d.overgroup)).relIndex (replacementMoved d) = 4
  norm_num at hh
  omega


include e hz hn in
/-- Every small actor in the replacement radical lies in that maximum and
commutes with it modulo the actual starting two-core. -/
theorem normalizer_small_movers_small_action_knownSimple
    (hb : 4 < replacementDistance h d)
    (A : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup)
      (normalizer (d.radical : Set d.overgroup)) 4
    A ≤ J ∧ ⁅J,A⁆ ≤ pCore 2 d.overgroup := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let N := normalizer (d.radical : Set d.overgroup)
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4
  obtain ⟨u,hN,_,hJ,hF,_,_,_⟩ := normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  change J = _ at hJ
  have hJmap : J.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [hJ]
    exact hF
  have hnat : fixedCodim ρ (A.map s.projection) ≤ 1 := by
    let := replacementMoved_normal h d
    rw [centralizer_index_eq_fixedCodim (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hidx
    have hh := (cover_model s).fixedCodim_bounds (A.map s.projection)
    simp only [Subgroup.map_id] at hh
    exact hh.1.trans ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx)
  have hAD := small_image_centralized _ u
    ((map_mono (hA.trans d.radical.le_normalizer)).trans_eq hN) hnat
  have hAJ : A ≤ J := by
    rw [hJ]
    exact le_inf (hA.trans d.radical.le_normalizer) (map_le_iff_le_comap.mp hAD.1)
  have hmap : (⁅J,A⁆ : Subgroup d.overgroup).map s.projection = ⊥ := by
    rw [map_commutator,hJmap]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hAD.2
  exact ⟨hAJ,((Subgroup.map_eq_bot_iff _).mp hmap).trans_eq s.projection_kernel⟩


include e hz hn in
/-- The unique maximum and its small-actor control on every actual edge,
transported through the literal local embedding. -/
theorem edge_normalizer_small_movers_knownSimple
    (hb : 4 < replacementDistance h d)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
    ∃ J : Subgroup (FreeAmalgam d.radical),
      SmallMover.Maximal (U d.radical a) (Q d.radical a) T 4 = {J} ∧
      SmallMover.join (U d.radical a) (Q d.radical a) T 4 = J ∧
      Q d.radical a ≤ J ∧ J ≤ T ∧
      (Q d.radical a).relIndex J = 8 ∧ J.relIndex T = 2 ∧
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = 4 ∧
      ∀ A : Subgroup (FreeAmalgam d.radical), A ≤ Q d.radical t →
        (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ 2 →
        A ≤ J ∧ ⁅J,A⁆ ≤ Q d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let N := normalizer (d.radical : Set d.overgroup)
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧ d.radical.map i = Q d.radical t ∧
      (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨hga,hgt⟩
      rw [hga,hgt]
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · rw [MonoidHom.range_comp]
        have he : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
          (stabilizer_m_base d.radical).symm
        rw [he]
        simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act d.radical g (alpha d.radical)).symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at ha
      cases ha
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := hcoords
  have hiN : N.map i = T := by
    have hh : (normalizer (d.radical.map i : Set _)).comap i = N := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
        comap_map_eq_self_of_injective hinj]
    rw [←hh,map_comap_eq,hiR,hir,inf_comm]
  obtain ⟨u,hN,hm,hj,hF,hFi,hNi,hfixed⟩ := normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  let F := N ⊓ ((D 6).map (MulAut.conj u).toMonoidHom).comap s.projection
  have hFm : SmallMover.Maximal (replacementMoved d) (pCore 2 d.overgroup) N 4 = {F} := hm
  have hFj : SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 = F := hj
  have hQF : pCore 2 d.overgroup ≤ F := by
    rw [←s.projection_kernel]
    exact le_inf ((s.projection_kernel ▸ replacement_core_le_radical h d).trans d.radical.le_normalizer)
      (ker_le_comap _ _)
  refine ⟨F.map i,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := maximal_map_singleton i hinj _ _ _ _ hFm
    rwa [hiU,hiQ,hiN] at hh
  · have hh := SmallMover.join_map i hinj (replacementMoved d) (pCore 2 d.overgroup) N 4
    rw [hFj,hiU,hiQ,hiN] at hh
    exact hh.symm
  · rw [←hiQ]
    exact map_mono hQF
  · change F.map i ≤ T
    rw [←hiN]
    exact map_mono inf_le_left
  · rw [←hiQ,relIndex_map_map_of_injective _ _ hinj]
    exact hFi
  · change (F.map i).relIndex T = 2
    rw [←hiN,relIndex_map_map_of_injective _ _ hinj]
    exact hNi
  · rw [←hiU,SmallMover.centralizer_index_map i hinj]
    exact hfixed
  · intro A hA hidx
    have hAr : A ≤ i.range := hA.trans (hiR ▸ map_le_range i d.radical)
    have hAm : (A.comap i).map i = A := map_comap_eq_self hAr
    have hA₀ : A.comap i ≤ d.radical := by
      have hh := comap_mono (f := i) hA
      rw [←hiR,comap_map_eq_self_of_injective hinj] at hh
      exact hh
    have hidx₀ : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
      rw [←hAm,←hiU,SmallMover.centralizer_index_map i hinj] at hidx
      exact hidx
    have hh := normalizer_small_movers_small_action_knownSimple
      (e := e) (hz := hz) (hn := hn) hb (A.comap i) hA₀ hidx₀
    change A.comap i ≤ SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4 ∧
      ⁅SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) N 4,A.comap i⁆ ≤ _ at hh
    rw [hFj] at hh
    have hh₁ := map_mono (f := i) hh.1
    rw [hAm] at hh₁
    have hh₂ := map_mono (f := i) hh.2
    rw [map_commutator,hAm,hiQ] at hh₂
    exact ⟨hh₁,hh₂⟩

include e hz hn in
/-- The small-mover maximum fixes the critical line and normalizes the full
critical kernel. When the line moves, it is exactly the relative kernel normalizer. -/
theorem small_critical_kernel_small_movers_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    J.relIndex T = 2 ∧
      J ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      J ≤ normalizer ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((¬ T ≤ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
          Subgroup (FreeAmalgam d.radical)) : Set _)) →
        T ⊓ normalizer ((Z d.radical a ⊓ Q d.radical a' :
          Subgroup (FreeAmalgam d.radical)) : Set _) = J) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let t := p.walk.getVert 1
  let T := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical a
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨J₀,_,hJ₀,_,hJT,_,hJi,_,hact⟩ := edge_normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  change J = J₀ at hJ₀
  rw [←hJ₀] at hJT hJi hact
  have hAt : Z d.radical a' ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hidx : (centralizer (Z d.radical a' : Set _)).relIndex (U d.radical a) ≤ 2 := by
    let := finite_Z d.radical a
    let : Finite (U d.radical a) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
    have hC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
    exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices s hc p hsmall).1
  have hcomm : ⁅J,Z d.radical a'⁆ ≤ centralizer (Z d.radical a : Set _) :=
    (hact _ hAt hidx).2.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color)))
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hJn : J ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    dsimp only [D]
    rw [commutator_comm (Z d.radical a)]
    exact SylowNormalizer.fixed_mod_central_normalizes (Z d.radical a') (Z d.radical a) J
      (hAG.trans (Z_normalized d.radical a))
      ((hJT.trans inf_le_right).trans (Z_normalized d.radical a)) hcomm
  have hJc : J ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    hJn.trans (normalizer_le_centralizer_of_card_two _
      (small_critical_commutator_card s hc p hsmall))
  have hJk : J ≤ normalizer
      ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := le_inf (hJT.trans inf_le_right) hJc
    rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
    exact hh.trans inf_le_right
  refine ⟨hJi,hJc,hJk,?_⟩
  intro hmove
  let H := T ⊓ normalizer
    ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _)
  have hJH : J ≤ H := le_inf hJT hJk
  have hHG : H ≤ stabilizer d.radical a := inf_le_left.trans inf_le_right
  have hHC : H ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    have hh := le_inf hHG (show H ≤ normalizer
      ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set _) from inf_le_right)
    rw [small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
    exact hh.trans inf_le_right
  let := finite_stabilizer d.radical a
  let : Finite T := Finite.of_injective (inclusion (show T ≤ stabilizer d.radical a from inf_le_right))
    (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion (show H ≤ T from inf_le_left)) (inclusion_injective _)
  have hpos : 0 < H.relIndex T := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hne : H.relIndex T ≠ 1 := fun he => hmove ((relIndex_eq_one.mp he).trans hHC)
  have hjpos : 0 < J.relIndex H := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have htwo : 2 ≤ H.relIndex T := by omega
  have hi := relIndex_mul_relIndex J H T hJH inf_le_left
  rw [hJi] at hi
  have he : J.relIndex H = 1 := by nlinarith
  exact le_antisymm (relIndex_eq_one.mp he) hJH



include e hz hn in
/-- The relative normalizer's small-mover group contains the full critical endpoint seed.
Consequently it generates the starting stabilizer with a selected neighboring
relative normalizer, including the fixed-line branch. -/
theorem small_mover_generating_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    Z d.radical a' ≤ J ∧
      ∃ t, Adjacent d.radical a t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical a) ⊔ J = stabilizer d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨J,_,hj,_,hJT,_,_,_,hact⟩ := edge_normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hidx : (centralizer (Z d.radical a' : Set _)).relIndex (U d.radical a) ≤ 2 := by
    let := finite_Z d.radical a
    let : Finite (U d.radical a) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
    have hC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
    exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices s hc p hsmall).1
  have hAJ := (hact _ hAt hidx).1
  obtain ⟨⟨P,hP⟩,_,_⟩ := SylowTerminal.four_lt_original_sylow_non_elementary_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  obtain ⟨t,hat,hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_at_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) P hP p
  dsimp only
  rw [hj]
  refine ⟨hAJ,t,hat,le_antisymm (sup_le inf_le_right (hJT.trans inf_le_right)) ?_⟩
  exact hgen.ge.trans (sup_le_sup_left hAJ _)

include e hz hn in
/-- In the order-sixteen image branch the relative normalizer is the
replacement edge core itself. Its source small-mover family is therefore
exactly the full critical-kernel normalizer when the critical line moves. -/
theorem sixteen_edge_small_movers_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ Q d.radical (p.walk.getVert 1) ≤
      centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let H := T ⊓ normalizer ((Z d.radical a ⊓ Q d.radical a' :
      Subgroup (FreeAmalgam d.radical)) : Set _)
    SmallMover.Maximal (U d.radical a) (Q d.radical a) T 4 = {H} ∧
      SmallMover.join (U d.radical a) (Q d.radical a) T 4 = H ∧ H.relIndex T = 2 ∧
      ∃ t, Adjacent d.radical a t ∧ Q d.radical t ⊔ H = stabilizer d.radical a := by
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  obtain ⟨J,hm,hj,_,_,_,hi,_,_⟩ := edge_normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p.start_color hat
  have hk := small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hm hj hi hk ⊢
  rw [hT] at hm hj hi hk
  have he := (hk.2.2.2 hmove).trans hj
  rw [←he] at hm hj hi
  obtain ⟨_,v,hav,hgen⟩ := small_mover_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  rw [hT,hj,SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hav] at hgen
  exact ⟨hm,hj,hi,v,hav,hgen⟩

include e hz hn in
/-- Literal original-Sylow application under the replacement embedding.
The original radical is not replaced by the characteristic edge core. -/
theorem original_sylow_small_movers_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let J := SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical)) T 4
    J = T ⊓ normalizer ((Z d.radical (alpha d.radical) ⊓ Q d.radical a' :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧ J.relIndex T = 2 := by
  have hk := small_critical_kernel_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hk ⊢
  rw [hfirst,SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hk
  exact ⟨(hk.2.2.2 hmove).symm,hk.1⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS


