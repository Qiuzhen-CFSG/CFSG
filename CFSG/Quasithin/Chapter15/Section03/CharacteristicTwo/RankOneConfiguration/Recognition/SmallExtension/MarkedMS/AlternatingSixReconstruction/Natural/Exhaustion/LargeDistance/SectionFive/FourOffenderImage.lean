module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BaumannImage
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Order-four offenders in the original Thompson image

Every six-letter natural offender is a transposition subgroup or contains
an offender of order four. In a two-subgroup, two distinct transposition
subgroups also generate an order-four offender: transport to the canonical
Sylow subgroup and use its three disjoint transpositions. Thus absence of
an order-four offender makes all nontrivial maximum-elementary images equal.
MS3 supplies one such image, so the whole elementary Thompson image has
order two. The checked small-Thompson argument then forces the actual
replacement distance to be two, including when the radical image is cyclic
of order greater than two.

Consequently every remaining large-distance replacement has an actual
order-four offender in its Thompson image. The six-letter classification
identifies it by literal conjugation as the two-swap group, the even part
of the three-pair group, or a mixed plane. These are subgroups of the given
quotient image; no elementary lift or full point-core equality is inferred.
The original nonsylow radical, both moved covers, and their central
attachments are retained. The general endpoint and opposite-core estimates
and the remaining larger-image exclusions are still required.

Source: Aschbacher--Smith B.3.4, printed pp.84--85, and C.1.24(c),
pp.130--131; MS93 Section 5, printed pp.912--927. This image reduction is
an additional route to the small-image branch, not a proof of (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace FourOffenderImage
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)

private theorem offender_conj {A : Subgroup S} (hA : IsOffender ρ A) (g : S) :
    IsOffender ρ (A.map (MulAut.conj g).toMonoidHom) :=
  ⟨hA.1.map_conj g,by rw [fixedCodim_map_conj,rank_map_conj]; exact hA.2⟩

private theorem initial_offender (i : Fin 4) (hi : 0 < i.val) :
    IsOffender ρ (disjointTranspositions 6 i.val) := by
  apply (isOffender_natural_iff _).mpr
  exact Or.inl (caseAFamily_disjointTranspositions hi (by omega))

private theorem plus_offender : IsOffender ρ plus := by
  apply (isOffender_natural_iff _).mpr
  exact (caseBFamily_iff plus).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (IsConjugateTo.refl _))))))

private theorem offender_four_or_small (A : Subgroup S) (hA : IsOffender ρ A) :
    Nat.card A = 2 ∨ ∃ B : Subgroup S, B ≤ A ∧ Nat.card B = 4 ∧ IsOffender ρ B := by
  have hf := (caseBFamily_iff A).mp ((isOffender_natural_iff A).mp hA)
  rcases hf with ⟨g,rfl⟩ | ⟨g,rfl⟩ | ⟨g,rfl⟩ | ⟨g,rfl⟩ | ⟨g,rfl⟩ | ⟨g,rfl⟩
  · left
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact card_disjointTranspositions 1
  · right
    refine ⟨_,le_rfl,?_,hA⟩
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact card_disjointTranspositions 2
  · right
    refine ⟨(disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom,
      map_mono (disjointTranspositions_le_D 6 2),?_,offender_conj (initial_offender 2 (by decide)) g⟩
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact card_disjointTranspositions 2
  · right
    refine ⟨plus.map (MulAut.conj g).toMonoidHom,map_mono plus_le_exceptional,?_,offender_conj plus_offender g⟩
    rw [card_map_of_injective (MulAut.conj g).injective,card_plus]
  · right
    refine ⟨_,le_rfl,?_,hA⟩
    rw [card_map_of_injective (MulAut.conj g).injective,card_evenPart]
  · right
    refine ⟨_,le_rfl,?_,hA⟩
    rw [card_map_of_injective (MulAut.conj g).injective,card_plus]

private theorem swap_sylow_certificate : ∀ k : Fin 16,
    (sylowWords k).support.card = 2 → ∃ i : Fin 3, sylowWords k = pairSwap 6 i := by decide +kernel

private theorem pair_certificate : ∀ i j : Fin 3, i ≠ j →
    ∃ g : S, (MulAut.conj g) (pairSwap 6 0) = pairSwap 6 i ∧
      (MulAut.conj g) (pairSwap 6 1) = pairSwap 6 j := by decide +kernel

private theorem two_swaps_four (B : Subgroup S) (i j : Fin 3) (hne : i ≠ j)
    (hi : pairSwap 6 i ∈ B) (hj : pairSwap 6 j ∈ B) :
    ∃ A : Subgroup S, A ≤ B ∧ Nat.card A = 4 ∧ IsOffender ρ A := by
  obtain ⟨g,hg0,hg1⟩ := pair_certificate i j hne
  refine ⟨(disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom,?_,?_,
    offender_conj (initial_offender 2 (by decide)) g⟩
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro t ⟨k,hk,rfl⟩
    have hh : k = 0 ∨ k = 1 := by fin_cases k <;> simp_all
    rcases hh with rfl | rfl
    · change (MulAut.conj g) (pairSwap 6 0) ∈ B
      rwa [hg0]
    · change (MulAut.conj g) (pairSwap 6 1) ∈ B
      rwa [hg1]
  · rw [card_map_of_injective (MulAut.conj g).injective]
    exact card_disjointTranspositions 2

private theorem no_four_conj (B : Subgroup S)
    (hno : ∀ A : Subgroup S, A ≤ B → Nat.card A = 4 → ¬ IsOffender ρ A) (g : S) :
    ∀ A : Subgroup S, A ≤ B.map (MulAut.conj g).toMonoidHom →
      Nat.card A = 4 → ¬ IsOffender ρ A := by
  intro A hAB hcard hoff
  let f := (MulAut.conj g).toMonoidHom
  let fi := (MulAut.conj g⁻¹).toMonoidHom
  have hid : fi.comp f = MonoidHom.id S := by
    ext x
    simp [fi,f,MulAut.conj_apply,mul_assoc]
  have hle : A.map fi ≤ B := by
    have hh := map_mono (f := fi) hAB
    rwa [map_map,hid,map_id] at hh
  exact hno (A.map fi) hle
    (by rw [card_map_of_injective (MulAut.conj g⁻¹).injective]; exact hcard)
    (offender_conj hoff g⁻¹)

private theorem offender_swap_of_card_two (A : Subgroup S) (hA : IsOffender ρ A)
    (hc : Nat.card A = 2) : ∃ t ∈ A, t.IsSwap ∧ A = zpowers t := by
  have hr : rank A = 1 := by change Nat.log 2 (Nat.card A) = 1; rw [hc]; decide
  exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
    A hA.1.1 (hA.2.trans_eq hr)

/-- In a two-subgroup with no order-four natural offender, all nontrivial
natural offenders are the same transposition subgroup. -/
private theorem offenders_unique_of_no_four (B : Subgroup S) (hp : IsPGroup 2 B)
    (hno : ∀ A : Subgroup S, A ≤ B → Nat.card A = 4 → ¬ IsOffender ρ A)
    {A D : Subgroup S} (hAB : A ≤ B) (hDB : D ≤ B)
    (hA : IsOffender ρ A) (hD : IsOffender ρ D) : A = D := by
  have ha : Nat.card A = 2 := (offender_four_or_small A hA).resolve_right (by
    rintro ⟨C,hCA,hc,ho⟩; exact hno C (hCA.trans hAB) hc ho)
  have hd : Nat.card D = 2 := (offender_four_or_small D hD).resolve_right (by
    rintro ⟨C,hCD,hc,ho⟩; exact hno C (hCD.trans hDB) hc ho)
  obtain ⟨t,ht,hts,heA⟩ := offender_swap_of_card_two A hA ha
  obtain ⟨r,hr,hrs,heD⟩ := offender_swap_of_card_two D hD hd
  obtain ⟨P,hBP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P sylow
  let f := (MulAut.conj g).toMonoidHom
  have hBs : B.map f ≤ sylowCarrier := by
    rintro _ ⟨b,hb,rfl⟩
    change (MulAut.conj g) b ∈ (sylow : Subgroup S)
    rw [←hg]
    exact mem_map_of_mem f (hBP hb)
  have htb : f t ∈ B.map f := mem_map_of_mem f (hAB ht)
  have hrb : f r ∈ B.map f := mem_map_of_mem f (hDB hr)
  have htc : (f t).support.card = 2 := by
    change (g*t*g⁻¹).support.card = 2
    rw [Equiv.Perm.card_support_conj]
    exact Equiv.Perm.card_support_eq_two.mpr hts
  have hrc : (f r).support.card = 2 := by
    change (g*r*g⁻¹).support.card = 2
    rw [Equiv.Perm.card_support_conj]
    exact Equiv.Perm.card_support_eq_two.mpr hrs
  obtain ⟨kt,hkt⟩ := (mem_sylowCarrier_iff _).mp (hBs htb)
  obtain ⟨kr,hkr⟩ := (mem_sylowCarrier_iff _).mp (hBs hrb)
  obtain ⟨i,hi⟩ := swap_sylow_certificate kt (by rwa [hkt])
  obtain ⟨j,hj⟩ := swap_sylow_certificate kr (by rwa [hkr])
  have hti : f t = pairSwap 6 i := hkt.symm.trans hi
  have hrj : f r = pairSwap 6 j := hkr.symm.trans hj
  have hij : i = j := by
    by_contra hne
    obtain ⟨C,hC,hc,ho⟩ := two_swaps_four (B.map f) i j hne (hti ▸ htb) (hrj ▸ hrb)
    exact no_four_conj B hno g C hC hc ho
  have htr : t = r := (MulAut.conj g).injective (hti.trans (hij ▸ hrj.symm))
  rw [heA,heD,htr]

private theorem four_offender_models (A : Subgroup S) (hc : Nat.card A = 4)
    (hoff : IsOffender ρ A) :
    IsConjugateTo A (disjointTranspositions 6 2) ∨
      IsConjugateTo A (evenPart 6) ∨ IsConjugateTo A plus := by
  rcases (caseBFamily_iff A).mp ((isOffender_natural_iff A).mp hoff) with ha | ha | ha | ha | ha | ha
  · have hh := ha.card_eq
    have htwo : Nat.card (disjointTranspositions 6 1) = 2 := card_disjointTranspositions 1
    rw [htwo,hc] at hh
    contradiction
  · exact Or.inl ha
  · have hh := ha.card_eq
    rw [show Nat.card (D 6) = 8 from card_disjointTranspositions 3,hc] at hh
    contradiction
  · have hh := ha.card_eq
    rw [card_exceptional,hc] at hh
    contradiction
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr ha)

end FourOffenderImage

open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)

/-- Absence of an order-four offender in the actual Thompson image forces
that entire image to have order two, irrespective of the radical image. -/
theorem thompson_image_card_two_of_no_four_offender
    (hno : ∀ A : Subgroup S, A ≤ (Stellmacher.elementaryAbelianMaxJ d.radical).map
      (SourceReduction.projection h e hz hn d) → Nat.card A = 4 → ¬ IsOffender ρ A) :
    Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map
      (SourceReduction.projection h e hz hn d)) = 2 := by
  let q := SourceReduction.projection h e hz hn d
  let J := (Stellmacher.elementaryAbelianMaxJ d.radical).map q
  obtain ⟨E,hE,hne,ho⟩ := SourceReduction.Cover.exists_maxElementary_offender h e hz hn d
  have hJE : E.map q ≤ J := map_mono (le_sSup hE)
  have hp : IsPGroup 2 J := ((replacement_radical_isPGroup h d).to_le
    (show Stellmacher.elementaryAbelianMaxJ d.radical ≤ d.radical from
      sSup_le fun _ hA => hA.1)).map q
  have hJne : ¬ Stellmacher.elementaryAbelianMaxJ d.radical ≤ q.ker := by
    intro hh
    apply hne
    rw [←SourceReduction.projection_kernel h e hz hn d]
    exact (le_sSup hE).trans hh
  have hEq : J = E.map q := ChapterB.thompson_image_of_unique_maximum_image d.radical q
    (E.map q) hJne (by
      intro F hF hnF
      have hFQ : ¬ F ≤ pCore 2 d.overgroup := by
        intro hh
        apply hnF
        apply (map_eq_bot_iff F).mpr
        rwa [SourceReduction.projection_kernel h e hz hn d]
      exact FourOffenderImage.offenders_unique_of_no_four J hp hno
        (map_mono (le_sSup hF)) hJE
        (SourceReduction.Cover.maxElementary_natural_offender h e hz hn d F hF hFQ) ho)
  have hcard := FourOffenderImage.offender_four_or_small (E.map q) ho
  have he : Nat.card (E.map q) = 2 := hcard.resolve_right (by
    rintro ⟨A,hA,hc,hoff⟩; exact hno A (hA.trans hJE) hc hoff)
  change Nat.card J = 2
  rw [hEq,he]

/-- All images without an order-four natural offender have distance two
on the original replacement, with both central covers retained. -/
theorem distance_eq_two_of_no_four_thompson_offender_knownSimple
    (hno : ∀ A : Subgroup S, A ≤ (Stellmacher.elementaryAbelianMaxJ d.radical).map
      (SourceReduction.projection h e hz hn d) → Nat.card A = 4 → ¬ IsOffender ρ A) :
    replacementDistance h d = 2 :=
  distance_eq_two_of_small_thompson_image_knownSimple
    (thompson_image_card_two_of_no_four_offender hno).le

/-- A remaining large-distance replacement has an actual order-four offender
inside its elementary Thompson image, in the unchanged natural marking. -/
theorem large_distance_thompson_contains_four_offender_knownSimple
    (hb : 2 < replacementDistance h d) :
    ∃ A : Subgroup S, A ≤ (Stellmacher.elementaryAbelianMaxJ d.radical).map
      (SourceReduction.projection h e hz hn d) ∧ Nat.card A = 4 ∧ IsOffender ρ A := by
  by_contra! hn
  have he := distance_eq_two_of_no_four_thompson_offender_knownSimple hn
  omega

/-- The remaining Thompson image contains one of three literal order-four
models: two disjoint transpositions, the even pair group, or a mixed plane.
The witness is conjugation inside the same six-letter quotient. -/
theorem large_distance_thompson_four_models_knownSimple
    (hb : 2 < replacementDistance h d) :
    ∃ g : S,
      (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom ≤
        (Stellmacher.elementaryAbelianMaxJ d.radical).map (SourceReduction.projection h e hz hn d) ∨
      (evenPart 6).map (MulAut.conj g).toMonoidHom ≤
        (Stellmacher.elementaryAbelianMaxJ d.radical).map (SourceReduction.projection h e hz hn d) ∨
      plus.map (MulAut.conj g).toMonoidHom ≤
        (Stellmacher.elementaryAbelianMaxJ d.radical).map (SourceReduction.projection h e hz hn d) := by
  obtain ⟨A,hA,hcard,hoff⟩ := large_distance_thompson_contains_four_offender_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  rcases FourOffenderImage.four_offender_models A hcard hoff with ⟨g,hg⟩ | ⟨g,hg⟩ | ⟨g,hg⟩
  · exact ⟨g,Or.inl (hg ▸ hA)⟩
  · exact ⟨g,Or.inr (Or.inl (hg ▸ hA))⟩
  · exact ⟨g,Or.inr (Or.inr (hg ▸ hA))⟩

/-- The corresponding exclusion can be checked in the whole radical image;
no equality between that image and its Thompson image is assumed. -/
theorem distance_eq_two_of_no_four_radical_offender_knownSimple
    (hno : ∀ A : Subgroup S, A ≤ d.radical.map (SourceReduction.projection h e hz hn d) →
      Nat.card A = 4 → ¬ IsOffender ρ A) : replacementDistance h d = 2 := by
  apply distance_eq_two_of_no_four_thompson_offender_knownSimple
  intro A hA hc
  exact hno A (hA.trans (map_mono (sSup_le fun _ hE => hE.1))) hc

/-- In particular, a cyclic radical image has distance two, even if its
order exceeds two. The radical itself is not assumed cyclic or Sylow. -/
theorem distance_eq_two_of_cyclic_radical_image_knownSimple
    (hcyc : IsCyclic (d.radical.map (SourceReduction.projection h e hz hn d))) :
    replacementDistance h d = 2 := by
  let := hcyc
  apply distance_eq_two_of_no_four_radical_offender_knownSimple (e := e) (hz := hz) (hn := hn)
  intro A hA hc ho
  let := ho.1.2
  let : IsCyclic A := isCyclic_of_injective (inclusion hA) (inclusion_injective _)
  have hd := IsElementaryAbelian.exponent_dvd_p 2 A
  rw [IsCyclic.exponent_eq_card,hc] at hd
  norm_num at hd

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
