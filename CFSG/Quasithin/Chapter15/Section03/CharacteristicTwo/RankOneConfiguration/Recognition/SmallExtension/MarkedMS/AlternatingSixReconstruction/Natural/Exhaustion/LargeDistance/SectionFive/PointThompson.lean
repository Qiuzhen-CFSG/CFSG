module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FourOffenderImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreNormal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.TerminalLine


/-!
# Thompson and Baumann images in the point-contained branches

At distance greater than two, an order-four natural offender lies in the
actual elementary Thompson image. Inside a marked point core every such
offender contains its unique transposition. The explicit subgroup lattice
then leaves only the three mixed planes or the full point core.

The normalizer of the radical image normalizes its Thompson image: lift a
normalizer through the surjective quotient and use that the radical contains
the quotient kernel. In the full-core case the even point stabilizer therefore
normalizes the Thompson image. Its three-cycle permutes the mixed planes,
forcing that image to be full. In a proper point core the order-four offender
already fills the mixed plane. In both cases the Thompson, Baumann and radical
images coincide under the original canonical projection.

Pulling these equalities back gives actual core supplements on every minimum
characteristic replacement. The existing full-point distance bound further
shows that distance greater than four in the point-contained branch requires
the same literal mixed-plane image for all three subgroups. Both central
covers and the original nonsylow radical are retained.

This does not exclude the mixed-plane case or the full-point distance-four
configuration. The residual-core estimates and radical images outside every
point core remain with the large-distance assembly owner.

Source: Aschbacher--Smith B.3.4, printed pp.84--85; Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), the Thompson-image analysis in
Section 5, printed pp.913--927. This is an image reduction for that argument,
not a proof of the source normalization and selection in (5.12).
-/

public noncomputable section

open Subgroup Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace PointThompson
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)

private theorem thompson_image_normalizer {H : Type*} [Group H]
    (q : H →* S) (hq : Function.Surjective q) (R : Subgroup H)
    (hk : q.ker ≤ R) :
    normalizer (R.map q : Set S) ≤
      normalizer ((Stellmacher.elementaryAbelianMaxJ R).map q : Set S) := by
  intro g hg
  obtain ⟨x,rfl⟩ := hq g
  have hx : x ∈ normalizer (R : Set H) := by
    have hh := le_normalizer_comap q hg
    rwa [Subgroup.comap_map_eq,sup_eq_left.mpr hk] at hh
  have hJ : x ∈ normalizer (Stellmacher.elementaryAbelianMaxJ R : Set H) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ R).map (MulAut.conj x).toMonoidHom = _
    have he : R.map (MulAut.conj x).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp hx
    rw [←Stellmacher.elementaryAbelianMaxJ_map_equiv,
      he]
  exact le_normalizer_map q (mem_map_of_mem q hJ)

private theorem point_thompson_equal {H : Type*} [Group H] [Finite H]
    (q : H →* S) (hq : Function.Surjective q) (R : Subgroup H)
    (hk : q.ker ≤ R) (hpoint : R.map q ≤ pointCore)
    (A : Subgroup S) (hAJ : A ≤ (Stellmacher.elementaryAbelianMaxJ R).map q)
    (hcard : Nat.card A = 4) (hoff : IsOffender ρ A) :
    (Stellmacher.elementaryAbelianMaxJ R).map q = R.map q ∧
      (CFSG.Quasithin.ChapterB.baumann R).map q = R.map q ∧
      (R.map q = pointCore ∨ IsConjugateTo (R.map q) plus) := by
  let J := (Stellmacher.elementaryAbelianMaxJ R).map q
  have hJR : J ≤ R.map q := map_mono (sSup_le fun _ hE => hE.1)
  have hAE : A ≤ exceptional 6 (by decide) :=
    ((hAJ.trans hJR).trans hpoint).trans_eq
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional
  have hswapA : pairSwap 6 2 ∈ A := (exceptional_last_mem_iff hAE).mpr
    ((caseBFamily_le_exceptional_iff hAE).mp ((isOffender_natural_iff A).mp hoff))
  have hswapJ : swap45 ∈ J := hAJ hswapA
  have hlarge : 4 ≤ Nat.card J := hcard ▸ card_le_of_le hAJ
  have hRE : R.map q ≤ exceptional 6 (by decide) := hpoint.trans_eq
    CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional
  have hcases := (exceptional_last_mem_iff hRE).mp (hJR hswapJ)
  have hchoice : (R.map q = pointCore) ∨
      (Nat.card (R.map q) = 4 ∧ IsConjugateTo (R.map q) plus) := by
    rcases hcases with he | he | he | he | he
    · have hh := card_le_of_le hJR
      rw [he,card_last] at hh
      omega
    · rw [he]
      exact Or.inr ⟨card_plus,IsConjugateTo.refl _⟩
    · rw [he]
      exact Or.inr ⟨mixedSecond_conjugate_plus.card_eq.trans card_plus,
        mixedSecond_conjugate_plus⟩
    · rw [he]
      exact Or.inr ⟨mixedThird_conjugate_plus.card_eq.trans card_plus,
        mixedThird_conjugate_plus⟩
    · exact Or.inl (he.trans
        CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm)
  have hJ : J = R.map q := by
    rcases hchoice with he | ⟨he,_⟩
    · rw [he]
      refine PointCoreNormal.eq_core J (hJR.trans hpoint) ?_ hswapJ ?_
      · have hn : K ≤ normalizer (R.map q : Set S) := by
          rw [he,←H1_core_eq_pointCore]
          exact K_le_H1.trans (H1.le_normalizer.trans
            (normalizer_le_normalizer_characteristic_image H1 (pCore 2 H1)))
        exact hn.trans (thompson_image_normalizer q hq R hk)
      · intro hle
        have hh := card_le_of_le hle
        have ht : Nat.card (zpowers swap45) = 2 := by
          rw [Nat.card_zpowers]
          exact (show swap45.IsSwap from ⟨4,5,by decide,rfl⟩).orderOf
        rw [ht] at hh
        omega
    · exact eq_of_le_of_card_ge hJR (he ▸ hlarge)
  refine ⟨hJ,?_,hchoice.imp id (fun hc => hc.2)⟩
  exact le_antisymm (map_mono inf_le_left)
    (hJ ▸ map_mono (CFSG.Quasithin.ChapterB.elementaryAbelianMaxJ_le_baumann R))

private theorem conjugate_back (A : Subgroup S) (u : S) :
    (A.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      MonoidHom.id S := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,map_id]

end PointThompson

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)
local notation "ρ" => naturalRepresentation (Fin 6)

/-- At large distance with point-core containment, the three actual images
coincide. The radical image is the prescribed full point core or a conjugate
of the order-four mixed plane, with its actual conjugator retained. -/
theorem large_distance_point_images_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (hpoint : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      pointCore.map (MulAut.conj u).toMonoidHom) :
    (Stellmacher.elementaryAbelianMaxJ d.radical).map
        (SourceReduction.projection h e hz hn d) =
      d.radical.map (SourceReduction.projection h e hz hn d) ∧
    (CFSG.Quasithin.ChapterB.baumann d.radical).map
        (SourceReduction.projection h e hz hn d) =
      d.radical.map (SourceReduction.projection h e hz hn d) ∧
    (d.radical.map (SourceReduction.projection h e hz hn d) =
        pointCore.map (MulAut.conj u).toMonoidHom ∨
      ∃ g : S, d.radical.map (SourceReduction.projection h e hz hn d) =
        plus.map (MulAut.conj g).toMonoidHom) := by
  let π := SourceReduction.projection h e hz hn d
  let c := (MulAut.conj u⁻¹).toMonoidHom
  let q := c.comp π
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hπ : Function.Surjective π := by
    have hs := s.surjective
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hs
  have hq : Function.Surjective q := (MulAut.conj u⁻¹).surjective.comp hπ
  have hk : q.ker ≤ d.radical := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj u⁻¹).injective,
      SourceReduction.projection_kernel h e hz hn d]
    exact replacement_core_le_radical h d
  have hR : d.radical.map q ≤ pointCore := by
    rw [←map_map]
    exact (map_mono hpoint).trans_eq (PointThompson.conjugate_back pointCore u)
  obtain ⟨A,hA,hcard,hoff⟩ := large_distance_thompson_contains_four_offender_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hAq : A.map c ≤ (Stellmacher.elementaryAbelianMaxJ d.radical).map q := by
    rw [←map_map]
    exact map_mono hA
  have hcardq : Nat.card (A.map c) = 4 := by
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective,hcard]
  have hoffq : IsOffender ρ (A.map c) :=
    ⟨hoff.1.map_conj _,by rw [fixedCodim_map_conj,rank_map_conj];exact hoff.2⟩
  obtain ⟨hJ,hB,hcases⟩ := PointThompson.point_thompson_equal q hq d.radical hk hR
    (A.map c) hAq hcardq hoffq
  rw [←map_map,←map_map] at hJ hB
  refine ⟨(map_injective (MulAut.conj u⁻¹).injective) hJ,
    (map_injective (MulAut.conj u⁻¹).injective) hB,?_⟩
  rcases hcases with he | ⟨g,hg⟩
  · left
    apply map_injective (f := (MulAut.conj u⁻¹).toMonoidHom) (MulAut.conj u⁻¹).injective
    rw [PointThompson.conjugate_back,map_map]
    exact he
  · right
    have hconj : IsConjugateTo (d.radical.map π) (d.radical.map q) := by
      refine ⟨u,?_⟩
      rw [show q = c.comp π from rfl,←map_map]
      simpa only [inv_inv] using (PointThompson.conjugate_back (d.radical.map π) u⁻¹).symm
    exact hconj.trans ⟨g,hg⟩

/-- Beyond distance four, the point-contained branch has exactly a mixed
plane as radical, Thompson and Baumann image in the same marking. -/
theorem four_lt_point_image_mixed_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (hpoint : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ g : S,
      d.radical.map (SourceReduction.projection h e hz hn d) =
        plus.map (MulAut.conj g).toMonoidHom ∧
      (Stellmacher.elementaryAbelianMaxJ d.radical).map
          (SourceReduction.projection h e hz hn d) =
        plus.map (MulAut.conj g).toMonoidHom ∧
      (CFSG.Quasithin.ChapterB.baumann d.radical).map
          (SourceReduction.projection h e hz hn d) =
        plus.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hJ,hB,hcases⟩ := large_distance_point_images_knownSimple (by omega) u hpoint
  rcases hcases with he | ⟨g,hg⟩
  · exact (Nat.not_le_of_gt hb (full_point_distance_le_four_knownSimple u he)).elim
  · exact ⟨g,hg,hJ.trans hg,hB.trans hg⟩

/-- On the actual replacement carrier, the ambient two-core supplements
both the elementary Thompson subgroup and the Baumann subgroup. These are
literal subgroup equalities, with no assumption that the radical is Sylow. -/
theorem point_radical_thompson_supplements_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (hpoint : d.radical.map (SourceReduction.projection h e hz hn d) ≤
      pointCore.map (MulAut.conj u).toMonoidHom) :
    d.radical = pCore 2 d.overgroup ⊔ Stellmacher.elementaryAbelianMaxJ d.radical ∧
      d.radical = pCore 2 d.overgroup ⊔ CFSG.Quasithin.ChapterB.baumann d.radical := by
  obtain ⟨hJ,hB,_⟩ := large_distance_point_images_knownSimple hb u hpoint
  have pullback (A : Subgroup d.overgroup)
      (he : A.map (SourceReduction.projection h e hz hn d) =
        d.radical.map (SourceReduction.projection h e hz hn d)) :
      d.radical = pCore 2 d.overgroup ⊔ A := by
    have hh := congrArg (Subgroup.comap (SourceReduction.projection h e hz hn d)) he
    rw [Subgroup.comap_map_eq,Subgroup.comap_map_eq,
      SourceReduction.projection_kernel h e hz hn d,
      sup_eq_left.mpr (replacement_core_le_radical h d)] at hh
    exact hh.symm.trans (sup_comm _ _)
  exact ⟨pullback _ hJ,pullback _ hB⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
