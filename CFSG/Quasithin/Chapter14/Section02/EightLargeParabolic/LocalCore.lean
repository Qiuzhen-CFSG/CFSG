module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Setup
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality
public import Theory.SpecificGroups.Triality.ParabolicCoreExtraspecial
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.PCoreRestriction

/-!
# The marked triality cores in the original eight-field parabolic

An explicit isomorphism of the whole inclusion amalgam carries the original
Sylow to the model unipotent subgroup and identifies both embedded two-cores
with the actual root radicals. The first core is extraspecial of order 512.
The original central involutions lie in its center, so the common order two
identifies these subgroups inside G. Consequently Mc is literally C_G(z),
and every ambient normalizer of the first core lies in Mc.

The partner's core is contained in the first core by Sylow containment and
restriction of normal two-subgroups. The reverse inclusion, the possible cubic
field extension and ambient recognition remain to be proved. In particular this
module does not identify Mc with the first endpoint or claim all of 14.2.18.

Source: Aschbacher--Smith 14.2.16 and 14.2.18, printed pp.986--987
(`refs/quasithin.pdf`). The marked realization is the explicit earlier input
owned by qt-e-1427-eight-amalgam-recognition.
-/

@[expose] public noncomputable section


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

/-- The explicit earlier marked realization, including both commuting squares. -/
abbrev MarkedTriality (T : Sylow 2 G) (M Mc H : Subgroup G) :=
  RankTwoAmalgam.Iso (amalgam T M Mc H)
    (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters 1 Nat.zero_lt_one))

/-- The marked overlap identifies the original Sylow with the model unipotent
subgroup. Normality inside the Borel makes this independent of Sylow choices. -/
theorem middle_sylow_map [Finite G] (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) :
    (((T : Subgroup G).subgroupOf (H ⊓ secondParabolic T M Mc H)).map
      r.middle.toMonoidHom).map
      (borel (binaryParameters 1 Nat.zero_lt_one)).subtype =
        unipotent (binaryParameters 1 Nat.zero_lt_one) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  have hTB : (T : Subgroup G) ≤ H ⊓ secondParabolic T M Mc H :=
    le_inf hTH ((show (T : Subgroup G) ≤ sourceResidual M Mc ⊔ (T : Subgroup G) from le_sup_right).trans le_sup_left)
  let S := (T.subtype hTB).mapSurjective (f := r.middle.toMonoidHom) r.middle.surjective
  let U := (unipotentSylow P rfl).subtype (unipotent_le_borel P)
  let : (U : Subgroup (borel P)).Normal :=
    ConcreteBruhat.unipotent_normal_in_borel P rfl
  have hUS : (U : Subgroup (borel P)) ≤ (S : Subgroup (borel P)) :=
    U.isPGroup'.le_sylow_of_normal S
  have he : (S : Subgroup (borel P)) = (U : Subgroup (borel P)) :=
    U.is_maximal' S.isPGroup' hUS
  have hm := congrArg (Subgroup.map (borel P).subtype) he
  have hs : (S : Subgroup (borel P)) =
      ((T : Subgroup G).subgroupOf (H ⊓ secondParabolic T M Mc H)).map
        r.middle.toMonoidHom := rfl
  have hu : (U : Subgroup (borel P)) = (unipotent P).subgroupOf (borel P) := rfl
  rw [hs, hu, map_subgroupOf_eq_of_le (unipotent_le_borel P)] at hm
  exact hm

/-- The original Sylow has the order of the marked model unipotent subgroup. -/
theorem source_sylow_card [Finite G] (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) : Nat.card T = 4096 := by
  let P := binaryParameters 1 Nat.zero_lt_one
  have hTB : (T : Subgroup G) ≤ H ⊓ secondParabolic T M Mc H :=
    le_inf hTH ((show (T : Subgroup G) ≤ sourceResidual M Mc ⊔ (T : Subgroup G)
      from le_sup_right).trans le_sup_left)
  have hc := congrArg (fun X : Subgroup (Carrier P) => Nat.card X) (middle_sylow_map r hTH)
  rw [card_map_of_injective (borel P).subtype_injective,
    card_map_of_injective r.middle.injective,
    Nat.card_congr (subgroupOfEquivOfLe hTB).toEquiv,
    card_unipotent_binary P rfl] at hc
  norm_num only [P, binaryParameters_q, pow_one, Nat.reducePow] at hc
  exact hc

/-- Both endpoint embeddings agree in G on every element of the whole model Borel. -/
theorem marked_ambient_compatibility (r : MarkedTriality T M Mc H)
    (b : borel (binaryParameters 1 Nat.zero_lt_one)) :
    (r.left.symm ((ChapterF.GreenBook.LieModels.Triality.amalgam _).left b) : G) =
      (r.right.symm ((ChapterF.GreenBook.LieModels.Triality.amalgam _).right b) : G) := by
  have hl := congrArg H.subtype (r.symm.left_commutes b)
  have hr := congrArg (secondParabolic T M Mc H).subtype (r.symm.right_commutes b)
  exact hl.trans hr.symm

/-- The original embedded O₂(H), not an unattached model group. -/
def firstCoreEquiv (r : MarkedTriality T M Mc H) :
    H.pCoreIn 2 ≃* radical (binaryParameters 1 Nat.zero_lt_one) .arms :=
  ((pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm.trans
    (((r.left.subgroupMap (pCore 2 H)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 r.left))).trans
        (parabolicTwoCoreEquivRadical _ rfl .arms))

/-- The literal second-parabolic core retains the other root radical. -/
def secondCoreEquiv (r : MarkedTriality T M Mc H) :
    (secondParabolic T M Mc H).pCoreIn 2 ≃*
      radical (binaryParameters 1 Nat.zero_lt_one) .central :=
  ((pCore 2 (secondParabolic T M Mc H)).equivMapOfInjective
    (secondParabolic T M Mc H).subtype
    (secondParabolic T M Mc H).subtype_injective).symm.trans
    (((r.right.subgroupMap (pCore 2 (secondParabolic T M Mc H))).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 r.right))).trans
        (parabolicTwoCoreEquivRadical _ rfl .central))

theorem firstCore_extraspecial (r : MarkedTriality T M Mc H) :
    IsExtraspecial 2 (H.pCoreIn 2) :=
  IsExtraspecial.of_mulEquiv (firstCoreEquiv r).symm
    (arms_radical_extraspecial_at_two _ rfl (by simp only [binaryParameters_q, pow_one]))

theorem firstCore_card (r : MarkedTriality T M Mc H) : Nat.card (H.pCoreIn 2) = 512 :=
  (Nat.card_congr (firstCoreEquiv r).toEquiv).trans
    (RadicalCoordinates.radical_arms_card _ rfl)

theorem secondCore_card (r : MarkedTriality T M Mc H) :
    Nat.card ((secondParabolic T M Mc H).pCoreIn 2) = 2048 :=
  (Nat.card_congr (secondCoreEquiv r).toEquiv).trans
    (RadicalCoordinates.radical_central_card _ rfl)

/-- The center of the first core, embedded in the original ambient group. -/
def firstCoreCenter (H : Subgroup G) : Subgroup G :=
  (center (H.pCoreIn 2)).map (H.pCoreIn 2).subtype

variable [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- The source central involution group is exactly the embedded extraspecial center. -/
theorem source_firstCore_center (r : MarkedTriality T M Mc H) :
    firstCoreCenter H = centralInvolutions T := by
  have hHC := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).2
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZH : centralInvolutions T ≤ H := (centralInvolutions_le_sylow T).trans hH.1.1.2
  have hZQ : centralInvolutions T ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 1) (by simpa using hZ))
      hZH (hHC.trans (Subgroup.centralizer_le_normalizer _))
  have hZC : centralInvolutions T ≤ firstCoreCenter H := by
    intro z hz
    refine ⟨⟨z, hZQ hz⟩, mem_center_iff.mpr ?_, rfl⟩
    intro q
    exact Subtype.ext (hHC (pCoreIn_le 2 H q.property) z hz).symm
  have hC : Nat.card (firstCoreCenter H) = 2 := by
    let := firstCore_extraspecial r
    rw [firstCoreCenter, card_map_of_injective (H.pCoreIn 2).subtype_injective]
    exact IsExtraspecial.center_order_p 2 (H.pCoreIn 2)
  exact (eq_of_le_of_card_ge hZC (by omega)).symm

/-- The original centralizer is the centralizer of the marked first-core center.
This does not identify Mc with H. -/
theorem source_partner_centralizer (r : MarkedTriality T M Mc H) :
    Mc = centralizer (firstCoreCenter H : Set G) := by
  rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
  exact (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The source centralizer is literally C_G(z) for each nonidentity element
of the marked central involution group. -/
theorem source_partner_eq_element_centralizer (r : MarkedTriality T M Mc H)
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    Mc = centralizer ({z} : Set G) := by
  have hc : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have he := congrArg (Subgroup.map (centralInvolutions T).subtype)
    (zpowers_eq_top_of_prime_card hc
      (show (⟨z,hz⟩ : centralInvolutions T) ≠ 1 from fun h => hne (congrArg Subtype.val h)))
  have hZ : zpowers z = centralInvolutions T := by
    simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype, ← MonoidHom.range_eq_map, range_subtype] using he
  rw [source_partner_centralizer hG hempty hM hu hmany hcard e hH r,
    source_firstCore_center hG hempty hM hu hmany hcard e hH r, ← hZ,
    zpowers_eq_closure, centralizer_closure]

/-- Every ambient normalizer of the first core lies in the actual partner Mc. -/
theorem source_firstCore_normalizer_le (r : MarkedTriality T M Mc H) :
    normalizer (H.pCoreIn 2 : Set G) ≤ Mc := by
  have hc : Nat.card (firstCoreCenter H) = 2 := by
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  rw [source_partner_centralizer hG hempty hM hu hmany hcard e hH r]
  exact (normalizer_le_normalizer_characteristic_image
    (H.pCoreIn 2) (center (H.pCoreIn 2))).trans
      (Subgroup.normalizer_le_centralizer_of_card_two _ hc)

/-- The partner's two-core is contained in the first parabolic's two-core.
Equality requires the remaining local action argument of 14.2.16. -/
theorem source_partner_core_le : Mc.pCoreIn 2 ≤ H.pCoreIn 2 := by
  have huH := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).1
  have hHM : H ≤ Mc := (show Mc ∈ maximalTwoLocalOvergroups H from
    huH ▸ Set.mem_singleton Mc).2
  have hT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hs := pCoreIn_le_sylow Mc (T.subtype (hH.1.1.2.trans hHM))
    change Mc.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf Mc).map Mc.subtype at hs
    rwa [map_subgroupOf_eq_of_le (hH.1.1.2.trans hHM)] at hs
  exact (le_inf (hT.trans hH.1.1.2) le_rfl).trans (inf_pCoreIn_le_of_le 2 hHM)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
