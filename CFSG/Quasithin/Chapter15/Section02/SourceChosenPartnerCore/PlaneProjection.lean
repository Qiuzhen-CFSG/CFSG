module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.FittingReduction
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ModelParabolics
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The plane in the partner core and its marked section image

The plane has order four and contains the nontrivial central seed Z. Its
H-action on the quotient by Z is trivial, since that quotient has order
at most two. In particular it centralizes Qc/Z. The characteristic-two
centralizer bound puts the entire plane in Qc, before any noncore rank
saturation or weak-closure argument.

Whenever a literal binary section retains a nonzero image of the plane,
its coordinates give a nonzero vector fixed by the actual H-image and by
the plane centralizer. These are exactly the two marking premises of the
model-parabolic contradiction. The section and its surviving plane image
remain explicit here; their construction belongs to qt-e-152-critical-pair.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136), and A.1.8 for the central-quotient bound.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- H fixes the actual plane quotient by the central seed. -/
theorem source_chosen_plane_commutator_le_seed
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) : ⁅ZS,H⁆ ≤ centralInvolutions T := by
  have hz : 2 ≤ Nat.card (centralInvolutions T) := by
    have hh := (one_lt_card_iff_ne_bot (H := centralInvolutions T)).mpr
      (Section03.InitialSource.centralInvolutions_ne_bot_of_maximal_local T h.maximal.1)
    omega
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup G) (centralInvolutions T) ZS bot_le hZ
  rw [relIndex_bot_left,relIndex_bot_left,hg.plane_card] at hprod
  have hpos : 0 < (centralInvolutions T).relIndex ZS :=
    Nat.pos_of_ne_zero ((centralInvolutions T).subgroupOf ZS).index_ne_zero_of_finite
  have hi : (centralInvolutions T).relIndex ZS ≤ 2 := by nlinarith
  by_cases he : (centralInvolutions T).relIndex ZS = 1
  · exact (le_normalizer_iff_commutator_le_left.mp hg.normalized).trans
      (relIndex_eq_one.mp he)
  · exact commutator_le_of_normalized_index_two ZS (centralInvolutions T) H hZ
      (by omega) hg.normalized
      (hg.in_partner.trans (hMc.le.trans (Subgroup.centralizer_le_normalizer _)))

/-- The entire distinguished plane lies in the actual partner two-core. -/
theorem source_chosen_plane_le_partner_core
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) : ZS ≤ twoCoreIn Mc := by
  have hZH : ZS ≤ H := hg.plane_le.trans
    ((h.prepared.inside_core H hg.outside).trans (twoCore_le H))
  have hTMc : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hQT : twoCoreIn Mc ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc,pCoreIn,twoCoreIn] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hc : ⁅ZS,twoCoreIn Mc⁆ ≤ centralInvolutions T :=
    (commutator_mono le_rfl (hQT.trans hg.outside.1.1.2)).trans
      (source_chosen_plane_commutator_le_seed h hg hMc hZ)
  let Z := (centralInvolutions T).subgroupOf Mc
  let : Z.Normal := source_chosen_seed_normal h hMc
  let q := QuotientGroup.mk' Z
  have hic : ⁅ZS.subgroupOf Mc,pCore 2 Mc⁆ ≤ Z := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_subgroupOf_eq_of_le (hZH.trans hg.in_partner)]
    exact hc
  have hmap : ⁅(ZS.subgroupOf Mc).map q,(pCore 2 Mc).map q⁆ = ⊥ := by
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hic
  have hcentral := (map_le_iff_le_comap.mp
    (commutator_eq_bot_iff_le_centralizer.mp hmap))
  have hm := map_mono (f := Mc.subtype) hcentral
  rw [map_subgroupOf_eq_of_le (hZH.trans hg.in_partner)] at hm
  exact hm.trans (source_chosen_core_quotient_centralizer h hg hMc)

/-- A surviving image of the actual plane supplies both required fixedness
conditions on the very same quotient representation. -/
theorem source_chosen_partner_plane_projection
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (d : BinaryConjugationSection L U B (ρ.comp (QuotientGroup.mk' (pCore 2 L))))
    (hU : ZS ≤ U) (hB : centralInvolutions T ≤ B) (hm : ¬ ZS ≤ B) :
    let q := QuotientGroup.mk' (pCore 2 L)
    let X := (H.subgroupOf L).map q
    ∃ w : W, w ≠ 0 ∧
      (∀ g : L, (g : G) ∈ centralizer (ZS : Set G) → ρ (q g) w = w) ∧
      (∀ g ∈ X, ρ g w = w) := by
  obtain ⟨z,hz,hzB⟩ := Set.not_subset.mp hm
  let u : U := ⟨z,hU hz⟩
  let w := (d.coordinates u).toAdd
  have hw : w ≠ 0 := by
    intro he
    exact hzB ((d.coordinates_eq_one_iff u).mp he)
  have hwP : w ∈ d.imageSpace ZS := (d.mem_imageSpace_iff ZS w).mpr ⟨u,hz,rfl⟩
  refine ⟨w,hw,?_,?_⟩
  · intro g hg
    have hc : ⁅centralizer (ZS : Set G),ZS⁆ ≤ B := by
      rw [commutator_eq_bot_iff_le_centralizer.mpr le_rfl]
      exact bot_le
    exact d.fixed_on_imageSpace_of_commutator_le (centralizer (ZS : Set G)) ZS hc g hg w hwP
  · rintro g ⟨a,ha,rfl⟩
    have hc : ⁅H,ZS⁆ ≤ B := by
      rw [commutator_comm]
      exact (source_chosen_plane_commutator_le_seed h hg hMc hZ).trans hB
    exact d.fixed_on_imageSpace_of_commutator_le H ZS hc a ha w hwP

/-- The literal section coordinates discharge all vector-marking premises of
the model-parabolic consumer. Chief recognition and survival are still needed. -/
theorem source_chosen_false_of_partner_model_section
    {T : Sylow 2 G} {M Mc V H ZS U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      BinaryConjugationSection L U B (ρ.comp q) →
      ZS ≤ U → centralInvolutions T ≤ B → ¬ ZS ≤ B →
      Representation.SmallDisplacementParabolics.ActionModel ρ → False := by
  dsimp only
  intro ρ d hU hB hm hmodel
  obtain ⟨w,hw,hfix,hXfix⟩ := source_chosen_partner_plane_projection h hg hMc hZ
    ρ d hU hB hm
  exact source_chosen_false_of_partner_actionModel h hg hMc hplane ρ w hw hmodel hfix hXfix

end CFSG.Quasithin.Chapter15.Section02
