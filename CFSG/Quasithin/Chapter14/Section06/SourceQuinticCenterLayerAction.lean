module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSNaturalCenter
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The faithful original quintic center-layer action

The full H-action on UH/ZT cannot have two-group image: its two-residual
would preserve the original four-plane, as does the original Sylow, forcing
H into the original plane normalizer M.  The actual quotient order ten or
twenty then identifies the entire action kernel with O2(H).  This covers
Sz(2) directly and uses neither positive Suzuki parameter nor span fullness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem small_odd_image_injective
    {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hc : Nat.card A ∣ 20) (hcore : pCore 2 A = ⊥)
    (himage : ¬ IsPGroup 2 f.range) : Function.Injective f := by
  have hmul : Nat.card f.ker * Nat.card f.range ∣ 20 := by
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    simpa only [←index_eq_card,f.ker.card_mul_index] using hc
  have h5 : ¬ 5 ∣ Nat.card f.ker := by
    intro hd
    have hh : 5 * Nat.card f.range ∣ 5 * 4 :=
      (Nat.mul_dvd_mul hd (dvd_refl _)).trans hmul
    have hr := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 5) hh
    exact himage (IsPGroup.of_card_dvd_pow (n := 2) hr)
  have hp : IsPGroup 2 f.ker := IsPGroup.of_card_dvd_pow (n := 2)
    (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm.dvd_of_dvd_mul_right
      (f.ker.card_subgroup_dvd_card.trans hc))
  exact f.ker_eq_bot_iff.mp (bot_unique
    ((le_sSup ⟨inferInstance,hp⟩ : f.ker ≤ pCore 2 A).trans hcore.le))

/-- The original quotient-center action has the full two-core kernel and
non-two-group image, including in the actual Sz(2) branch. -/
theorem source_quintic_faithful_center_layer_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let UH := conjugateSpanBy (localModule T M) H
    let ZT := centralInvolutions T
    ∃ hN : (ZT.subgroupOf UH).Normal,
      letI := hN
      ∃ α : H →* MulAut (UH ⧸ ZT.subgroupOf UH),
        α.ker = pCore 2 H ∧ ¬ IsPGroup 2 α.range ∧
          ∀ h : H, ∀ u : UH,
            α h (QuotientGroup.mk' (ZT.subgroupOf UH) u) =
              QuotientGroup.mk' (ZT.subgroupOf UH)
                ⟨(h : G) * (u : G) * (h : G)⁻¹,
                  (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy
                    (localModule T M) H h.property) u).mp u.property⟩ := by
  classical
  let V := localModule T M
  let U := conjugateSpanBy V H
  let Z := centralInvolutions T
  let := (Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let hN : (Z.subgroupOf U).Normal := normal_of_isMulCommutative _
  let := hN
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)).2.2.2.2.2.2
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action H U Z hHU
    (hHZ.trans (Subgroup.centralizer_le_normalizer _)) hN
  have hcomm : ⁅U,H.pCoreIn 2⁆ ≤ Z :=
    (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2.le
  have hkill : pCore 2 H ≤ α.ker := by
    have hh := quotient_conjugation_action_kills_commutator_layer H U Z (H.pCoreIn 2)
      hN hHU hcomm α hα
    exact (show pCore 2 H = (H.pCoreIn 2).subgroupOf H from
      (comap_map_eq_self_of_injective H.subtype_injective _).symm) ▸ hh
  have hnot : ¬ IsPGroup 2 α.range := by
    intro hp
    have hr := pResidual_le_ker_of_isPGroup 2 α.rangeRestrict hp
    have hres : pResidual 2 H ≤ α.ker := by
      intro r hr'
      exact congrArg Subtype.val (show α.rangeRestrict r = 1 from hr hr')
    let R := (pResidual 2 H).map H.subtype
    have hRN : R ≤ normalizer (V : Set G) := by
      apply le_normalizer_iff.mpr
      intro r hr' v hv
      obtain ⟨r,hr',rfl⟩ := hr'
      let vU : U := ⟨v,le_conjugateSpanBy V H hv⟩
      have ha := hα r vU
      rw [show α r = 1 from hres hr'] at ha
      let wU : U := ⟨(r : G)*v*(r : G)⁻¹,(mem_normalizer_iff.mp (hHU r.property) v).mp vU.property⟩
      have he : (QuotientGroup.mk wU : U ⧸ Z.subgroupOf U) = QuotientGroup.mk vU := ha.symm
      have hz : (r : G)*v*(r : G)⁻¹/v ∈ Z :=
        (show wU/vU ∈ Z.subgroupOf U from QuotientGroup.eq_iff_div_mem.mp he)
      have hh := V.mul_mem ((show Z ≤ V from le_conjugateSpanBy _ _) hz) hv
      change (r : G)*v*(r : G)⁻¹ ∈ V
      simpa only [div_mul_cancel] using hh
    have hRM : R ≤ M := by
      rw [InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
      exact hRN
    have hgen : R ⊔ (T : Subgroup G) = H := by
      have hh := congrArg (Subgroup.map H.subtype)
        (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
      rw [Subgroup.map_sup] at hh
      change R ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype =
        (⊤ : Subgroup H).map H.subtype at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.2,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hH.1.2 (hgen.ge.trans (sup_le hRM hM.1.2))
  let q := QuotientGroup.mk' (pCore 2 H)
  let β := QuotientGroup.lift (pCore 2 H) α hkill
  have hβrange : β.range = α.range := by
    ext b
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
      exact ⟨r,hx⟩
    · rintro ⟨r,hr⟩
      exact ⟨q r,hr⟩
  have hc : Nat.card (H ⧸ pCore 2 H) ∣ 20 := by
    rcases Section02.SolvableAmalgam.source_index_five_models
      hG T hempty hM hu hmany hcard e H hH.1 hi with hd | hs
    · obtain ⟨eD⟩ := hd
      rw [(Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card]
      decide
    · obtain ⟨eS⟩ := hs
      rw [(Nat.card_congr eS.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card]
  have hβ := small_odd_image_injective β hc (pCore_quotient_pCore_eq_bot 2)
    (hβrange.symm ▸ hnot)
  have hker : α.ker = pCore 2 H := by
    ext r
    change β (q r) = 1 ↔ r ∈ pCore 2 H
    rw [←map_one β,hβ.eq_iff]
    exact QuotientGroup.eq_one_iff r
  exact ⟨hN,α,hker,hnot,hα⟩

end CFSG.Quasithin.Chapter14.Section06
