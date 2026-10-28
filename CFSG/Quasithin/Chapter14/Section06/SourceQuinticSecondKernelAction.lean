module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticMiddleCoreProduct
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSElementaryQuotient
public import Theory.GroupTheory.Commutator.NormalPrimeQuotient
public import Theory.Representation.BinaryPrimeDegree
import all CFSG.Quasithin.Chapter14.Section06.SourceQuinticCenterLayerAction

/-!
# The faithful original full second-kernel quotient action

Conjugation acts on the actual full core modulo the full radius-two kernel.
The proved span fullness and reciprocal commutator prevent a two-group
image.  The original quotient of order ten or twenty then gives the full
action kernel.  Its prime-five binary degree forces at least sixteen
elements in this literal quotient, including the Sz(2) boundary.

The internal import reuses the frozen small-quotient injectivity calculation;
the quotient, action, full kernel, and conjugation formula here are actual
original-source constructions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The original full second-kernel quotient carries its faithful local
quotient action and has order at least sixteen, in both small quintic cases. -/
theorem source_quintic_faithful_second_kernel_action
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
    let QH := H.pCoreIn 2
    let C := H ⊓ centralizer (UH : Set G)
    C ≤ QH ∧ ∃ hN : (C.subgroupOf QH).Normal,
      letI := hN
      IsElementaryAbelian 2 (QH ⧸ C.subgroupOf QH) ∧
      ∃ α : H →* MulAut (QH ⧸ C.subgroupOf QH),
        α.ker = pCore 2 H ∧ ¬ IsPGroup 2 α.range ∧
          16 ≤ Nat.card (QH ⧸ C.subgroupOf QH) ∧
          ∀ h : H, ∀ q : QH,
            α h (QuotientGroup.mk' (C.subgroupOf QH) q) =
              QuotientGroup.mk' (C.subgroupOf QH)
                ⟨(h : G) * (q : G) * (h : G)⁻¹,
                  (mem_normalizer_iff.mp ((H.le_normalizer.trans
                    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) h.property) q).mp q.property⟩ := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let Z := centralInvolutions T
  obtain ⟨hCQ,hN,hE,_⟩ := source_quintic_full_kernel_elementary_quotient
    hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  let := hE
  let W := Q ⧸ C.subgroupOf Q
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer (hHU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action H Q C hHQ hHC hN
  have hQQ : ⁅Q,Q⁆ ≤ C := by
    have hh : _root_.commutator Q ≤ C.subgroupOf Q :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := C.subgroupOf Q)).mp inferInstance
    have hm := map_mono (f := Q.subtype) hh
    rw [map_subtype_commutator,subgroupOf_map_subtype] at hm
    exact hm.trans inf_le_left
  have hkill : pCore 2 H ≤ α.ker := by
    have hh := quotient_conjugation_action_kills_commutator_layer H Q C Q hN hHQ hQQ α hα
    exact (show pCore 2 H = Q.subgroupOf H from
      (comap_map_eq_self_of_injective H.subtype_injective _).symm) ▸ hh
  have hfull : U = ⁅U,H⁆ := by
    obtain ⟨g,hg,hDQ,hne,hVI,hTI,hprod,hcomm,hfull⟩ :=
      source_quintic_middle_core_product hG T hempty hM hu hmany hcard e H hH hi
    exact hfull
  have hUQ : U ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hcomm : ⁅U,Q⁆ = Z :=
    (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2
  have hZH : Z ≤ centralizer (H : Set G) := le_centralizer_iff.mp
    (Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)).2.2.2.2.2.2
  have hmove : ⁅U,Q⁆ ≠ ⊥ := by
    rw [hcomm]
    intro he
    have hh := plane_centralInvolutions_card T M hM.1.2 hcard e
    change Nat.card Z = 2 at hh
    rw [he,card_bot] at hh
    omega
  have hkerC : ⁅Q,α.ker.map H.subtype⁆ ≤ centralizer (U : Set G) := by
    rw [commutator_comm]
    apply le_trans ?_ (show C ≤ centralizer (U : Set G) from inf_le_right)
    apply commutator_le.mpr
    rintro a ⟨a₀,ha,rfl⟩ q hq
    let x : Q := ⟨q,hq⟩
    let y : Q := ⟨(a₀ : G)*q*(a₀ : G)⁻¹,(mem_normalizer_iff.mp (hHQ a₀.property) q).mp hq⟩
    have he : (QuotientGroup.mk y : W) = QuotientGroup.mk x := by
      have hh := hα a₀ x
      rw [show α a₀ = 1 from ha] at hh
      exact hh.symm
    have hh := QuotientGroup.eq_iff_div_mem.mp he
    change (a₀ : G)*q*(a₀ : G)⁻¹/q ∈ C at hh
    simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using hh
  have hnot : ¬ IsPGroup 2 α.range := by
    intro hp
    have hn := not_isPGroup_quotient_of_reciprocal_centralizer H U Q Z
      (hUQ.trans (pCoreIn_le 2 H)) hHU
      ((isPGroup_pCoreIn 2 H).to_le hUQ) hfull.symm hcomm.le hZH hmove α.ker hkerC
    exact hn (hp.of_equiv (QuotientGroup.quotientKerEquivRange α).symm)
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
  have hm := Section02.SolvableAmalgam.source_index_five_models
    hG T hempty hM hu hmany hcard e H hH.1 hi
  have hc : Nat.card (H ⧸ pCore 2 H) ∣ 20 ∧ 5 ∣ Nat.card (H ⧸ pCore 2 H) := by
    rcases hm with hd | hs
    · rw [(Nat.card_congr hd.some.toEquiv).trans DihedralGroup.nat_card]; decide
    · rw [(Nat.card_congr hs.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card]
      decide
  have hβ := small_odd_image_injective β hc.1 (pCore_quotient_pCore_eq_bot 2)
    (hβrange.symm ▸ hnot)
  have hker : α.ker = pCore 2 H := by
    ext r
    change β (q r) = 1 ↔ r ∈ pCore 2 H
    rw [←map_one β,hβ.eq_iff]
    exact QuotientGroup.eq_one_iff r
  let : MulDistribMulAction (H ⧸ pCore 2 H) W := MulDistribMulAction.compHom _ β
  let ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive W) :=
    Representation.ofElementaryAbelianAction
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply hβ
    ext w
    exact congrArg Additive.toMul (DFunLike.congr_fun hab (Additive.ofMul w))
  have hd : 4 ≤ Module.finrank (ZMod 2) (Additive W) := by
    have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
      (by decide : Nat.Prime 5) (by decide : 5 ≠ 2) hc.2
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five] using hh
  have hW : 16 ≤ Nat.card W := by
    change 2^4 ≤ Nat.card (Additive W)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hd
  exact ⟨hCQ,hN,hE,α,hker,hnot,hW,hα⟩

end CFSG.Quasithin.Chapter14.Section06
