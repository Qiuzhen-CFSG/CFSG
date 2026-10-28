module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterIntersection
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureCoreRecovery
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureFixedPoint

/-!
# The actual outer closure of order 128

The original intersection has order 16. Its full centralizer kernel on U
is exactly this intersection because C_G(U)=U, so the elementary eight
image gives W order 128. Quotienting by the original central point gives
the whole binary six-space, with its literal H action, complete kernel,
and the unchanged scalar point whose orbit spans the whole space.

Source: Aschbacher--Smith, conclusion following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The unchanged outer closure has order128, and its original central
quotient is the entire six-dimensional representation with full kernel. -/
theorem original_tripleSix_central_closure_outer_size
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    let Z := zpowers (z:G)
    Nat.card (U ⊓ W : Subgroup G) = 16 ∧ Nat.card W = 128 ∧
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        Nat.card (W ⧸ Z.subgroupOf W) = 64 ∧
        Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 6 ∧
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧ pCore 2 φ.range = ⊥ ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ ∧
            ∀ g : H, (g:G) ∈ J ⊔ (T : Subgroup G) → φ g x = x := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  have hI : Nat.card (U ⊓ W : Subgroup G) = 16 :=
    original_tripleSix_central_closure_outer_intersection h structural D a z hz hzT hnot houter
  have hCU : centralizer (U : Set G) = U :=
    (original_tripleSix_central_closure_core_recovery
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter).2.2.2.2.1
  have hWT : W ≤ (T : Subgroup G) :=
    (original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter).1
  have hWN : W ≤ normalizer (U : Set G) :=
    hWT.trans (((structural K h).2.2 U D).1)
  have height : Nat.card (inducedAutomizer U W) = 8 :=
    (original_tripleSix_central_closure_outer_eight h structural D a z hz hzT hnot houter).1
  have hsize : Nat.card (inducedAutomizer U W) =
      (centralizer (U : Set G)).relIndex W := by
    rw [inducedAutomizer, ←relIndex_ker, MonoidHom.ker_rangeRestrict,
      normalizerMonoidHom_ker, relIndex_subgroupOf hWN]
  have hindex : (U ⊓ W).relIndex W = 8 := by
    rw [inf_relIndex_right, ←hCU, ←hsize, height]
  have hWcard : Nat.card W = 128 := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ W) W bot_le inf_le_right
    rw [relIndex_bot_left, relIndex_bot_left, hindex, hI] at hm
    omega
  obtain ⟨hHW, hZN, hrest⟩ :=
    original_tripleSix_central_closure_fixed_point h structural D a z hz hzT hnot
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he, φ, hformula, hker, hcore, x, hx, hpoint, horbit, hfixed⟩ := hrest
  let := he
  have hp := tripleSixPoint_properties D a z hz
  have hZW : Z ≤ W := (zpowers_le.mpr hp.1).trans (le_conjugateSpanBy V1 R)
  have hZcard : Nat.card (Z.subgroupOf W) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv]
    let := D.elementary
    have ho : orderOf (z:G) = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property)
      (fun hh => hz (Subtype.ext hh))
    rw [Nat.card_zpowers, ho]
  have hquot : Nat.card (W ⧸ Z.subgroupOf W) = 64 := by
    have hh := (Z.subgroupOf W).index_mul_card
    change Nat.card (W ⧸ Z.subgroupOf W) * Nat.card (Z.subgroupOf W) = Nat.card W at hh
    rw [hWcard, hZcard] at hh
    omega
  have hdim : Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)) = 6 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (W ⧸ Z.subgroupOf W))
    rw [Nat.card_zmod] at hh
    change Nat.card (W ⧸ Z.subgroupOf W) = _ at hh
    rw [hquot] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hh.symm)
  exact ⟨hI, hWcard, hHW, hZN, he, hquot, hdim, φ, hformula, hker, hcore,
    x, hx, hpoint, horbit, hfixed⟩

end CFSG.Quasithin.Chapter12.Section07
