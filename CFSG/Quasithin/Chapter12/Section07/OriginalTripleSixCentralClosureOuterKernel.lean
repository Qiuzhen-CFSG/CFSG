module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterExtraspecial
import Theory.GroupTheory.CentricRadicalCoreComparison
import Theory.GroupTheory.SelfCentralizingCore
import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
import Theory.GroupTheory.PCoreActionSplitting

/-!
# The complete original H-action kernel is W

Characteristic two kills the odd core of the actual H. The proved Sylow
centricity then bounds its centralizer of W by W. An automorphism trivial
on the actual central quotient is inner, so the retained conjugation
representation has full kernel W. Its reduced image identifies O2(H)=W.
The original point and its spanning orbit are retained in that same action.

Source: Aschbacher--Smith, conclusion following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal original central quotient action has complete kernel W,
which is also the whole two-core of H. -/
theorem original_tripleSix_central_closure_outer_kernel
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
    H ⊓ centralizer (W : Set G) = Z ∧ H.pCoreIn 2 = W ∧
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧
          φ.ker = W.subgroupOf H ∧ pCore 2 φ.range = ⊥ ∧
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
  obtain ⟨hWT, hHW, _, _, hTC, hcenter, hex, _⟩ :=
    original_tripleSix_central_closure_outer_extraspecial
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let := hex
  have hWH : W ≤ H := hWT.trans le_sup_right
  have hp := tripleSixPoint_properties D a z hz
  have hzW : (z:G) ∈ W := le_conjugateSpanBy V1 R hp.1
  have hZW : Z ≤ W := zpowers_le.mpr hzW
  let P := W.subgroupOf H
  let : P.Normal := normal_subgroupOf_of_le_normalizer hHW
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hHchar : H ∈ Chapter1.He G := by
    apply Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
    refine ⟨?_, (show (T : Subgroup G) ≤ H from le_sup_right)⟩
    intro hb
    have hh : (z:G) ∈ H.pCoreIn 2 := hc.2.2.1 hzW
    rw [show H.pCoreIn 2 = ⊥ from hb] at hh
    exact hz (Subtype.ext hh)
  have hodd : pPrimeCore 2 H = ⊥ :=
    pPrimeCore_eq_bot_of_centralizer_pCore_le 2 (Chapter1.mem_He_iff.mp hHchar)
  have hcent : ((T.subtype (show (T : Subgroup G) ≤ H from le_sup_right) : Sylow 2 H) :
      Subgroup H) ⊓ centralizer (P : Set H) ≤ P := by
    intro x hx
    apply hZW
    apply hTC.le
    refine ⟨hx.1, ?_⟩
    intro w hw
    exact congrArg Subtype.val (hx.2 ⟨w, hWH hw⟩ hw)
  have hCH : centralizer (P : Set H) ≤ P := by
    simpa only [hodd, bot_sup_eq] using AlperinGoldschmidt.normal_p_centralizer_le
      (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)) P hcent
  have hCG : H ⊓ centralizer (W : Set G) = Z := by
    apply le_antisymm
    · intro x hx
      have hxW : x ∈ W := hCH (show (⟨x, hx.1⟩ : H) ∈ centralizer (P : Set H) from
        fun w hw => Subtype.ext (hx.2 w hw))
      apply hcenter.le
      exact ⟨⟨x, hxW⟩, mem_center_iff.mpr (fun w => Subtype.ext (hx.2 w w.property)), rfl⟩
    · intro x hx
      exact ⟨hWH (hZW hx), (hTC.ge hx).2⟩
  obtain ⟨hHW', hZN, he, φ, hformula, hker, hcore, x, hx, hpoint, horbit, hfixed⟩ :=
    original_tripleSix_central_closure_fixed_point h structural D a z hz hzT hnot
  let : (Z.subgroupOf W).Normal := hZN
  let := he
  let β : H →* MulAut W := W.normalizerMonoidHom.comp (inclusion hHW')
  have hk : φ.ker = P := by
    apply le_antisymm
    · intro g hg
      have hdis (w : W) : β g w * w⁻¹ ∈ center W := by
        have hh : ⁅(g:G), (w:G)⁆ ∈ Z := by
          simpa only [commutatorElement_inv] using Z.inv_mem ((hker g).mp hg w w.property)
        have hh' : ((β g w * w⁻¹ : W) : G) ∈ (center W).map W.subtype := hcenter.symm ▸ hh
        obtain ⟨y, hy, heq⟩ := hh'
        exact (Subtype.ext heq : y = β g w * w⁻¹) ▸ hy
      obtain ⟨r, hr⟩ := IsExtraspecial.exists_conj_of_central_displacement (p := 2) (β g) hdis
      have hcentral : (r:G)⁻¹ * (g:G) ∈ centralizer (W : Set G) := by
        intro w hw
        have heq := congrArg (fun f : MulAut W => (f ⟨w, hw⟩ : G)) hr
        change (r:G) * w * (r:G)⁻¹ = (g:G) * w * (g:G)⁻¹ at heq
        calc
          w * ((r:G)⁻¹ * (g:G)) = (r:G)⁻¹ * ((r:G) * w * (r:G)⁻¹) * (g:G) := by group
          _ = (r:G)⁻¹ * ((g:G) * w * (g:G)⁻¹) * (g:G) := by rw [heq]
          _ = ((r:G)⁻¹ * (g:G)) * w := by group
      have hh := hZW (hCG.le ⟨H.mul_mem (H.inv_mem (hWH r.property)) g.property, hcentral⟩)
      change (g:G) ∈ W
      simpa only [mul_inv_cancel_left] using W.mul_mem r.property hh
    · intro g hg
      apply (hker g).mpr
      intro w hw
      exact hc.2.2.2.2.1 (commutator_mem_commutator hw (hc.2.2.1 hg))
  have hkcore : φ.ker = pCore 2 H := φ.ker_eq_pCore_of_range_core_eq_bot 2
    (by
      rw [hk]
      exact (T.isPGroup'.to_le hWT).of_injective
        (subgroupOfEquivOfLe hWH).toMonoidHom (subgroupOfEquivOfLe hWH).injective) hcore
  have hHcore : H.pCoreIn 2 = W := by
    rw [pCoreIn, ←hkcore, hk, map_subgroupOf_eq_of_le hWH]
  exact ⟨hCG, hHcore, hHW', hZN, he, φ, hformula, hker, hk, hcore,
    x, hx, hpoint, horbit, hfixed⟩

end CFSG.Quasithin.Chapter12.Section07
