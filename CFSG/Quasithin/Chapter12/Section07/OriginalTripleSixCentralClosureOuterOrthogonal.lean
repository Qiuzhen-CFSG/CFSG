module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterKernel
public import Theory.GroupTheory.ExtraspecialSquareSixPlus
import Theory.GroupTheory.PCoreKernelRange

/-!
# The literal H-image in the plus orthogonal six-space

The square form of the actual W has plus type by its original elementary
intersection of order16. Transport its conjugation action through a square
isometry. Its entire kernel is W=O2(H), and the coordinates retain every
original W vector. The same action yields an eight-point representation
with that full kernel through the checked deleted-space comparison.

Source: Aschbacher--Smith, conclusion following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.AlgebraicGroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual square-action image, with original vectors and full kernel
retained, embeds in the split orthogonal six-group and its eight-point model. -/
theorem original_tripleSix_central_closure_outer_orthogonal
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
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hex : IsExtraspecial 2 W),
      letI := hex
      ∃ e : (ExtraspecialSquare.form W).IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)),
        ∃ f : H →* Atlas.Order20160A8.O_DPlus 3 (ZMod 2),
          f.ker = W.subgroupOf H ∧ f.ker = pCore 2 H ∧ pCore 2 f.range = ⊥ ∧
          (∀ (g : H) (w : W),
            (f g).val (e (Additive.ofMul (QuotientGroup.mk' (center W) w))) =
              e (Additive.ofMul (QuotientGroup.mk' (center W)
                ⟨(g:G) * (w:G) * (g:G)⁻¹,
                  (mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩))) ∧
          ∃ r : H →* Equiv.Perm (Fin 8), r.ker = W.subgroupOf H ∧
            (∀ g : H, ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (r g) = f g) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let Z := zpowers (z:G)
  obtain ⟨hWT, hHW, hWcard, hIcard, _, hcenter, hex, _⟩ :=
    original_tripleSix_central_closure_outer_extraspecial
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let := hex
  obtain ⟨_, hcore, _, hZN, he, φ, _, hker, hk, _, _⟩ :=
    original_tripleSix_central_closure_outer_kernel
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let : (Z.subgroupOf W).Normal := hZN
  let := he
  let I := (U ⊓ W : Subgroup G).subgroupOf W
  let := D.elementary
  let : IsElementaryAbelian 2 (U ⊓ W : Subgroup G) := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.subgroupOf inf_le_right
  have hIc : Nat.card I = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ W ≤ W from inf_le_right)).toEquiv).trans hIcard
  obtain ⟨e, σ, hσker, hσformula⟩ := ExtraspecialSquare.plus_six_automorphism_action W hWcard I hIc
  let β : H →* MulAut W := W.normalizerMonoidHom.comp (inclusion hHW)
  let f := σ.comp β
  have hfker : f.ker = W.subgroupOf H := by
    rw [←hk]
    ext g
    change β g ∈ σ.ker ↔ g ∈ φ.ker
    rw [hσker, ←IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 2)]
    rw [hker g]
    constructor
    · intro hg w hw
      have hh := DFunLike.congr_fun (show quotientAut (center W) (β g) = 1 from hg)
        (QuotientGroup.mk' (center W) ⟨w, hw⟩)
      rw [quotientAut_apply_mk] at hh
      have hm : β g ⟨w, hw⟩ / ⟨w, hw⟩ ∈ center W := QuotientGroup.eq_iff_div_mem.mp hh
      have hzmem := hcenter.le (mem_map_of_mem W.subtype hm)
      have hc : ⁅(g:G), w⁆ ∈ Z := by
        change (g:G) * w * (g:G)⁻¹ / w ∈ Z at hzmem
        simpa only [div_eq_mul_inv, commutatorElement_def] using hzmem
      simpa only [commutatorElement_inv] using Z.inv_mem hc
    · intro hg
      apply MulEquiv.ext
      intro q
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (center W) q
      rw [quotientAut_apply_mk]
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hm : ⁅(g:G), (w:G)⁆ ∈ Z := by
        simpa only [commutatorElement_inv] using Z.inv_mem (hg w w.property)
      obtain ⟨y, hy, hyw⟩ := hcenter.ge hm
      have hyw' : y = β g w / w := by
        apply Subtype.ext
        change (y:G) = (g:G) * (w:G) * (g:G)⁻¹ / (w:G)
        change (y:G) = ⁅(g:G), (w:G)⁆ at hyw
        simpa only [div_eq_mul_inv, commutatorElement_def] using hyw
      exact hyw' ▸ hy
  have hWH : W ≤ H := hWT.trans le_sup_right
  have hfcore : f.ker = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [hfker, map_subgroupOf_eq_of_le hWH]
    exact hcore.symm
  refine ⟨hHW, hex, e, f, hfker, hfcore, pCore_range_eq_bot_of_ker_eq_pCore 2 f hfcore, ?_, ?_⟩
  · intro g w
    have hh := hσformula (β g) (QuotientGroup.mk' (center W) w)
    rw [quotientAut_apply_mk] at hh
    exact hh
  · let r := ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.symm.toMonoidHom.comp f
    refine ⟨r, ?_, ?_⟩
    · calc
        r.ker = f.ker := by
          ext g
          change ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.symm (f g) = 1 ↔ f g = 1
          exact ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.symm.map_eq_one_iff
        _ = W.subgroupOf H := hfker
    · intro g
      exact ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv.apply_symm_apply (f g)

end CFSG.Quasithin.Chapter12.Section07
