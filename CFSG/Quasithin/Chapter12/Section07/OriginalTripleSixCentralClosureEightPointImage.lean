module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureLocalImage
import Theory.SpecificGroups.SymmetricEight.SingularDisplacement

/-!
# Original local markings in the eight-point central-closure image

Keep the actual square isometry and full H-action kernel W. Its original
J T image is S4, with the same restricted kernel, and its original Sylow
image is dihedral of order eight. Nonidentity elements in the original
U-image are fixed-point-free: their displacements lift to the elementary
original U, so the square-form displacement is singular.

Source: Aschbacher--Smith, following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.AlgebraicGroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Original local recognition inside the actual eight-point action,
including its complete kernels and a fixed-point-free original four-plane. -/
theorem original_tripleSix_central_closure_eight_point_local_image
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
    let L := J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hex : IsExtraspecial 2 W),
      letI := hex
      ∃ e : (ExtraspecialSquare.form W).IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)),
        ∃ r : H →* Equiv.Perm (Fin 8),
          r.ker = W.subgroupOf H ∧ r.ker = pCore 2 H ∧
          (∀ (g : H) (w : W),
            (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (r g)).val
              (e (Additive.ofMul (QuotientGroup.mk' (center W) w))) =
              e (Additive.ofMul (QuotientGroup.mk' (center W)
                ⟨(g:G) * (w:G) * (g:G)⁻¹,
                  (mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩))) ∧
          (∀ b ∈ (U.subgroupOf H).map r, b ≠ 1 → ∀ i : Fin 8, b i ≠ i) ∧
          ∃ hLH : L ≤ H, ∃ q : L →* Equiv.Perm (Fin 4), Function.Surjective q ∧
            q.ker = W.subgroupOf L ∧ q.ker = (r.comp (inclusion hLH)).ker ∧
            (U.subgroupOf L).map q = pCore 2 (Equiv.Perm (Fin 4)) ∧
            Nonempty (((L.subgroupOf H).map r) ≃* Equiv.Perm (Fin 4)) ∧
            Nonempty ((((T : Subgroup G).subgroupOf H).map r) ≃* DihedralGroup 4) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let L := J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  obtain ⟨hHW, hex, e, f, hfk, hfcore, _, hformula, r, hrk, hr⟩ :=
    original_tripleSix_central_closure_outer_orthogonal
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let := hex
  have hrkf : r.ker = f.ker := hrk.trans hfk.symm
  refine ⟨hHW, hex, e, r, hrk, hrkf.trans hfcore, ?_, ?_, ?_⟩
  · intro g w
    rw [hr]
    exact hformula g w
  · rintro b ⟨g, hg, rfl⟩ hne
    apply ClassicalOrthogonal.BinaryD3Comparison.fixedPointFree_of_singular_displacement _ hne
    let β : H →* MulAut W := W.normalizerMonoidHom.comp (inclusion hHW)
    have hWT : W ≤ (T : Subgroup G) :=
      (original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter).1
    have hWU : W ≤ normalizer (U : Set G) := hWT.trans (((structural K h).2.2 U D).1)
    let := D.elementary
    have hs (w : W) : (β g w * w⁻¹)^2 = 1 := by
      apply Subtype.ext
      have hm : ⁅(g:G), (w:G)⁆ ∈ U :=
        (le_normalizer_iff_commutator_le_left.mp hWU) (commutator_mem_commutator hg w.property)
      have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hm
      change ((g:G) * (w:G) * (g:G)⁻¹ * (w:G)⁻¹)^2 = 1
      simpa only [commutatorElement_def] using hh
    have hsing := ExtraspecialSquare.singular_displacement W (β g) hs
    have hequiv (v : ExtraspecialSquare.Space W) :
        (f g).val (e v) = e ((ExtraspecialSquare.isometryAction W (β g)).val v) := by
      obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (center W) v.toMul
      have hv : v = Additive.ofMul (QuotientGroup.mk' (center W) w) :=
        congrArg Additive.ofMul hw.symm
      rw [hv, ExtraspecialSquare.isometryAction_apply, quotientAut_apply_mk]
      exact hformula g w
    intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [hr]
    change (ClassicalOrthogonal.formD 3 (ZMod 2))
      ((f g).val (e u) - e u) = 0
    calc
      (ClassicalOrthogonal.formD 3 (ZMod 2))
          ((f g).val (e u) - e u) =
        (ClassicalOrthogonal.formD 3 (ZMod 2))
          (e ((ExtraspecialSquare.isometryAction W (β g)).val u) - e u) := by
            rw [hequiv]
      _ = (ClassicalOrthogonal.formD 3 (ZMod 2))
          (e.toLinearEquiv ((ExtraspecialSquare.isometryAction W (β g)).val u - u)) := by
            exact congrArg (ClassicalOrthogonal.formD 3 (ZMod 2))
              (e.toLinearEquiv.map_sub _ _).symm
      _ = ExtraspecialSquare.form W
          ((ExtraspecialSquare.isometryAction W (β g)).val u - u) := e.map_app _
      _ = 0 := hsing u
  · obtain ⟨hLH, hlocal⟩ := original_tripleSix_central_closure_local_image
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
    exact ⟨hLH, hlocal r hrk⟩

end CFSG.Quasithin.Chapter12.Section07
