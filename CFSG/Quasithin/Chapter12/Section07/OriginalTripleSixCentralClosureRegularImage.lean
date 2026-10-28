module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureEightPointImage
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterImageFour
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.QuotientActionCentralizer
public import Theory.SpecificGroups.SymmetricEight.FreeFourTransitivity
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.RegularActionConjugacy
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.LocalGroups

/-!
# Transitivity and the regular original Sylow in the central-closure image

The original U-image has order four and acts freely on the eight points.
The full W kernel makes the image two-core-free, so the finite four-block
obstruction forces transitivity. The actual T-image is a Sylow of order
eight; transitivity then makes its action regular. Its regular marking
reduces the actual J T image to one of the four checked S4 overgroups.
The square isometry, original conjugation formula and entire W kernel are
retained throughout.

Source: Aschbacher--Smith, following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.AlgebraicGroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
open Theory.SpecificGroups.SymmetricEight
open Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual two-core-free H/W action is transitive, its original T-image
is regular dihedral, and the original J T local has a checked finite marking. -/
theorem original_tripleSix_central_closure_regular_image
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
          r.ker = W.subgroupOf H ∧ r.ker = pCore 2 H ∧ pCore 2 r.range = ⊥ ∧
          (∀ (g : H) (w : W),
            (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (r g)).val
              (e (Additive.ofMul (QuotientGroup.mk' (center W) w))) =
              e (Additive.ofMul (QuotientGroup.mk' (center W)
                ⟨(g:G) * (w:G) * (g:G)⁻¹,
                  (mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩))) ∧
          Nat.card ((U.subgroupOf H).map r) = 4 ∧
          MulAction.IsPretransitive r.range (Fin 8) ∧
          (∀ b ∈ ((T : Subgroup G).subgroupOf H).map r,
            b ≠ 1 → ∀ i : Fin 8, b i ≠ i) ∧
          Nonempty (((L.subgroupOf H).map r) ≃* Equiv.Perm (Fin 4)) ∧
          ∃ c : Equiv.Perm (Fin 8),
            (((T : Subgroup G).subgroupOf H).map r).map (MulAut.conj c).toMonoidHom = twoGroup ∧
            MaximalTwo (r.range.map (MulAut.conj c).toMonoidHom) ∧
            ∃ j : Fin 4,
              ((L.subgroupOf H).map r).map (MulAut.conj c).toMonoidHom = localGroup j := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let L := J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  obtain ⟨hHW, hex, e, r, hrW, hrcore, hformula, hfree, hLH,
      q, hq, hqW, hqker, hUq, ⟨eL⟩, ⟨eT⟩⟩ :=
    original_tripleSix_central_closure_eight_point_local_image
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let := hex
  have hcore : pCore 2 r.range = ⊥ := pCore_range_eq_bot_of_ker_eq_pCore 2 r hrcore
  obtain ⟨N, hN, hNW, _, hcard, _, _⟩ := original_tripleSix_central_closure_outer_image_four
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let : N.Normal := hN
  have hsame : r.ker = (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk', hNW, hrW]
  have hAcard : Nat.card ((U.subgroupOf H).map r) = 4 := by
    have he : Nat.card ((U.subgroupOf H).map r) =
        Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N)) := le_antisymm
      (card_map_le_card_map_of_ker_le _ _ _ hsame.ge)
      (card_map_le_card_map_of_ker_le _ _ _ hsame.le)
    exact he.trans hcard
  have hA2 : ∀ b ∈ (U.subgroupOf H).map r, b ^ 2 = 1 := by
    rintro b ⟨u, hu, rfl⟩
    let := D.elementary
    have hu2 : u ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (u:G) hu)
    rw [← map_pow, hu2, map_one]
  have htrans := FreeFourTransitivity.transitive r.range ((U.subgroupOf H).map r)
    (map_le_range _ _) hAcard hA2 hfree hcore
  let := htrans
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  let S : Sylow 2 H := T.subtype hTH
  let S' : Sylow 2 r.range := S.mapSurjective r.rangeRestrict_surjective
  have hSmap : (S' : Subgroup r.range).map r.range.subtype =
      ((T : Subgroup G).subgroupOf H).map r := by
    change (((T : Subgroup G).subgroupOf H).map r.rangeRestrict).map r.range.subtype = _
    rw [map_map]
    rfl
  have hSc : Nat.card S' = 8 := by
    rw [← card_map_of_injective (f := r.range.subtype) r.range.subtype_injective, hSmap,
      Nat.card_congr eT.toEquiv]
    simp [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hTfree : ∀ b ∈ ((T : Subgroup G).subgroupOf H).map r,
      b ≠ 1 → ∀ i : Fin 8, b i ≠ i := by
    rintro b ⟨u, hu, rfl⟩ hb i
    exact FreeFourTransitivity.sylow_free r.range S' hSc (r.rangeRestrict u)
      ⟨u, hu, rfl⟩ (fun he => hb (congrArg Subtype.val he)) i
  let Q := ((T : Subgroup G).subgroupOf H).map r
  let d : DihedralGroup 4 →* Equiv.Perm (Fin 8) := Q.subtype.comp eT.symm.toMonoidHom
  have hdi : Function.Injective d := Q.subtype_injective.comp eT.symm.injective
  have hdr : d.range = Q := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eT.symm.surjective, ← MonoidHom.range_eq_map,
      Q.range_subtype]
  have hdf : ∀ x : DihedralGroup 4, x ≠ 1 → ∀ i, d x i ≠ i := by
    intro x hx i
    exact hTfree (d x) (eT.symm x).property
      (fun he => hx (hdi (he.trans d.map_one.symm))) i
  obtain ⟨c, hc⟩ := regular_dihedral_conjugacy d hdi hdf
  rw [hdr] at hc
  let f := (MulAut.conj c).toMonoidHom.comp r
  have hfr : f.range = r.range.map (MulAut.conj c).toMonoidHom := MonoidHom.range_comp _ _
  let S'' : Sylow 2 f.range := S.mapSurjective f.rangeRestrict_surjective
  have hS'' : (S'' : Subgroup f.range).map f.range.subtype = twoGroup := by
    change (((T : Subgroup G).subgroupOf H).map f.rangeRestrict).map f.range.subtype = _
    rw [map_map]
    change ((T : Subgroup G).subgroupOf H).map f = _
    rw [show f = (MulAut.conj c).toMonoidHom.comp r from rfl, ← map_map]
    exact hc
  have hmax : MaximalTwo (r.range.map (MulAut.conj c).toMonoidHom) :=
    hfr ▸ maximalTwo_of_sylow f.range S'' hS''
  let A := ((L.subgroupOf H).map r).map (MulAut.conj c).toMonoidHom
  have hTX : twoGroup ≤ A := by
    rw [← hc]
    apply map_mono
    apply map_mono
    exact subgroupOf_mono H (show (T : Subgroup G) ≤ L from le_sup_right)
  let ea : A ≃* Equiv.Perm (Fin 4) :=
    (((L.subgroupOf H).map r).equivMapOfInjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective).symm.trans eL
  have hAX : A ≤ r.range.map (MulAut.conj c).toMonoidHom := map_mono (map_le_range _ _)
  obtain ⟨j, hj⟩ := symmetricFour_classification hmax A hAX hTX ea
  exact ⟨hHW, hex, e, r, hrW, hrcore, hcore, hformula, hAcard, htrans,
    hTfree, ⟨eL⟩, c, hc, hmax, j, hj⟩

end CFSG.Quasithin.Chapter12.Section07
