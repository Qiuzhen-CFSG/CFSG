module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureSpanningImage
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.CoreFreeLocalImage

/-! Full recognition of the actual H/W image, preserving the original square
marking, all of its kernel, the original JT local and its spanning fixed point.
The finite sieve constructs the second local; it is not a premise.
Source: Aschbacher--Smith, following12.7.20, printed p.846. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.AlgebraicGroup
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
open Theory.SpecificGroups.SymmetricEight
open Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual two-core-free H/W action is transitive, its original T-image
is PSL3(2) in its checked native marking, retaining the locally fixed spanning point. -/
theorem original_tripleSix_central_closure_classified_image
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
              ((L.subgroupOf H).map r).map (MulAut.conj c).toMonoidHom = localGroup j ∧
              Nonempty (r.range ≃* PSL(3, ZMod 2)) ∧
              Nonempty ((H ⧸ r.ker) ≃* PSL(3, ZMod 2)) ∧
              (∃ p : Equiv.Perm (Fin 8),
                r.range.map (MulAut.conj p).toMonoidHom = modelGroup) ∧
              ∃ x : ClassicalOrthogonal.VectorD 3 (ZMod 2), x ≠ 0 ∧
                (∃ w : W, (w:G) ∈ tripleSixPoint D a z ∧
                  e (Additive.ofMul (QuotientGroup.mk' (center W) w)) = x) ∧
                (∀ g : H, (g:G) ∈ L →
                  (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (r g)).val x = x) ∧
                Submodule.span (ZMod 2) (Set.range (fun g : r.range =>
                  (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g.val).val x)) = ⊤ := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let L := J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  obtain ⟨hHW, hex, e, r, hrW, hrcore, hcore, hformula, hAcard, htrans, hfree, ⟨eL⟩,
      c, hc, hmax, j, hj, x, hx, hpoint, hfix, hspan⟩ := original_tripleSix_central_closure_spanning_image
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let := hex
  let f := MulAut.conj c
  let X := r.range.map f.toMonoidHom
  let A := ((L.subgroupOf H).map r).map f.toMonoidHom
  have hAX : A ≤ X := map_mono (map_le_range _ _)
  have hTA : twoGroup ≤ A := by
    rw [← hc]
    exact map_mono (map_mono (subgroupOf_mono H (show (T : Subgroup G) ≤ L from le_sup_right)))
  let eA : A ≃* Equiv.Perm (Fin 4) :=
    (((L.subgroupOf H).map r).equivMapOfInjective f.toMonoidHom f.injective).symm.trans eL
  have hcoreX : pCore 2 X = ⊥ := by
    rw [← pCore_map_iso 2 (r.range.equivMapOfInjective f.toMonoidHom f.injective), hcore,
      Subgroup.map_bot]
  obtain ⟨⟨eX⟩, ⟨p, hp⟩, _⟩ := core_free_local_image hmax hcoreX A hAX hTA eA
  have hclass : Nonempty (r.range ≃* PSL(3, ZMod 2)) :=
    ⟨(r.range.equivMapOfInjective f.toMonoidHom f.injective).trans eX⟩
  have hquotient : Nonempty ((H ⧸ r.ker) ≃* PSL(3, ZMod 2)) := by
    obtain ⟨er⟩ := hclass
    exact ⟨(QuotientGroup.quotientKerEquivRange r).trans er⟩
  have hconj : ∃ p : Equiv.Perm (Fin 8),
      r.range.map (MulAut.conj p).toMonoidHom = modelGroup := by
    refine ⟨p * c, ?_⟩
    have hcomp : (MulAut.conj (p * c)).toMonoidHom =
        (MulAut.conj p).toMonoidHom.comp f.toMonoidHom := by
      ext g
      simp [f, MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← map_map]
    exact hp
  exact ⟨hHW, hex, e, r, hrW, hrcore, hcore, hformula, hAcard, htrans, hfree, ⟨eL⟩,
    c, hc, hmax, j, hj, hclass, hquotient, hconj, x, hx, hpoint, hfix, hspan⟩

end CFSG.Quasithin.Chapter12.Section07
