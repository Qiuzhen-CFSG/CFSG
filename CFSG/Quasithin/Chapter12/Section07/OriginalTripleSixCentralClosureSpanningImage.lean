module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureRegularImage

/-! The same original square marking retains the original JT-fixed point and
its spanning H-orbit. Transport uses exactly Z(W)=<z>, not an abstract module
identification. Source: Aschbacher--Smith, following12.7.20, printed p.846. -/

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
is regularly marked, and retains the original locally fixed spanning point. -/
theorem original_tripleSix_central_closure_spanning_image
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
  let Z := zpowers (z:G)
  obtain ⟨hHW, hex, e, r, hrW, hrcore, hcore, hformula, hAcard, htrans, hfree, eL,
      c, hc, hmax, j, hj⟩ := original_tripleSix_central_closure_regular_image
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let := hex
  obtain ⟨_, _, _, hZN, he, φ, hφ, _, _, _, x, hx, hpoint, hspan, hfix⟩ :=
    original_tripleSix_central_closure_outer_kernel
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  let : (Z.subgroupOf W).Normal := hZN
  let := he
  have hcenter := (original_tripleSix_central_closure_outer_extraspecial
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter).2.2.2.2.2.1
  have hzW : (z:G) ∈ W := le_conjugateSpanBy _ _ (tripleSixPoint_properties D a z hz).1
  have hZW : Z ≤ W := zpowers_le.mpr hzW
  have hZC : Z.subgroupOf W = center W := by
    apply map_injective W.subtype_injective
    rw [map_subgroupOf_eq_of_le hZW, hcenter]
  let q := QuotientGroup.quotientMulEquivOfEq hZC
  let d : Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] ExtraspecialSquare.Space W :=
    LinearEquiv.ofBijective (q.toMonoidHom.toAdditive.toZModLinearMap 2) q.bijective
  let b := d.trans e.toLinearEquiv
  have hb (w : W) : b (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
      e (Additive.ofMul (QuotientGroup.mk' (center W) w)) := rfl
  have hpoint' : ∃ w : W, (w:G) ∈ tripleSixPoint D a z ∧
      e (Additive.ofMul (QuotientGroup.mk' (center W) w)) = b x := by
    have hxV := hpoint ▸ Submodule.mem_span_singleton_self (R := ZMod 2) x
    change x.toMul ∈ ((tripleSixPoint D a z).subgroupOf W).map
      (QuotientGroup.mk' (Z.subgroupOf W)) at hxV
    obtain ⟨w, hw, hwx⟩ := hxV
    exact ⟨w, hw, (hb w).symm.trans
      (congrArg (fun v : W ⧸ Z.subgroupOf W => b (Additive.ofMul v)) hwx)⟩
  have intertwine (g : H) (v : Additive (W ⧸ Z.subgroupOf W)) :
      (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (r g)).val (b v) = b (φ g v) := by
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) v.toMul
    have hv : v = Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w) :=
      congrArg Additive.ofMul hw.symm
    rw [hv, hφ, hb, hb]
    exact hformula g w
  have hfixed : ∀ g : H, (g:G) ∈ L →
      (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (r g)).val (b x) = b x := by
    intro g hg
    exact (intertwine g x).trans (congrArg b (hfix g hg))
  have hspan' : Submodule.span (ZMod 2)
      (Set.range (fun g : r.range =>
        (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g.val).val (b x))) = ⊤ := by
    let P := Submodule.span (ZMod 2)
      (Set.range (fun g : r.range =>
        (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g.val).val (b x)))
    have hle : Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) ≤
        P.comap b.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      obtain ⟨u, hu⟩ := g.property
      have hv : (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (r u)).val (b x) ∈ P :=
        Submodule.subset_span ⟨⟨r u, u, rfl⟩, rfl⟩
      change b (g.val x) ∈ P
      rw [← hu, ← intertwine]
      exact hv
    have hP : P.comap b.toLinearMap = ⊤ := top_unique (hspan ▸ hle)
    apply top_unique
    intro v _
    have hv : b.symm v ∈ P.comap b.toLinearMap := hP ▸ Submodule.mem_top
    change b (b.symm v) ∈ P at hv
    simpa only [b.apply_symm_apply] using hv
  exact ⟨hHW, hex, e, r, hrW, hrcore, hcore, hformula, hAcard, htrans, hfree, eL,
    c, hc, hmax, j, hj, b x, fun hh => hx (b.injective (hh.trans b.map_zero.symm)),
    hpoint', hfixed, hspan'⟩

end CFSG.Quasithin.Chapter12.Section07
