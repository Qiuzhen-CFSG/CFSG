module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeCubicLifts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialChiefSylow
/-!
# Original cubic lifts from the remaining order-four chief interval

The kernel of the binary chief action meets the extraspecial star residual
in order nine. Its stable Frattini line supplies two Sylow-normalized cubic
generators. Taking two-residuals of their literal preimages produces two
subgroups of the original H generating O²(H), with exact intrinsic two-cores
as kernels of the restricted star maps.

Since H = O²(H)T escapes N_G(L) while T lies there, at least one of these
lifts escapes N_G(L). The ambient subgroup is two-perfect, is T-invariant,
and normalizes L₁ by the already proved relative point normality. Its
quotient by its own two-core has order three, and its star image is a
noncentral cubic. The final theorem constructs the action on the literal
chief interval; no module or point-normality callback is assumed.

This supplies the original cubic subgroups needed in the reducible Sylow
step of Aschbacher–Smith 14.7.9 and 14.7.15(2), printed pp.1045–1047,
as it arises in the remaining order-four case of 14.7.20(2), p.1049.
The S₃ quotient of YT and the geometric containment argument of 14.5.3(2)
remain to be proved. Consequently these lifts do not yet exclude the
order-four interval or prove the residual classification through 14.7.52.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The order-four chief action supplies cubic generators in the original H. -/
theorem extraspecial_two_chief_cubic_lifts
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 2) :
    ∃ A B : Subgroup F.H, A ⊔ B = pResidual 2 F.H ∧
      (IsPPerfect 2 A ∧ (T : Subgroup G).subgroupOf F.H ≤ normalizer (A : Set F.H) ∧
        Nat.card (A.map (starMap F)) = 3 ∧
        A.map (starMap F) ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
        ((starMap F).comp A.subtype).ker = pCore 2 A ∧ Nat.card (A ⧸ pCore 2 A) = 3) ∧
      (IsPPerfect 2 B ∧ (T : Subgroup G).subgroupOf F.H ≤ normalizer (B : Set F.H) ∧
        Nat.card (B.map (starMap F)) = 3 ∧
        B.map (starMap F) ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
        ((starMap F).comp B.subtype).ker = pCore 2 B ∧ Nat.card (B ⧸ pCore 2 B) = 3) := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨σ,hσ,hZ,hmP,_,_,_⟩ := extraspecial_point_central_chief_degree
    h hab structural previous hex hcard hexp hB hUN s hp hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hN : Nat.card (σ.ker.subgroupOf P) = 9 := by
    rcases extraspecial_center_kernel_residual_card σ P hP rfl hZ hmP (Or.inl hd) with h2 | h4
    · exact h2.2.2
    · omega
  have hk : IsPGroup 2 (starMap F).ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 F.H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact IsExtraspecial.exists_cubic_lifts_of_normal_nine (starMap F)
    (QuotientGroup.mk'_surjective _) hk hP heP σ.ker hN
    (fun z hz => hZ (mem_map_of_mem P.subtype hz))
    ((T : Subgroup G).subgroupOf F.H) T.isPGroup'.comap_subtype

/-- At least one cubic lift escapes the original normalizer of L, while
normalizing the point residual and retaining the literal star-map kernel. -/
theorem extraspecial_two_chief_escaping_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hp : ⁅B,F.Li L 1⁆ ≤ N) (hm : ¬ ⁅B,K F⁆ ≤ N)
    (hd : Module.finrank (ZMod 2) W = 2) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 := by
  obtain ⟨A,B,hAB,hA,hB⟩ := extraspecial_two_chief_cubic_lifts
    h hab structural previous hex hcard hexp hB hUN s hp hm hd
  have hgen : A.map F.H.subtype ⊔ B.map F.H.subtype = K F := by
    rw [←Subgroup.map_sup,hAB]
    rfl
  have he : ¬ A.map F.H.subtype ≤ normalizer (L : Set G) ∨
      ¬ B.map F.H.subtype ≤ normalizer (L : Set G) := by
    by_contra! hn
    apply h.flag_escape F previous
    rw [residual_product F,←hgen]
    exact sup_le (sup_le hn.1 hn.2) (h.sylow_normalizes structural)
  obtain ⟨A,hAK,hperfect,hAT,hcardA,hAZ,hker,hquot,hesc⟩ :
      ∃ A : Subgroup F.H, A ≤ pResidual 2 F.H ∧ IsPPerfect 2 A ∧
        (T : Subgroup G).subgroupOf F.H ≤ normalizer (A : Set F.H) ∧
        Nat.card (A.map (starMap F)) = 3 ∧
        A.map (starMap F) ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
        ((starMap F).comp A.subtype).ker = pCore 2 A ∧ Nat.card (A ⧸ pCore 2 A) = 3 ∧
        ¬ A.map F.H.subtype ≤ normalizer (L : Set G) := by
    rcases he with he | he
    · exact ⟨A,le_sup_left.trans_eq hAB,hA.1,hA.2.1,hA.2.2.1,hA.2.2.2.1,
        hA.2.2.2.2.1,hA.2.2.2.2.2,he⟩
    · exact ⟨B,le_sup_right.trans_eq hAB,hB.1,hB.2.1,hB.2.2.1,hB.2.2.2.1,
        hB.2.2.2.2.1,hB.2.2.2.2.2,he⟩
  let Y := A.map F.H.subtype
  have hYH : Y ≤ F.H := map_subtype_le A
  let e : A ≃* Y := equivMapOfInjective A F.H.subtype F.H.subtype_injective
  have hstar : star F Y = A.map (starMap F) := by
    change ((A.map F.H.subtype).comap F.H.subtype).map (starMap F) = _
    rw [comap_map_eq_self_of_injective F.H.subtype_injective]
  have hnorm : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    rw [←map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
    exact (map_mono hAT).trans (le_normalizer_map F.H.subtype)
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hHL : F.H ≤ normalizer (F.Li L 1 : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn
  let f := (starMap F).comp (inclusion hYH)
  have hke : f.ker.comap e.toMonoidHom = pCore 2 A := hker
  have hkerY : f.ker = pCore 2 Y := by
    calc
      f.ker = (f.ker.comap e.toMonoidHom).map e.toMonoidHom :=
        (map_comap_eq_self_of_surjective e.surjective _).symm
      _ = (pCore 2 A).map e.toMonoidHom := congrArg (map e.toMonoidHom) hke
      _ = pCore 2 Y := pCore_map_iso 2 e
  refine ⟨Y,hYH,map_mono hAK,hperfect.of_surjective e.toMonoidHom e.surjective,
    hnorm,hYH.trans hHL,hesc,hstar.symm ▸ hcardA,hstar.symm ▸ hAZ,hkerY,?_⟩
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm.trans hquot

open NoncentralChiefRefinement in
/-- Construct the cubic escape directly from the literal original chief interval.
No representation or normalization premise is supplied by a caller. -/
theorem extraspecial_four_interval_escaping_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let Q := (centralizer (F.U : Set G)).subgroupOf F.H
  have hQ : IsPGroup 2 Q :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)).comap_subtype
  have hBQ : B.val ≤ Q := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hQ.to_le hBQ)
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  have hd : Module.finrank (ZMod 2) (Additive (Section N B)) = 2 := by
    have he : Nat.card (Additive (Section N B)) = 4 := hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) he
  exact extraspecial_two_chief_escaping_cubic h hab structural previous hex hcard hexp hBC hUN s
    ((commutator_mono hBC le_rfl).trans (hp.trans hUN)) hm hd

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
