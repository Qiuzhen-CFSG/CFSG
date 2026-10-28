module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Geometry
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The full dotted center residual in original 14.3.15

The displaced center is a nontrivial normal subgroup of the original dotted
Sylow subgroup. Its normal closure has the entire two-residual in the full
orthogonal action, with order nine and a marked inverter lying in the
original displaced center. Relative normal closure and residual images are
transported through the literal terminal quotient map.

Source: Aschbacher--Smith 14.3.15, printed p.995.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {L M : Subgroup G}

omit [Finite G] in
theorem terminalDot_centerConjugateSpan_eq_normalClosure
    (F : InvariantFlag T V 2) (g : G) (hg : conjugate F.ZU g ≤ F.H) :
    F.terminalDot (centerConjugateSpan F g) =
      normalClosure (F.terminalDot (conjugate F.ZU g) : Set F.TerminalHdot) := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  change ((conjugateSpanBy (conjugate F.ZU g) F.H).subgroupOf F.H).map q = _
  rw [← normalClosure_subgroupOf_eq_conjugateSpanBy _ _ hg,
    map_normalClosure _ q (QuotientGroup.mk'_surjective _)]
  rfl

theorem terminalDot_centerConjugateResidual_eq_embedded
    (F : InvariantFlag T V 2) (g : G) (hg : conjugate F.ZU g ≤ F.H) :
    F.terminalDot (centerConjugateResidual F g) =
      (pResidual 2 (normalClosure
        (F.terminalDot (conjugate F.ZU g) : Set F.TerminalHdot))).map
        (normalClosure (F.terminalDot (conjugate F.ZU g) : Set F.TerminalHdot)).subtype := by
  let J := centerConjugateSpan F g
  have hJH : J ≤ F.H := centerConjugateSpan_le_H F g hg
  let JH := J.subgroupOf F.H
  have he : ((pResidual 2 JH).map JH.subtype).map F.H.subtype =
      centerConjugateResidual F g := by
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hJH]
    rfl
  have he' : (centerConjugateResidual F g).subgroupOf F.H =
      (pResidual 2 JH).map JH.subtype := by
    rw [← he, subgroupOf, comap_map_eq_self_of_injective F.H.subtype_injective]
  change ((centerConjugateResidual F g).subgroupOf F.H).map
    (QuotientGroup.mk' F.terminalHatAction.ker) = _
  rw [he',map_embedded_pResidual]
  change (pResidual 2 (F.terminalDot (centerConjugateSpan F g))).map
    (F.terminalDot (centerConjugateSpan F g)).subtype = _
  rw [terminalDot_centerConjugateSpan_eq_normalClosure F g hg]

private theorem full_orthogonal_group_equiv
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization ρ ⊤) :
    Nonempty (D ≃* WreathTwoResidual.Actor) := by
  obtain ⟨e,_,_⟩ := hr
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨e.trans (topEquiv.trans
    ((ChapterG.Section09.FittingRecognition.Four.splitOrthogonalEquiv.trans
      BinaryFourPlus.isometryEquivWreath).trans
      (RegularWreathProduct.congr eSL.symm (MulEquiv.refl _))))⟩

private theorem full_orthogonal_normal_sylow_residual
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization ρ ⊤)
    (P : Sylow 2 D) (R : Subgroup D) (hle : R ≤ (P : Subgroup D))
    (hn : (P : Subgroup D) ≤ normalizer (R : Set D)) (hne : R ≠ ⊥) :
    (pResidual 2 (normalClosure (R : Set D))).map
      (normalClosure (R : Set D)).subtype = pResidual 2 D ∧
    Nat.card (pResidual 2 D) = 9 ∧
    ∃ r : D, r ∈ R ∧ orderOf r = 2 ∧
      ∀ x : D, x ∈ pResidual 2 D → r*x*r⁻¹=x⁻¹ := by
  obtain ⟨e⟩ := full_orthogonal_group_equiv ρ hr
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let R' := R.map e.toMonoidHom
  have hle' : R' ≤ (P' : Subgroup WreathTwoResidual.Actor) := map_mono hle
  have hn' : (P' : Subgroup WreathTwoResidual.Actor) ≤ normalizer (R' : Set _) :=
    (map_mono hn).trans (le_normalizer_map _)
  have hne' : R' ≠ ⊥ := by
    intro hb
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_bot]
    exact hb
  have heR : (normalClosure (R : Set D)).map e.toMonoidHom =
      normalClosure (R' : Set _) := map_normalClosure _ _ e.surjective
  have hr' := WreathTwoResidual.normalClosure_residual_eq P' R' hle' hn' hne'
  refine ⟨?_,?_,?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_embedded_pResidual,heR,map_pResidual]
    exact hr'
  · obtain ⟨ee⟩ := WreathTwoResidual.residual_equiv_elementaryNine
    rw [Nat.card_congr (e.subgroupMap (pResidual 2 D)).toEquiv]
    change Nat.card ((pResidual 2 D).map e.toMonoidHom) = 9
    rw [map_pResidual 2 e,Nat.card_congr ee.toEquiv]
    norm_num [Nat.card_fun,Nat.card_zmod]
  · obtain ⟨r,hr,hord,hinv⟩ :=
      WreathTwoResidual.exists_normal_sylow_inverter P' R' hle' hn' hne'
    obtain ⟨a,ha,hea⟩ := hr
    change e a = r at hea
    refine ⟨a,ha,?_,?_⟩
    · rw [← e.orderOf_eq a,hea]
      exact hord
    · intro x hx
      apply e.injective
      simp only [map_mul,map_inv,hea]
      exact hinv (e x) ((map_pResidual 2 e) ▸ (mem_map_of_mem e.toMonoidHom hx))

theorem rankTwo_full_orthogonal_center_residual
    (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g∈F.P L) (hgH : g∉F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (_hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU≠F.Vi 1)
    (hr : ChapterG.Section09.FittingRecognition.OrthogonalRealization
      F.terminalRepresentation ⊤) :
    F.terminalDot (centerConjugateResidual F g) = pResidual 2 F.TerminalHdot ∧
    Nat.card (F.terminalDot (centerConjugateResidual F g)) = 9 ∧
    ∃ r : F.TerminalHdot, r∈F.terminalDot (conjugate F.ZU g) ∧ orderOf r=2 ∧
      ∀ x : F.TerminalHdot, x∈pResidual 2 F.TerminalHdot → r*x*r⁻¹=x⁻¹ := by
  have hg := F.conjugate_center_le_H g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)
  obtain ⟨hle,hn⟩ := rankTwo_conjugate_center_normal_in_Tdot h F hne g hgP hgH
  have hnormal := (normal_subgroupOf_iff_le_normalizer hle).mp hn
  have hne' : F.terminalDot (conjugate F.ZU g) ≠ ⊥ :=
    F.terminalDot_center_ne_bot g hg (rankTwo_terminal_center_kernel h F d hne g hgP hgH)
      (lt_of_le_of_ne (F.point_le_ZU (by decide)) (Ne.symm hZ))
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨he,hcard,hinv⟩ := full_orthogonal_normal_sylow_residual
    F.terminalRepresentation hr P (F.terminalDot (conjugate F.ZU g)) hle hnormal hne'
  have he' := (terminalDot_centerConjugateResidual_eq_embedded F g hg).trans he
  exact ⟨he',he'.symm ▸ hcard,hinv⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
