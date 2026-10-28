module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Exhaustion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.WholeComponents
public import Theory.GroupTheory.WreathTwoSubgroups
public import Theory.GroupTheory.WreathCubicRecognition

/-!
# Original HS centerlessness and its local-structure application

The exhaustive earlier action reduction leaves only a solvable irreducible
four-space in a putative counterexample to Z(I₂) = 1. Its orthogonal
realization embeds the literal dotted group in SL₂(2) wreath C₂ with
index at most two. The original L₁ is two-perfect and Sylow-normalized,
so its dotted image is normal. Its natural seed action identifies the
hatted kernel on L₁ as O₂(L₁), making that image a normal cubic.

The cubic-normalizer calculation and the index bound identify the actual
dotted group with S₃ × S₃. The completed Goldschmidt and H.5.5 orbit
contradiction then closes this last branch. Thus source_centerless has
no extra local model or exclusion premise.

Apply it first to the original localStructure_of_centerless_action
consumer, and then discharge that action premise with the independent
source action theorem. The latter is used only after centerlessness is
proved. The authorized earlier structural and faithful-classification
inputs remain explicit, with their original universal scopes. This is
a separate extension above the Section04 import boundary.

Source: Aschbacher--Smith 14.3.23--25 and 14.3.28--32, printed
pp.1000--1004; F.6.11, F.6.18 and H.5.5 in the preceding solvable branch.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

private theorem source_wreath_normal_cubic
    (f : F.TerminalHdot →* WreathTwoResidual.Actor) (hf : Function.Injective f) :
    (F.terminalDot (F.Li L 1)).Normal ∧ Nat.card (F.terminalDot (F.Li L 1))=3 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let N := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes structural)
      ((F.invariant 1).trans (F.Gi 1).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.Gi 1) (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)))
  have hLH : F.Li L 1 ≤ F.H := fun x hx => (F.Li_le L 1 hx).2
  have hp : IsPPerfect 2 N := by
    have hh : IsPPerfect 2 (F.Li L 1) := by
      rw [hres]
      exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
    exact hh.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
  let S := (T.subtype (F.invariant 1)).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSN : (S : Subgroup F.TerminalHdot) ≤ normalizer (N.map q : Set F.TerminalHdot) := by
    apply le_trans (map_mono (f := q) ?_) (N.le_normalizer_map q)
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    exact (mem_normalizer_iff.mp (hTn ht)) (x : G)
  have hn : (F.terminalDot (F.Li L 1)).Normal :=
    WreathTwoResidual.normal_of_injective_of_twoPerfect f hf S (N.map q)
      (hp.of_surjective (q.subgroupMap N) (q.subgroupMap_surjective N)) hSN
  refine ⟨hn,?_⟩
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let k := q.comp (inclusion ((F.Li_le L 1).trans inf_le_right))
  have hkperf : IsPPerfect 2 (F.Li L 1) := by
    rw [hres]
    exact isPPerfect_embedded_pResidual 2 _
  let j := f.comp k
  have hjr : j.range ≤ pResidual 2 WreathTwoResidual.Actor :=
    le_pResidual_of_isPPerfect _ (hkperf.of_surjective j.rangeRestrict j.rangeRestrict_surjective)
  have hr : Nat.card (pResidual 2 WreathTwoResidual.Actor)=9 := by
    obtain ⟨e⟩ := WreathTwoResidual.residual_equiv_elementaryNine
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hdis := IsPGroup.disjoint_of_coprime
    (pCore_isPGroup.map j : IsPGroup 2 ((pCore 2 (F.Li L 1)).map j))
    (IsPGroup.of_card (p := 3) (n := 2) hr) (by decide : Nat.Coprime 2 3)
  have hcore : pCore 2 (F.Li L 1) ≤ k.ker := by
    intro a ha
    apply hf
    exact (Subgroup.disjoint_def.mp hdis (mem_map_of_mem j ha) (hjr ⟨a,rfl⟩)).trans f.map_one.symm
  have hkernel : (F.uhatAction.comp (inclusion ((F.Li_le L 1).trans inf_le_right))).ker =
      pCore 2 (F.Li L 1) := by
    apply le_antisymm
    · intro a ha
      rw [←D.seedAction_ker]
      apply (F.mem_tildeAction_ker_iff _ _ _
        ((le_conjugateSpanBy V F.H).trans F.U_le_H) _ a).mpr
      intro v hv
      rw [← (source_closure d earlier hq chosen structural alternatives F hne).2.2]
      refine ⟨V.mul_mem ((mem_normalizer_iff.mp
        (chosen.normalizes (F.Li_le L 1 a.property).1) v).mp hv) (V.inv_mem hv),?_⟩
      exact (F.mem_uhatAction_ker_iff _).mp ha v (le_conjugateSpanBy V F.H hv)
    · intro a ha
      have hh : (⟨a,(F.Li_le L 1 a.property).2⟩ : F.H) ∈ q.ker := hcore ha
      rw [show q.ker=F.uhatAction.ker from QuotientGroup.ker_mk' _] at hh
      exact hh
  have hrange : k.range=F.terminalDot (F.Li L 1) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨_,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have hk : k.ker=pCore 2 (F.Li L 1) := by
    rw [←hkernel]
    ext a
    exact QuotientGroup.eq_one_iff _
  rw [←hrange,←Nat.card_congr (QuotientGroup.quotientKerEquivRange k).toEquiv,hk,
    Nat.card_congr D.quotientEquiv.toEquiv]
  exact BinaryLinear.SmallParabolicLevi.derived_two_card


/-- The remaining solvable irreducible action is the literal symmetric-three product. -/
theorem source_solvable_irreducible_model [IsElementaryAbelian 2 F.Uhat]
    (hZ : F.ZU ≠ F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4)
    (hi : IsIrreducible F.terminalRepresentation) (hs : Group.IsSolvable F.TerminalHdot) :
    Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hb := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  have hr : 2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by omega
  have hX : F.terminalDot (F.X g)≠⊥ := by
    intro he
    let : Subsingleton (F.terminalDot (F.X g)) := he ▸ inferInstance
    have hz : finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))=0 :=
      Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨_,_,H,hindex,e,c,he⟩ := hyp.orthogonal_case_of_rank_bound
    (CaseOneLarge.source_terminal_cover F d chosen) hs hi hX hr hb
  let E := ChapterG.Section09.FittingRecognition.Four.splitOrthogonalEquiv.trans
    (BinaryFourPlus.isometryEquivWreath.trans
      (RegularWreathProduct.congr
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm (MulEquiv.refl _)))
  let j := E.toMonoidHom.comp (H.subtype.comp e.toMonoidHom)
  have hj : Function.Injective j := E.injective.comp (Subtype.val_injective.comp e.injective)
  obtain ⟨hn,hcard⟩ := source_wreath_normal_cubic d earlier hq chosen structural alternatives F hne j hj
  let := hn
  apply WreathCubicRecognition.equiv_pair_of_injective_of_normal_cubic j hj
    (F.terminalDot (F.Li L 1)) hcard
  have hc := H.card_mul_index
  rw [ChapterG.Section09.FittingRecognition.Four.card_orthogonalFour] at hc
  rw [Nat.card_congr e.toEquiv]
  nlinarith [Nat.mul_le_mul_left (Nat.card H) hindex]

/-- The original centerlessness theorem, with every local action alternative discharged. -/
theorem source_centerless
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) : Chapter12.Section08.centerIn (F.I₂ L)=⊥ := by
  by_contra hI
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  obtain ⟨hd,hi,hs⟩ := source_contrary_irreducible_solvable_four d earlier hq chosen structural
    alternatives classification F hne hZ hI
  exact hI (source_centerless_of_solvable_model d earlier hq chosen structural alternatives F hne
    classification hZ (source_solvable_irreducible_model d earlier hq chosen structural alternatives
      F hne hZ hd hi hs))

/-- Apply source 14.3.31 to the original local structure, retaining its independent action input. -/
theorem localStructure_of_source_centerless_action
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless d earlier hq chosen structural alternatives F hne classification hZ) action

/-- Assemble the independent source action theorem after proving centerlessness,
with the original earlier-source inputs still explicit. -/
theorem source_localStructure
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) : LocalStructure L F :=
  source_localStructure_of_centerless d earlier hq chosen structural alternatives F hne hZ
    (source_centerless d earlier hq chosen structural alternatives F hne classification hZ)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless


