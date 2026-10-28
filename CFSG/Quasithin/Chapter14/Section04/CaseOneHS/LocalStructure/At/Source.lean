module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.NaturalAction

/-!
# Original HS LocalStructure from the same-G,T inputs

The last solvable irreducible action embeds in SL2(2) wreath C2. Its
normal cubic and index bound identify the literal quotient as S3 by S3,
so the Goldschmidt contradiction completes centerlessness. Only then is
the independent natural-action theorem applied. Thus all local action,
centerlessness, central-product and component premises are discharged.
The genuine earlier naturality, structure, alternatives and faithful
classification remain explicit at the original G,T. Their final discharge
belongs to qt-d-14414-source; the independent overgroup and recognition
steps remain with qt-d-14414-hs-source and qt-i48-hs-recognition.
Source: Aschbacher--Smith 14.3.23--25,28--32, pp.999--1004.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/Source.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
private theorem source_source_wreath_normal_cubic_at
    (f : F.TerminalHdot →* WreathTwoResidual.Actor) (hf : Function.Injective f) :
    (F.terminalDot (F.Li L 1)).Normal ∧ Nat.card (F.terminalDot (F.Li L 1))=3 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let N := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes_at structural)
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
      rw [← (source_closure_at d earlier hq chosen structural alternatives F hne).2.2]
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
theorem source_solvable_irreducible_model_at [IsElementaryAbelian 2 F.Uhat]
    (hZ : F.ZU ≠ F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4)
    (hi : IsIrreducible F.terminalRepresentation) (hs : Group.IsSolvable F.TerminalHdot) :
    Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hb := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
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
  obtain ⟨hn,hcard⟩ := source_source_wreath_normal_cubic_at d earlier hq chosen structural alternatives F hne j hj
  let := hn
  apply WreathCubicRecognition.equiv_pair_of_injective_of_normal_cubic j hj
    (F.terminalDot (F.Li L 1)) hcard
  have hc := H.card_mul_index
  rw [ChapterG.Section09.FittingRecognition.Four.card_orthogonalFour] at hc
  rw [Nat.card_congr e.toEquiv]
  nlinarith [Nat.mul_le_mul_left (Nat.card H) hindex]
theorem source_centerless_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) : Chapter12.Section08.centerIn (F.I₂ L)=⊥ := by
  by_contra hI
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  obtain ⟨hd,hi,hs⟩ := source_contrary_irreducible_solvable_four_at d earlier hq chosen structural
    alternatives classification F hne hZ hI
  exact hI (source_centerless_of_solvable_model_at d earlier hq chosen structural alternatives F hne
    classification hZ (source_solvable_irreducible_model_at d earlier hq chosen structural alternatives
      F hne hZ hd hi hs))
theorem source_localStructure_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) : LocalStructure L F :=
  source_localStructure_of_centerless_at d earlier hq chosen structural alternatives F hne hZ
    (source_centerless_at d earlier hq chosen structural alternatives F hne classification hZ)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end
