module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.EarlierNontrivial
public import Theory.SpecificGroups.BinaryLinear.DerivedTwoCardinality
public import Theory.SpecificGroups.SymmetricThreeProduct.MarkedNormalClosure

/-!
# Constructing the original solvable marked seed row

For the actual quotient H/C_H(U/Z(U)) isomorphic to S₃ × S₃, the
point residual L₁ has hatted action kernel O₂(L₁). Indeed its image lies
in the odd two-residual, while its faithful natural action on V/V₁ gives
the reverse kernel containment. Its dotted image therefore has order three
and acts faithfully on the original seed plane.

The earlier Sylow argument makes dotted L₁ normal. Since Z(U)^g fixes
the seed plane pointwise, its dotted image centralizes dotted L₁. The
literal product model then identifies its normal closure as the other S₃
factor, gives the order-two marked image, and proves the L₁T supplement.
Transport through the same quotient map constructs SolvableSeedRow.

The checked central-quotient argument now proves the solvable branch of
14.3.25 from the model alone. Its application discharges the seed premise
in the Thompson containment used by the Goldschmidt branch of 14.3.31.
The earlier exhaustive model alternatives, nonsolvable marked rows, and
remaining centerlessness contradictions stay with this task. No theorem
assuming centerlessness is used here.

This extension uses the earlier nontriviality theorem above the Section04
boundary and is imported directly. Final source_centerless and its literal
LocalStructure application remain to be assembled.
Source: Aschbacher--Smith, 14.3.23(2)(i), 14.3.25 and 14.3.29--31,
printed pp.1000--1003, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_solvable_point_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    (F.uhatAction.comp (inclusion ((F.Li_le L 1).trans inf_le_right))).ker =
      pCore 2 (F.Li L 1) := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let q := QuotientGroup.mk' F.uhatAction.ker
  let f := q.comp (inclusion ((F.Li_le L 1).trans inf_le_right))
  have hp : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 _
  have hfr : f.range ≤ pResidual 2 (Hdot F F.uhatAction) :=
    le_pResidual_of_isPPerfect _ (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  obtain ⟨e⟩ := model
  have hr : Nat.card (pResidual 2 (Hdot F F.uhatAction)) = 9 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,
      map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
    exact SymmetricThreeProductResidual.residual_card
  have hdis := IsPGroup.disjoint_of_coprime
    (pCore_isPGroup.map f : IsPGroup 2 ((pCore 2 (F.Li L 1)).map f))
    (IsPGroup.of_card (p := 3) (n := 2) hr) (by decide : Nat.Coprime 2 3)
  have hcore : pCore 2 (F.Li L 1) ≤ f.ker := by
    intro k hk
    exact Subgroup.disjoint_def.mp hdis (mem_map_of_mem f hk) (hfr ⟨k,rfl⟩)
  apply le_antisymm
  · intro k hk
    rw [←D.seedAction_ker]
    apply (F.mem_tildeAction_ker_iff _ _ _
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) _ k).mpr
    intro v hv
    rw [← (source_closure d earlier hq chosen structural alternatives F hne).2.2]
    refine ⟨V.mul_mem ((mem_normalizer_iff.mp
      (chosen.normalizes (F.Li_le L 1 k.property).1) v).mp hv) (V.inv_mem hv),?_⟩
    exact (F.mem_uhatAction_ker_iff _).mp hk v (le_conjugateSpanBy V F.H hv)
  · intro k hk
    have hh : (⟨k,(F.Li_le L 1 k.property).2⟩ : F.H) ∈ q.ker := hcore hk
    rw [show q.ker = F.uhatAction.ker from QuotientGroup.ker_mk' _] at hh
    exact hh

private theorem source_solvable_point_order (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nat.card (dotImage F F.uhatAction (F.Li L 1)) = 3 := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let q := QuotientGroup.mk' F.uhatAction.ker
  let f := q.comp (inclusion ((F.Li_le L 1).trans inf_le_right))
  have hrange : f.range = dotImage F F.uhatAction (F.Li L 1) := by
    ext x
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨_,k.property,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,hk⟩,rfl⟩
  have hker : f.ker = pCore 2 (F.Li L 1) := by
    rw [←source_solvable_point_kernel d earlier hq chosen structural alternatives F hne model]
    ext k
    exact QuotientGroup.eq_one_iff _
  rw [←hrange,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hker,
    Nat.card_congr D.quotientEquiv.toEquiv]
  exact BinaryLinear.SmallParabolicLevi.derived_two_card

private theorem source_solvable_point_faithful_on_seed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (n : Hdot F F.uhatAction) (hn : n ∈ dotImage F F.uhatAction (F.Li L 1))
    (hf : ∀ w ∈ hatSpace F V, F.terminalRepresentation n w = w) : n = 1 := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  obtain ⟨k,hk,rfl⟩ := hn
  let kL : F.Li L 1 := ⟨k,hk⟩
  have hc : kL ∈ pCore 2 (F.Li L 1) := by
    rw [←D.seedAction_ker]
    apply (F.mem_tildeAction_ker_iff _ _ _
      ((le_conjugateSpanBy V F.H).trans F.U_le_H) _ kL).mpr
    intro v hv
    rw [← (source_closure d earlier hq chosen structural alternatives F hne).2.2]
    refine ⟨V.mul_mem ((mem_normalizer_iff.mp
      (chosen.normalizes (F.Li_le L 1 hk).1) v).mp hv) (V.inv_mem hv),?_⟩
    let vU : F.U := ⟨v,le_conjugateSpanBy V F.H hv⟩
    have he := congrArg Additive.toMul (hf (hatElement F vU) ⟨vU,hv,rfl⟩)
    change F.uhatAction k (QuotientGroup.mk' (center F.U) vU) =
      QuotientGroup.mk' (center F.U) vU at he
    rw [F.uhatAction_apply_mk] at he
    refine ⟨_,QuotientGroup.eq_iff_div_mem.mp he,?_⟩
    simp only [commutatorElement_def,div_eq_mul_inv]
    rfl
  have hh := (source_solvable_point_kernel d earlier hq chosen structural alternatives F hne model).symm ▸ hc
  exact (QuotientGroup.eq_one_iff k).mpr hh

private theorem source_solvable_center_centralizes_point_image (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (g : G) (hgP : g ∈ F.P L) :
    dotImage F F.uhatAction (conjugate F.ZU g) ≤
      centralizer (dotImage F F.uhatAction (F.Li L 1) : Set (Hdot F F.uhatAction)) := by
  let N := dotImage F F.uhatAction (F.Li L 1)
  let ρ := elementaryRepresentation (p := 2) (faithfulAction F F.uhatAction)
  let W := hatSpace F V
  let := source_dot_Li_one_normal_of_symmetricThreePair d earlier hq chosen structural F model
  have hstable (n : Hdot F F.uhatAction) (hn : n ∈ N) (w : Additive F.Uhat) (hw : w ∈ W) :
      ρ n w ∈ W := by
    obtain ⟨k,hk,rfl⟩ := hn
    obtain ⟨v,hv,he⟩ := hw
    refine ⟨F.uAction k v,(mem_normalizer_iff.mp
      (chosen.normalizes (F.Li_le L 1 hk).1) (v:G)).mp hv,?_⟩
    change QuotientGroup.mk' (center F.U) (F.uAction k v) = F.uhatAction k w.toMul
    rw [←F.uhatAction_apply_mk,he]
  intro z hz n hn
  have hzK : z ∈ BinaryOffender.subspaceKernel ρ W ⊤ :=
    ⟨mem_top _,source_conjugate_center_fixes_seed chosen F g hgP z hz⟩
  have hzi := (BinaryOffender.subspaceKernel ρ W ⊤).inv_mem hzK
  have hm : n⁻¹ * (z*n*z⁻¹) ∈ N := N.mul_mem (N.inv_mem hn)
    ((inferInstance : N.Normal).conj_mem n hn z)
  have he : n⁻¹ * (z*n*z⁻¹) = 1 :=
    source_solvable_point_faithful_on_seed d earlier hq chosen structural alternatives F hne model _ hm (by
      intro w hw
      change ρ (n⁻¹ * (z*n*z⁻¹)) w = w
      simp only [map_mul,Module.End.mul_apply,hzi.2 w hw,hzK.2 _ (hstable n hn w hw)]
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply])
  exact (mul_inv_eq_iff_eq_mul.mp (inv_mul_eq_one.mp he).symm).symm

/-- Construct every marked-row premise from the actual solvable quotient and original flag. -/
theorem source_solvable_seed_row (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : SolvableSeedRow F L g := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let q := QuotientGroup.mk' F.uhatAction.ker
  let N := dotImage F F.uhatAction (F.Li L 1)
  let A := dotImage F F.uhatAction (conjugate F.ZU g)
  let := source_dot_Li_one_normal_of_symmetricThreePair d earlier hq chosen structural F model
  let := source_actor_elementary d earlier hq chosen structural alternatives F hne g hgP hgH
  have hAX : A ≤ dotImage F F.uhatAction (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAX
  have hpL : IsPPerfect 2 (F.Li L 1) := by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 _
  let f : F.Li L 1 →* N :=
    (q.comp (inclusion ((F.Li_le L 1).trans inf_le_right))).codRestrict N
      (fun k => mem_map_of_mem q k.property)
  have hfs : Function.Surjective f := by
    rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨k,hk⟩,rfl⟩
  let S := (T.subtype (F.invariant 1)).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨hc,hm,hs⟩ := SymmetricThreeProduct.marked_normalClosure model N A
    (hpL.of_surjective f hfs)
    (source_solvable_point_order d earlier hq chosen structural alternatives F hne model)
    (source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives F hne hZ g hgP hgH)
    (source_solvable_center_centralizes_point_image d earlier hq chosen structural alternatives F hne model g hgP) S
  have hAH : conjugate F.ZU g ≤ F.H := by
    intro z hz
    exact (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP ⟨z,hz⟩).property
  have hK : solvableSeedActor F g =
      conjugateSpanBy ((conjugate F.ZU g).subgroupOf F.H) ⊤ := by
    apply map_injective F.H.subtype_injective
    rw [solvableSeedActor_map F chosen.normalizes g hgP,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hAH,←MonoidHom.range_eq_map,range_subtype]
  have hKm : (solvableSeedActor F g).map q = conjugateSpanBy A ⊤ := by
    rw [hK,map_conjugateSpanBy,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rfl
  refine ⟨?_,?_,hc⟩
  · rw [hKm]
    exact hm
  · rw [hKm]
    exact hs

/-- The solvable branch of 14.3.25, with the marked row and elementary quotient constructed. -/
theorem source_seed_exclusion_of_solvable_model (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) : centralLTSeed F L = ⊥ := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  by_cases hZ : F.ZU = F.Vi 1
  · apply le_bot_iff.mp
    intro z hz
    have hzP := (source_centralLT_seed d earlier hq chosen structural alternatives F).2.1 hz
    rw [hZ] at hzP
    exact (source_point_inf_centerLT d earlier hq chosen structural F).le ⟨hzP,hz.1⟩
  · obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
    exact source_seed_exclusion_of_symmetricThreePair d earlier hq chosen structural alternatives F hne
      g hgP hgH (source_solvable_seed_row d earlier hq chosen structural alternatives F hne hZ model g hgP hgH) model

/-- The literal Thompson containment for the Goldschmidt branch, with its seed premise discharged. -/
theorem source_solvable_model_thompson_le_plane_core (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U)
    (model : Nonempty ((Hdot F F.uhatAction) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  source_contrary_thompson_le_plane_core d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_solvable_model d earlier hq chosen structural alternatives F hne model) hI


end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
