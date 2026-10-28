module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNondegenerate
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedModels
public import Theory.GroupTheory.GeneralizedFitting.ComponentSimpleQuotient
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryHigherResidual

/-!
# The kernel of the original exchanged constituent

For a noncentral kernel, the separating exchanged actions make component Sylow
two-subgroups elementary. The literal HY action quotient then satisfies G.9
with its original self-dual action and sharp stabilizer degree. Its image is
A5, with the exact constituent kernel, and its constituent has dimension four.

For a central kernel, the already proved centerlessness gives faithfulness.
The entire original actor embeds in the image automorphism group. Its order
and moved-constituent intertwining obstruction exclude A5 and the exceptional
A6 module; the original cubic-rank bound and the actual orthogonal module
exclude every higher symplectic and orthogonal residual.

The two kernel conclusions are applied to the same original flag in
ExchangedNondegenerateExclusion. No constituent faithfulness, recognition
callback or unmarked replacement for the action is assumed.
Source: Aschbacher--Smith G.10.15, G.11.6, G.12.1, printed pp.362--366,370;
14.4.2 and 14.4.14, pp.1006--1012, refs/quasithin.pdf. The proof adapts the
checked Section03 exchanged-kernel arguments to the rank-three source flag.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedKernel
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
  (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
  (hm : ⁅C,X⁆ ≠ ⊥) (S : Sylow 2 D)
  (hSX : (S : Subgroup D) ≤ normalizer (X : Set D))
  (hind : (normalizer (C : Set D)).index ≤ 2)
  {I : Submodule (ZMod 2) U}
  (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) (hv : v ∉ I)
  (hk : ¬ (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom.ker ≤
    center (componentOrbit C ⊤))
  (hc : ExchangedGeometry.CompletedData ρ B C X I hI)
  (hnd : (B.restrict I).Nondegenerate)

include h hn hC hind hI hk in
private theorem normalizer_index_eq_two : (normalizer (C : Set D)).index = 2 := by
  have hp := (normalizer (C : Set D)).index_ne_zero_of_finite
  have h1 : (normalizer (C : Set D)).index ≠ 1 := by
    intro he
    let : C.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp he)
    let H := componentOrbit C ⊤
    let : H.Normal := componentOrbit_top_normal C
    have heH : H = C := le_antisymm
      (iSup_conjugates_le_of_le_normalizer C ⊤ C le_rfl (by rw [normalizer_eq_top]))
      (le_componentOrbit C ⊤)
    let : IsQuasisimple H := heH.symm ▸ hC.2
    let R := invariantSubspace ρ H I hI.invariant
    rcases IsQuasisimple.normal_le_center_or_eq_top R.toRepresentation.asGroupHom.ker with hker | ht
    · exact hk hker
    · have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
        (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
      have hle : I ≤ fixedSpace ρ H := by
        intro u hu a
        have ha : R.toRepresentation.asGroupHom a = 1 := MonoidHom.mem_ker.mp (ht ▸ mem_top a)
        exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : U)) ha
      exact hI.isIrrPlus.ne_bot ρ (bot_unique (hfix ▸ hle))
  omega

include h hn hC hm S hSX hind hI hv hk in
private theorem orbit_sylow_elementary (P : Sylow 2 (componentOrbit C ⊤)) :
    IsElementaryAbelian 2 P := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let R := invariantSubspace ρ H I hI.invariant
  let N := R.toRepresentation.asGroupHom.ker
  obtain ⟨x,_,hsep⟩ := h.exchanged_pair_separates hn hC hm S hSX hind hI hv
  let : IsElementaryAbelian 2 ((((S : Subgroup D).subgroupOf H) ⊓ N) : Subgroup H) :=
    Representation.BinaryOffender.ExchangedKernel.kernel_sylow_elementary ρ H X S hSX R x hsep
  have hcomp (P : Sylow 2 C) : IsElementaryAbelian 2 P :=
    Representation.BinaryOffender.ExchangedKernel.component_sylow_elementary_of_kernel hC S N hk P
  exact ExchangedOrbit.orbit_sylow_elementary hC
    (normalizer_index_eq_two h hn hC hind hI hk) hcomp P

include h hn hC hm S hSX hind hI hv hk hc hnd in
/-- The noncentral constituent kernel gives an actual A5 quotient of the original
component orbit, with exactly the original constituent kernel. -/
theorem noncentral_five_quotient
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D)) :
    finrank (ZMod 2) I = 4 ∧
    ∃ p : componentOrbit C ⊤ →* alternatingGroup (Fin 5), Function.Surjective p ∧
      (∀ a, p a = 1 ↔
        (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation a = 1) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let A := ExchangedAction.actor ρ X I
  let P := H ⊔ A
  let R := invariantSubspace ρ H I hI.invariant
  let σ := ExchangedAction.imageAction ρ H X I hI.invariant
  let π := ExchangedAction.projection ρ H X I hI.invariant
  let image := ExchangedAction.image ρ H X I hI.invariant
  let Q := ExchangedAction.quotient ρ H X I hI.invariant
  have hd := hI.isIrrPlus.finrank_gt_two ρ H
  have hi := hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H
  let r : H →* image H := (π.subgroupMap (H.subgroupOf P)).comp
    (subgroupOfEquivOfLe (show H ≤ P from le_sup_left)).symm.toMonoidHom
  have hr : Function.Surjective r := (π.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe (show H ≤ P from le_sup_left)).symm.surjective
  have hrker (a : H) : r a = 1 ↔ R.toRepresentation a = 1 := by
    rw [← Subtype.val_inj]
    exact QuotientGroup.eq_one_iff _
  have hne : image H ≠ ⊥ := by
    intro hz
    have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
      (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
    apply hI.isIrrPlus.ne_bot ρ
    apply bot_unique
    rw [← hfix]
    intro u hu a
    have he : r a = 1 := Subtype.ext (mem_bot.mp (hz ▸ (r a).property))
    exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩ : U)) ((hrker a).mp he)
  have hcomponent : IsComponent Q (image H) := by
    apply ExchangedOrbit.image_orbit_component hC
      (normalizer_index_eq_two h hn hC hind hI hk) P le_sup_left π
      (QuotientGroup.mk'_surjective _) _ hne
    intro hker
    apply hk
    intro a ha
    apply hker
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff _).mpr
    exact congrArg Units.val (MonoidHom.mem_ker.mp ha)
  have hnormal : (image H).Normal := Subgroup.Normal.map inferInstance π
    (QuotientGroup.mk'_surjective _)
  have hir : IsIrreducible (σ.comp (image H).subtype) :=
    (irreducible_comp_surjective_iff r hr _).mp hi
  have hself : Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) := by
    refine ⟨.mk ((B.restrict I).toDual hnd) ?_⟩
    intro a
    ext u w
    change B (ρ a u) w = B u (ρ (a⁻¹ : H) w)
    have he := h.preserves (a : D) (u : U) (ρ (a⁻¹ : H) w)
    simpa only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel,
      map_one, Module.End.one_apply] using he
  have hself' := MarkedAction.selfDual_image ρ H A I hI.invariant inf_le_left hself
  have hfaithA := h.spanning_constituent_stabilizer_faithful hc.2.1
  let eA := ExchangedAction.actorEquiv ρ H X I hI.invariant hfaithA
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion (show A ≤ X from inf_le_right)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (A.subgroupOf P) := IsElementaryAbelian.subgroupOf
    (show A ≤ P from le_sup_right)
  have hcard : Nat.card A = 2 ^ (finrank (ZMod 2) I - 2) := by
    let Y := (subspaceStabilizer ρ I).subgroupOf X
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    have he : finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 := hc.2.2.2.1
    have hy : Nat.card Y = 2 ^ finrank (ZMod 2) (Additive Y) := by
      change Nat.card (Additive Y) = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    rw [← Nat.card_congr (ExchangedAction.stabilizerEquiv ρ X I).toEquiv, hy]
    congr 1
    omega
  have setup : ChapterG.Section09.Setup σ (image A) (finrank (ZMod 2) I - 2) := {
    faithful := kerRepresentation_faithful _
    elementary := IsElementaryAbelian.map π
    card_actor := (Nat.card_congr eA.toEquiv).symm.trans hcard
    degree_le := by omega }
  have hmove : ⁅image H,image A⁆ ≠ ⊥ := by
    intro hz
    let : IsElementaryAbelian 2 (image A) := setup.elementary
    let : IsIrreducible (σ.comp (image H).subtype) := hir
    have htriv : ∀ a : image A, a = 1 := by
      intro a
      apply Subtype.ext
      apply Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
        σ (image H) setup.faithful
      · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ a.property
      · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz) a.property
    have ha : Nat.card (image A) = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,htriv⟩
    have hh : Nat.card (image A) = 2 ^ (finrank (ZMod 2) I - 2) := setup.card_actor
    have hp := one_lt_pow' (by decide : 1 < 2)
      (show finrank (ZMod 2) I - 2 ≠ 0 by omega)
    omega
  have input : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple σ
      (image A) (image H) (image H) (finrank (ZMod 2) I - 2) := {
    setup with
    quotient := ⟨((Classical.choice cover).subgroup P).map π (QuotientGroup.mk'_surjective _)⟩
    component := hcomponent
    noncentral := hmove
    normal_H := hnormal
    irreducible := hir
    components := Or.inl rfl }
  have hel (P : Sylow 2 (image H)) : IsElementaryAbelian 2 P :=
    ExchangedOrbit.elementary_sylow_image r hr
      (orbit_sylow_elementary h hn hC hm S hSX hind hI hv hk) P
  obtain ⟨e⟩ := PairedA5Models.alternating_five_of_selfDual_sharp_elementary input
    (by omega) hel hself'
  have hd4 : finrank (ZMod 2) I = 4 := by
    let : (image H).Normal := hnormal
    let : IsIrreducible (σ.comp (image H).subtype) := hir
    have hrank := input.toSetup.rank_le_automorphisms (L := image H)
      (by rw [normalizer_eq_top]; exact le_top)
    rw [primeRank_equiv 2 (MulAut.congr e)] at hrank
    have hbound := Theory.SpecificGroups.Alternating.FiveExtensionAction.automorphism_primeRank_two_le
    obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
      (fun w => h.alternating w) hnd
    omega
  refine ⟨hd4,e.toMonoidHom.comp r, e.surjective.comp hr, fun a => ?_⟩
  exact e.map_eq_one_iff.trans (hrker a)

include h hn hC hm S hSX hind hI hv hc in
private theorem actor_obstruction
    (hfI : Function.Injective (invariantSubspace ρ (componentOrbit C ⊤) I
      hI.invariant).toRepresentation.asGroupHom) :
    ∃ E : Subgroup (MulAut (ExchangedNondegenerate.constituentLinearAction ρ C X I hI).range),
      IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ (finrank (ZMod 2) I - 1) ∧
      ∃ α ∈ E, ¬ ∃ c : I ≃ₗ[ZMod 2] I,
        ∀ k : (ExchangedNondegenerate.constituentLinearAction ρ C X I hI).range, ∀ u : I,
          c (k.val u) = (α k).val (c u) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  have hgeo := h.exchanged_constituent_geometry hn hC hm S hSX hind hI hv
  have hY := hc.2.2.2.2.2.1
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  let f : X →* MulAut H := MulAut.conjNormal.comp X.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro z hz
    have hz1 : f z = 1 := hz
    have hzinv : (z : D)⁻¹ = z := inv_eq_iff_mul_eq_one.mpr (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (z : D) z.property)
    have hzY : (z : D) ∈ subspaceStabilizer ρ I := by
      by_contra hn
      have hm : I.map (ρ (z : D)⁻¹) ≠ I := by
        rw [hzinv]
        exact fun he => hn ((subspace_map_eq_iff ρ I _).mp he)
      have ho := hI.conjugation_not_inner ρ
        hfix z hm
      apply ho
      change f z ∈ MulAut.innerSubgroup H
      rw [hz1]
      exact (MulAut.innerSubgroup H).one_mem
    have hzc : (z : D) ∈ centralizer (H : Set D) := by
      rw [mem_centralizer_iff]
      intro h hh
      have he := congrArg (fun a : MulAut H => (a ⟨h,hh⟩ : D)) hz1
      change (z : D) * h * (z : D)⁻¹ = h at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have he := hY (⟨z,hzY⟩ : Y) hzc
    exact mem_bot.mpr (congrArg Subtype.val he)
  let e : H ≃* (ExchangedNondegenerate.constituentLinearAction ρ C X I hI).range := MonoidHom.ofInjective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective.comp
      hfI)
  let a : X →* MulAut (ExchangedNondegenerate.constituentLinearAction ρ C X I hI).range :=
    (MulAut.congr e).toMonoidHom.comp f
  have ha : Function.Injective a := (MulAut.congr e).injective.comp hf
  let E := a.range
  have hE : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective (MonoidHom.ofInjective ha).symm.toMonoidHom
      (MonoidHom.ofInjective ha).symm.injective
  have hcard : Nat.card E = 2 ^ (finrank (ZMod 2) I - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective ha).toEquiv]
    have hindex := hgeo
    obtain ⟨_,_,_,_,hindex,_⟩ := hindex
    have hcy := Y.card_mul_index
    have hy : Nat.card Y = 2 ^ finrank (ZMod 2) (Additive Y) := by
      change Nat.card (Additive Y) = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    have hx : Nat.card X = 2 ^ finrank (ZMod 2) (Additive X) := by
      change Nat.card (Additive X) = _
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rw [show Y.index = 2 from hindex,hy,hx,← pow_succ] at hcy
    have hr := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hcy
    have hd : finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 := hc.2.2.2.1
    change Nat.card (Additive X) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    congr 1
    omega
  obtain ⟨x,hx,_⟩ := hgeo
  refine ⟨E,hE,hcard,a x,⟨x,rfl⟩,?_⟩
  rintro ⟨c,hc'⟩
  let R := invariantSubspace ρ H I hI.invariant
  have hα (h : H) : a x (e h) = e (MulAut.conjNormal (x : D) h) := by
    change e (MulAut.conjNormal (x : D) (e.symm (e h))) = _
    rw [e.symm_apply_apply]
  let b : RepEquiv R.toRepresentation
      (conjugateRep R.toRepresentation (x : D)) := .mk c (by
    intro h
    apply LinearMap.ext
    intro u
    have he := hc' (e h) u
    rw [hα] at he
    exact he)
  have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : D) x.property)
  exact hI.not_equiv_moved ρ hfix x
    (by rwa [hxi])
    ⟨(b.trans (conjugateSubrepresentationEquiv ρ H R
      (x : D)).symm).toRepresentationEquiv⟩


include h hn hC hm S hSX hind hI hv hc hnd in
/-- The central-kernel alternative is impossible for the actual recognized
nondegenerate image. The whole actor and original cubic-rank bound are used. -/
theorem not_central_kernel
    (hrank : primeRank 3 D ≤ 2)
    (models : ExchangedNondegenerate.RecognizedData ρ B C X I hI) :
    ¬ (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation.asGroupHom.ker ≤
      center (componentOrbit C ⊤) := by
  intro hker
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let K := (ExchangedNondegenerate.constituentLinearAction ρ C X I hI).range
  have hz := ExchangedNondegenerate.recognized_image_centerless h hn hC hI hnd models
  have hf := faithful_constituent_of_centerless_image ρ h.faithful
    (h.irreducible_of_not_solvable hn) H I hI.invariant (hI.isIrrPlus.ne_bot ρ) hz hker
  let e : H ≃* K := MonoidHom.ofInjective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective.comp hf)
  let : Finite K := Finite.of_surjective e e.surjective
  have hbound : primeRank 3 K ≤ 2 := by
    rw [← primeRank_equiv 3 e]
    exact (_root_.primeRank_le_of_injective 3 H.subtype H.subtype_injective).trans hrank
  change primeRank 3 (ExchangedNondegenerate.constituentLinearAction ρ C X I hI).range ≤ 2 at hbound
  obtain ⟨E,hE,hcard,α,hα,hno⟩ := actor_obstruction h hn hC hm S hSX hind hI hv hc hf
  rcases models.2 with hs | ⟨hd,q,hq,_,he⟩ | ⟨hd,⟨a⟩⟩
  · by_cases hd : finrank (ZMod 2) I = 4
    · have hm := ChapterG.Section12.symplecticResidual_four_model (B.restrict I)
        (fun w => h.alternating w) hnd hd
      dsimp only at hm
      rw [← hs] at hm
      exact hno (hm.2 E hE (by rw [hcard,hd]; decide) α hα)
    · obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
        (fun w => h.alternating w) hnd
      let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
      have hd' := hI.isIrrPlus.finrank_gt_two ρ H
      have hr := (ChapterG.Section12.symplecticResidual_center_and_threeRank
        (B.restrict I) (fun w => h.alternating w) hnd (by omega)).2
      change primeRank 3 (ExchangedNondegenerate.constituentLinearAction ρ C X I hI).range ≤ 2 at hbound
      rw [hs] at hbound
      omega
  · have hqn : q.polarBilin.Nondegenerate := hq.symm ▸ hnd
    by_cases hd6 : finrank (ZMod 2) I = 6
    · have ho := QuadraticForm.BinarySixResidual.orthogonal_six q hqn hd6
      change center (ChapterG.Section12.embeddedResidual q.isometrySubgroup) = ⊥ ∧
        (ImageAutomorphismsLinear (ChapterG.Section12.embeddedResidual q.isometrySubgroup) ∨
          3 ≤ primeRank 3 (ChapterG.Section12.embeddedResidual q.isometrySubgroup)) at ho
      rw [← he] at ho
      rcases ho.2 with ha | hr
      · exact hno (ha α)
      · omega
    · obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
        (fun w => h.alternating w) hnd
      have hr := QuadraticForm.BinaryHigherCoordinates.residual_rank_ge_three q hqn (by change 8 ≤ finrank (ZMod 2) I; omega)
      change 3 ≤ primeRank 3 (ChapterG.Section12.embeddedResidual q.isometrySubgroup) at hr
      rw [← he] at hr
      omega
  · have hb : primeRank 2 (MulAut K) ≤ 2 := by
      rw [primeRank_equiv 2 (MulAut.congr a)]
      exact Theory.SpecificGroups.Alternating.FiveExtensionAction.automorphism_primeRank_two_le
    have hec := (primeRank_le_iff_elementary_card_le _).mp hb E hE
    rw [hcard,hd] at hec
    norm_num at hec

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedKernel
