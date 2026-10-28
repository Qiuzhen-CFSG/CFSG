module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedKernel
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.FieldFour
public import Theory.Representation.BinaryPermutation.PairedPointRank
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Excluding the original nondegenerate exchanged constituent

The original extraspecial square form has a nonzero singular vector in the
selected constituent. A transitive SL2(4) action would make that constituent
isotropic for the square form, forcing the noncentral kernel to vanish.
The actual A5 quotient therefore has the orthogonal four-dimensional action.
Separating complementary quotient actions identify the whole component orbit
and its action with the direct sum of two orthogonal A5 factors. The original
Sylow-fixed point then has cubic rank at least two in its stabilizer, contrary
to the original 12.8.13(8) bound.

Together with the central-kernel exclusion this removes the last nondegenerate
branch. The final theorem constructs the source conjugator and gives the
large-case contradiction with only the authorized exact MixedSizeInput and
the retained earlier-source hypotheses. The latter are still universal
Structural1222, Theorem12213 and Earlier1332CaseOne inputs; this is not their
guarded same-G,T specialization. Final 14.4.14 assembly must discharge those
inputs and the independent mixed-size theorem.

Source: Aschbacher--Smith G.10.15, G.11.2(12), 12.8.13(7)--(8), 14.4.2 and
14.4.14, printed pp.362--366,855--856,1006--1012, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedKernel
local instance fieldFourAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
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

include h hn hC hI hc hk in
private theorem not_transitive_of_singular_quadratic
    (q : QuadraticForm (ZMod 2) U) (hqn : q.polarBilin.Nondegenerate)
    (hq : ∀ a u, q (ρ a u) = q u) (i : I) (hi : i ≠ 0) (hqi : q i = 0) :
    ¬ ∀ u w : I, u ≠ 0 → w ≠ 0 → ∃ a : componentOrbit C ⊤,
      (invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant).toRepresentation a u = w := by
  intro ht
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hz (u : I) : q u = 0 := by
    by_cases hu : u = 0
    · simp only [hu,Submodule.coe_zero,map_zero]
    · obtain ⟨a,ha⟩ := ht i u hi hu
      exact (congrArg (fun z : I => q z) ha).symm.trans ((hq a i).trans hqi)
  have hiso : ∀ u ∈ I, ∀ w ∈ I, q.polarBilin u w = 0 := by
    intro u hu w hw
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      hz ⟨u+w,I.add_mem hu hw⟩,hz ⟨u,hu⟩,hz ⟨w,hw⟩,sub_zero]
  have hpres : ∀ a u w, q.polarBilin (ρ a u) (ρ a w) = q.polarBilin u w := by
    intro a u w
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,← map_add]
    rw [hq,hq,hq]
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  have hxinv (x : X) : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : D) x.property)
  have hpair (x : X) (hx : I.map (ρ (x : D)⁻¹) ≠ I) : I ⊔ I.map (ρ (x : D)⁻¹) = ⊤ := by
    rw [hxinv] at hx ⊢
    exact (h.independent_orbit_pair I (hI.isIrrPlus.finrank_gt_two ρ H)
      (hI.independent_orbit_of_fixedSpace_eq_bot ρ hfix) x hx).1.symm.trans hc.2.1
  obtain ⟨x,hx,_,_⟩ := hc.2.2.1
  obtain ⟨hf,_,_⟩ := hI.faithful_dual_of_isotropic_pair ρ h.faithful q.polarBilin hqn hpres
    hfix (hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H)
    hiso ⟨x,by rwa [hxinv]⟩ hpair
  apply hk
  rw [(MonoidHom.ker_eq_bot_iff _).mpr hf]
  exact bot_le

include h hn hC hm S hSX hind hI hv hk hc hnd in
/-- The actual square form excludes the transitive A5 constituent. The resulting
coordinates retain the full original H-action on both exchanged summands. -/
theorem paired_orthogonal_coordinates
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (q : QuadraticForm (ZMod 2) U) (hqn : q.polarBilin.Nondegenerate)
    (hq : ∀ a u, q (ρ a u) = q u) (i : I) (hi : i ≠ 0) (hqi : q i = 0) :
    ∃ e : componentOrbit C ⊤ ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)),
      ∃ c : U ≃ₗ[ZMod 2] (BinaryPermutation.natural (Fin 5) × BinaryPermutation.natural (Fin 5)),
        ∀ (a : componentOrbit C ⊤) u, c (ρ a u) =
          (BinaryPermutation.naturalRepresentation (Fin 5) (e a).1.val (c u).1,
           BinaryPermutation.naturalRepresentation (Fin 5) (e a).2.val (c u).2) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let R := invariantSubspace ρ H I hI.invariant
  obtain ⟨_,p,hp,hker⟩ := noncentral_five_quotient h hn hC hm S hSX hind hI hv hk hc hnd cover
  have hkp : p.ker ≤ R.toRepresentation.asGroupHom.ker := by
    intro a ha
    exact Units.ext ((hker a).mp (MonoidHom.mem_ker.mp ha))
  let τ : Representation (ZMod 2) (alternatingGroup (Fin 5)) I :=
    (Units.coeHom _).comp (p.liftOfSurjective hp ⟨R.toRepresentation.asGroupHom,hkp⟩)
  have hτ (a : H) : τ (p a) = R.toRepresentation a := by
    change Units.coeHom (Module.End (ZMod 2) I)
      ((p.liftOfSurjective hp ⟨R.toRepresentation.asGroupHom,hkp⟩) (p a)) = _
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    exact Representation.asGroupHom_apply _ _
  have hρ : τ.comp p = R.toRepresentation := MonoidHom.ext hτ
  let : IsIrreducible τ := (irreducible_comp_surjective_iff p hp τ).mp
    (hρ.symm ▸ hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H)
  have hτn : ∃ a, τ a ≠ 1 := by
    by_contra! hall
    have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
      (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
    apply hI.isIrrPlus.ne_bot ρ
    apply bot_unique
    rw [← hfix]
    intro u hu a
    have ha : R.toRepresentation a = 1 := (hτ a).symm.trans (hall (p a))
    exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩ : U)) ha
  have htn := not_transitive_of_singular_quadratic h hn hC hI hk hc q hqn hq i hi hqi
  obtain ⟨_,hm⟩ := ChapterG.Section09.DefiningCharacteristic.alternating_five_irreducible_action_alternatives
    τ (MulEquiv.refl _) hτn
  have horth : ∃ a : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5),
      Nonempty (Representation.Equiv τ
        (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp a.toMonoidHom)) := by
    rcases hm with ⟨a,⟨c⟩⟩ | he
    · apply False.elim
      apply htn
      intro u w hu hw
      have hcu : c u ≠ 0 := fun he => hu (c.toLinearEquiv.map_eq_zero_iff.mp he)
      have hcw : c w ≠ 0 := fun he => hw (c.toLinearEquiv.map_eq_zero_iff.mp he)
      obtain ⟨b,hb⟩ := Matrix.SL2.exists_mulVec_eq
        (Representation.OrthogonalFourMinus.FiniteModel.Field 1) (c u) (c w) hcu hcw
      obtain ⟨z,hz⟩ := hp (a.symm b)
      refine ⟨z,c.injective ?_⟩
      rw [← hτ z,hz]
      have he := Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap (a.symm b) u
      change c (τ (a.symm b) u) = Representation.SL2.BinarySmall.natural (a (a.symm b)) (c u) at he
      rw [a.apply_symm_apply] at he
      exact he.trans hb
    · exact he
  obtain ⟨a,⟨c⟩⟩ := horth
  let f := a.toMonoidHom.comp p
  have hfk : f.ker ≠ ⊥ := by
    intro hz
    apply hk
    intro z hzR
    have he : p z = 1 := (hker z).mpr (congrArg Units.val (MonoidHom.mem_ker.mp hzR))
    have hz1 : z = 1 := mem_bot.mp (hz ▸ (show z ∈ f.ker from by
      change a (p z) = 1
      rw [he,map_one]))
    rw [hz1]
    exact one_mem _
  obtain ⟨x,_,hcompl,_⟩ := hc.2.2.1
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  apply Representation.simple_pair_coordinates ρ h.faithful H R
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) f
    (a.surjective.comp hp) hfk c.toLinearEquiv _ x hcompl.disjoint hcompl.sup_eq_top
  intro z u
  rw [← hτ z]
  exact Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap (p z) u

include h hn hC hm S hSX hind hI hv hc hnd in
/-- Both constituent-kernel cases are excluded using the original square form
and the marked Sylow-fixed point, without a faithfulness assumption on I. -/
theorem nondegenerate_impossible
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (models : ExchangedNondegenerate.RecognizedData ρ B C X I hI)
    (hrank : primeRank 3 D ≤ 2)
    (hpoint : primeRank 3 (ChapterG.Section10.pointCentralizer ρ v) ≤ 1)
    (hfix : ∀ a ∈ S, ρ a v = v)
    (q : QuadraticForm (ZMod 2) U) (hqn : q.polarBilin.Nondegenerate)
    (hq : ∀ a u, q (ρ a u) = q u) (i : I) (hi : i ≠ 0) (hqi : q i = 0) : False := by
  have hk := not_central_kernel h hn hC hm S hSX hind hI hv hc hnd hrank models
  obtain ⟨e,c,hact⟩ := paired_orthogonal_coordinates h hn hC hm S hSX hind hI hv hk hc hnd
    cover q hqn hq i hi hqi
  let : (componentOrbit C ⊤).Normal := componentOrbit_top_normal C
  have hr := Representation.BinaryPermutationPair.two_le_point_rank ρ (componentOrbit C ⊤)
    e c hact S v hfix (ChapterG.Section10.pointCentralizer ρ v) (fun _ => Iff.rfl)
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedKernel


namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The nondegenerate exchanged constituent of the original rank-three flag
is impossible. Both kernel cases, the literal square form and the original
point-centralizer rank bound are discharged here. -/
theorem source_exchanged_nondegenerate_impossible (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) (hnd : (B.restrict I).Nondegenerate) : False := by
  let := chosen.elementary
  obtain ⟨P,hfix,hXP,hN⟩ := hS
  have hSX := (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  have hc := source_exchanged_completion d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  have models := (source_exchanged_nondegenerate_recognition d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv hnd).1
  have hker := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  have htwo : IsPGroup 2 F.terminalHatAction.ker := hker ▸ pCore_isPGroup
  have hrank : primeRank 3 F.TerminalHdot ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ htwo).trans
      ((Chapter14.Section03.NonabelianSource.Recognition.pointNormalizer_sqtk
        d.qtke F (by decide)).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hpoint : primeRank 3 (ChapterG.Section10.pointCentralizer F.terminalRepresentation v) ≤ 1 := by
    let J := F.terminalDot (centralizer (F.ZU : Set G))
    let Z := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
    have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
      rw [hZ]
      exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
    have hJ : J = ⊤ := by
      apply top_unique
      intro a _
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
      exact mem_map_of_mem _ (hHc b.property)
    have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one
      d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
    change primeRank 3 (Z.subgroupOf J) ≤ 1 at hu
    have hZJ : Z ≤ J := by rw [hJ]; exact le_top
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hZJ)] at hu
    exact hu
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  let q := Chapter14.Section03.NonabelianSource.Recognition.centerPointQuadraticForm F c (by decide) hZ
  have hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU := disjoint_iff.mpr
    (F.parabolic_displaced_centers (by decide) L chosen.normalizes c.seed_center g hgP hgH).1
  obtain ⟨hs,hi,hqn⟩ := Chapter14.Section03.NonabelianSource.Recognition.quadratic_intersection_of_center_point
    F c (by decide) hZ g hdis
  have hqpres : ∀ a u, q (F.terminalRepresentation a u) = q u := by
    intro a u
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hi a u.toMul
  obtain ⟨x,_,_,_,_,i,hi0,_,hiW,_⟩ := hyp.exchanged_constituent_geometry
    hns hC hm P hSX hind hI hv
  have hqi : q (⟨i,i.property.1⟩ : I) = 0 := by
    apply hs
    have hh : (i : Additive F.Uhat) ∈ I ⊓ hatSpace F (F.E g) := by
      rw [hiW]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact hh.2
  exact ExchangedKernel.nondegenerate_impossible hyp hns hC hm P hSX hind hI hv hc hnd
    (source_terminal_cover F d chosen) models hrank hpoint hfix q hqn hqpres
    ⟨i,i.property.1⟩ (fun hz => hi0 (congrArg Subtype.val hz)) hqi

/-- Conditional large-case source contradiction. The only mixed-tensor input is
the authorized exact MixedSizeInput; every exchanged recognition and kernel
premise is discharged on the original flag. Earlier-source premises are retained. -/
theorem source_large_impossible_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : False := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hnd,models,hz,hzH⟩ :=
    FixedLineReduction.source_large_recognized_nondegenerate_remainder_of_mixed_size
      d earlier hq chosen structural alternatives classification size F hne hZ hlarge g hg hgP hgH
  let := heU
  let := heX
  exact source_exchanged_nondegenerate_impossible d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hS hn hC hm hI hv hnd

/-- The source conjugator is constructed, so the conditional large exclusion
has no extra group element or local recognition premise. -/
theorem source_large_exclusion_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U) : False := by
  obtain ⟨g,hg,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  exact source_large_impossible_of_mixed_size d earlier hq chosen structural alternatives
    classification size F hne hZ hlarge g hg hgP hgH

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
