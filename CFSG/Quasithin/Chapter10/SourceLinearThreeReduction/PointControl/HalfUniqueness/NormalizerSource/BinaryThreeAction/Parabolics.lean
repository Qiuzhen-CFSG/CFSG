module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Stabilizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPairCore
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Normalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Wreath.Source
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Theory.GroupTheory.SubgroupCoverTransport

/-!
# The two source parabolics and their actual normalizer enlargements

The selected zero-kernel natural action gives two distinct maximal parabolics
above the original Sylow T in L₀T. Their embedded TWO-residuals generate L₀.
Each residual lies in Xi, and source 3.1.1 gives a nontrivial two-core in the
literal enlargement <N_G(N_T(L)),H_i>. The intrinsic 10.2.4 classification then
applies to its actual normal closure, retaining the adequate Held alternative.

These constructions precede point-centralizer control. The remaining model
argument must show N_G(N_T(L)) normalizes both residuals. Its discharge and
final assembly remain with qt-d-10-nona5-half-sylow-unique; ModuleChoiceAt is
produced independently by qt-d-10-nona5-point-selection.
Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02
namespace Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- A literal maximal parabolic above the original Sylow, with its own
intrinsic two-core quotient. -/
structure Data (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (H : Subgroup G) : Prop where
  sylow_le : (T : Subgroup G) ≤ H
  le_join : H ≤ localJoin T L
  maximal : IsCoatom (H.subgroupOf (localJoin T L))
  quotient : Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor)
  core_le_stabilizer : H.pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (L : Set G)

variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

/-- Both actual parabolics exist under the original zero-kernel branch. -/
theorem exists_pair
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ∃ H₁ H₂ : Subgroup G, Data D H₁ ∧ Data D H₂ ∧ H₁ ≠ H₂ ∧
      H₁ ⊔ H₂ = localJoin T L := by
  obtain ⟨s,_,f,hf,hk,_,_⟩ := exists_wreath_action D hmodel hzero hfull ht htn hcross
  let J := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  obtain ⟨A,B,hSA,hSB,hA,hB,hne,hgen,⟨eA⟩,⟨eB⟩,hcA,hcB⟩ :=
    Matrix.PSL3Two.WreathPair.exists_parabolics_with_core f.hom hf hk S
  have hS : (S : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have core_bound (U : Subgroup J) (hSU : (S : Subgroup J) ≤ U)
      (hc : ∀ a ∈ U.pCoreIn 2, (f.hom a).right = 1) :
      (U.map J.subtype).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) := by
    rw [← map_pCoreIn_of_injective 2 U J.subtype J.subtype_injective]
    rintro _ ⟨a,ha,rfl⟩
    have hs : U.pCoreIn 2 ≤ (S : Subgroup J) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSU] using
        pCoreIn_le_sylow U (S.subtype hSU)
    have hat : (a : G) ∈ (T : Subgroup G) := hS ▸ mem_map_of_mem J.subtype (hs ha)
    exact ⟨hat,f.normalizes_of_right_eq_one hat (hc a ha)⟩
  have ha : (A.map J.subtype).subgroupOf J = A := by
    exact Subgroup.comap_map_eq_self_of_injective (f := J.subtype) J.subtype_injective A
  have hb : (B.map J.subtype).subgroupOf J = B := by
    exact Subgroup.comap_map_eq_self_of_injective (f := J.subtype) J.subtype_injective B
  let a := A.equivMapOfInjective J.subtype J.subtype_injective
  let b := B.equivMapOfInjective J.subtype J.subtype_injective
  refine ⟨A.map J.subtype,B.map J.subtype,
    ⟨hS ▸ map_mono hSA,map_subtype_le _,by change IsCoatom ((A.map J.subtype).subgroupOf J); rwa [ha],
      ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eA⟩,
      core_bound A hSA hcA⟩,
    ⟨hS ▸ map_mono hSB,map_subtype_le _,by change IsCoatom ((B.map J.subtype).subgroupOf J); rwa [hb],
      ⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB⟩,
      core_bound B hSB hcB⟩,
    fun he => hne (map_injective J.subtype_injective he),?_⟩
  rw [← Subgroup.map_sup,hgen,← MonoidHom.range_eq_map,range_subtype]

/-- Every such parabolic has a nontrivial actual two-core, since it contains
and normalizes the original two-core of L₀T. -/
theorem Data.mem_H (h : Data D H) : H ∈ Chapter1.H G := by
  have hn : H ≤ normalizer ((localJoin T L).pCoreIn 2 : Set G) :=
    h.le_join.trans ((localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (localJoin T L))))
  have hc : (localJoin T L).pCoreIn 2 ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      ((join_core_le_stabilizer D).trans (inf_le_left.trans h.sylow_le)) hn
  exact fun he => D.module_ne_bot (bot_unique (D.module_le_core.trans (hc.trans_eq he)))

/-- T is itself maximal in H, not just a maximal two-subgroup of H. -/
theorem Data.sylow_maximal (h : Data D H) : (T : Subgroup G) ⋖ H := by
  obtain ⟨e⟩ := h.quotient
  have hm := WreathTwoResidual.sylow_isCoatom_of_core_quotient (T.subtype h.sylow_le) e
  have hc := (covBy_map_subtype_iff H _ _).mpr hm.covBy_top
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,
    ← MonoidHom.range_eq_map,range_subtype] using hc

/-- Exact minimal-parabolic premise of the common-normal theorem. -/
theorem Data.uniqueMaximal (h : Data D H) : Order.HasUniqueMaximalOver (T : Subgroup G) H := by
  have hc := h.sylow_maximal
  refine ⟨hc.lt,(T : Subgroup G),⟨le_rfl,hc⟩,?_⟩
  intro U hU
  exact (hc.eq_or_eq hU.1 hU.2.le).resolve_right hU.2.ne

/-- The embedded residual of an actual source parabolic. -/
def residual (H : Subgroup G) : Subgroup G := (pResidual 2 H).map H.subtype

/-- Both source residuals generate precisely L₀. -/
theorem residuals_generate {H₁ H₂ : Subgroup G} (h₁ : Data D H₁) (h₂ : Data D H₂)
    (hgen : H₁ ⊔ H₂ = localJoin T L) :
    residual H₁ ⊔ residual H₂ = localOrbit T L := by
  let J := localJoin T L
  let A := H₁.subgroupOf J
  let B := H₂.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hSA : (S : Subgroup J) ≤ A := subgroupOf_mono J h₁.sylow_le
  have hSB : (S : Subgroup J) ≤ B := subgroupOf_mono J h₂.sylow_le
  have hAB : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup h₁.le_join h₂.le_join,hgen,subgroupOf_self]
  have hr := pResidual_eq_sup_of_finite_sylow_pair A B (S : Subgroup J)
    (S.subtype hSA) (S.subtype hSB)
    (map_subgroupOf_eq_of_le hSA) (map_subgroupOf_eq_of_le hSB) hAB
  have he := congrArg (Subgroup.map J.subtype) hr
  rw [Subgroup.map_sup,Subgroup.map_map,Subgroup.map_map] at he
  have ha : ((pResidual 2 A).map A.subtype).map J.subtype = residual H₁ := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le h₁.le_join]
    rfl
  have hb : ((pResidual 2 B).map B.subtype).map J.subtype = residual H₂ := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le h₂.le_join]
    rfl
  rw [Subgroup.map_map] at ha hb
  rw [ha,hb,source_join_residual D] at he
  exact he.symm

/-- The two-residual lies in the original orbit. -/
theorem Data.residual_le_orbit (h : Data D H) : residual H ≤ localOrbit T L :=
  (embedded_pResidual_mono 2 h.le_join).trans_eq (source_join_residual D)

/-- It is supplemented by the original full Sylow. -/
theorem Data.residual_sup_sylow (h : Data D H) : residual H ⊔ (T : Subgroup G) = H :=
  embedded_pResidual_sup_of_common_sylow H (T : Subgroup G) (T.subtype h.sylow_le)
    (map_subgroupOf_eq_of_le h.sylow_le)

/-- The wreath-residual theorem applies to the actual embedded O²(H). -/
theorem Data.xi (h : Data D H) :
    residual H ∈ Chapter1.Xi G (T : Subgroup G) ∧
    Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient (residual H)) := by
  obtain ⟨e⟩ := h.quotient
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let w := RegularWreathProduct.congr eSL (MulEquiv.refl (Multiplicative (ZMod 2)))
  exact SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.wreathResidualAt T
    H h.sylow_le h.mem_H ⟨e.trans w⟩

/-- T normalizes its original index-two stabilizer. -/
theorem stabilizer_normalized (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) := by
  have he : (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf (T : Subgroup G)) =
      (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
    ext x
    exact and_iff_right x.property
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
  rw [he]
  exact normal_of_index_eq_two
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)

/-- Source 3.1.1 gives O₂(G_i) ≠ 1 for G_i=<N_G(T₁),H_i>.
The common-normal subgroup and the residual-Sylow premise are constructed. -/
theorem Data.enlargement_mem_H (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ⊔ H ∈ Chapter1.H G := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let N := normalizer (R : Set G)
  have hR : R ≠ ⊥ := fun he => D.module_ne_bot
    (bot_unique ((D.module_le_core.trans (join_core_le_stabilizer D)).trans_eq he))
  have hp : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  have hN : N ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨R,hR,hp,rfl⟩,stabilizer_normalized D hn⟩
  have hTO : (T : Subgroup G) ⊓ localOrbit T L ≤ R :=
    inf_le_inf_left _ (source_nonnormal_orbit_le_normalizer D hn)
  have hs : Chapter1.IsSylowIn 2 R (residual H ⊔ R) :=
    (source_orbit_sylow_of_intersection_le R inf_le_left hTO).restrict le_sup_right
      (sup_le_sup_right h.residual_le_orbit R)
  obtain ⟨Q,hQR,hQ,hQN⟩ := Chapter3.source_common_normal_knownSimple
    D.simpleQTKE T N H R hN ⟨h.mem_H,h.sylow_le⟩ h.uniqueMaximal hR inf_le_left hs le_rfl
  have hnorm := Chapter3.normalIn_iff_le_normalizer.mp hQN
  rw [Chapter3.generated_eq_sup] at hnorm
  have hc := le_pCoreIn_of_normalizes (hp.to_le hQR) hnorm.1 hnorm.2
  exact fun he => hQ (bot_unique (hc.trans_eq he))

/-- The source normal-closure classification on the literal enlargement.
No recognition or local-input premise is left, and Held is retained. -/
theorem Data.normalClosure_models (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let E := normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ⊔ H
    conjugateSpanBy (residual H) E = residual H ∨ ∃ I : Subgroup G,
      I ∈ Chapter1.cComponentsIn E ∧ IsQuasisimple (Chapter1.XiQuotient I) ∧
      conjugateSpanBy (residual H) E = componentOrbit I (T : Subgroup G) ∧
      SourceLinearThreeReplacement.Overgroups.ClosureModel T I := by
  let E := normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ⊔ H
  let P : Sylow 3 (residual H) := Classical.arbitrary _
  have hXT : residual H ⊔ (T : Subgroup G) ≤ E := by
    rw [h.residual_sup_sylow]
    exact le_sup_right
  have hTE : (T : Subgroup G) ≤ E := h.sylow_le.trans le_sup_right
  have hi := Chapter1.XiEmbedding.localInput_of_mem_Xi h.xi.1
    (SourceLinearThreeReplacement.Overgroups.Closure.sylowIn_overgroup hTE)
    hXT (by decide : Odd 3) h.xi.2 P
  obtain ⟨e⟩ := h.quotient
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let w := RegularWreathProduct.congr eSL (MulEquiv.refl (Multiplicative (ZMod 2)))
  have hw : Nonempty (((residual H ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (residual H ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      SourceLinearThreeReplacement.Overgroups.Closure.ParabolicWreath) := by
    rw [h.residual_sup_sylow]
    exact ⟨e.trans w⟩
  exact SourceLinearThreeReplacement.Overgroups.Closure.normalClosure_models hi
    (Chapter1.RadicalExclusions.sqtk_of_mem_H D.simpleQTKE (h.enlargement_mem_H hn)) hw

/-- The final normalizer step uses the two literal residuals, whose generation
has been proved, and the original normalizer of L₀. -/
theorem normalizer_le_of_normalizes_pair {H₁ H₂ : Subgroup G}
    (h₁ : Data D H₁) (h₂ : Data D H₂) (hgen : H₁ ⊔ H₂ = localJoin T L)
    (hN₁ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H₁ : Set G))
    (hN₂ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H₂ : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal := by
  have h := (le_inf hN₁ hN₂).trans
    (normalizer_inf_normalizer_le_normalizer_sup (residual H₁) (residual H₂))
  rw [residuals_generate h₁ h₂ hgen] at h
  exact h

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
