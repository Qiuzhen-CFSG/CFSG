module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter10.SourceFullModuleFusion
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations
public import CFSG.Quasithin.Chapter8.Section03
public import Theory.Representation.BinaryOffender.SylowTransport

/-!
# Core fusion for the quiet full module

When J(T) centralizes the original full module V, the two-core of N_G(U)
lies in M for every U ≤ V. If V itself lies in that two-core, fusion in
V replaces any conjugator through U by one in N_G(U). The resulting pair
of conjugate modules normalizes each other. Either zero weak-closure
centralization or non-FF action then forces the pair to commute.

The non-FF hypothesis is on the literal image Aut_{L₀T}(V). Its image
contains a Sylow subgroup of Aut_G(V), so Sylow conjugacy transfers any
ambient offender into the local actor while preserving its fixed codimension.
This proves the full-module cases of both alternatives in 3.2.10(6), without
strengthening the source's local non-FF assumption to an ambient assumption.

The application discharges the two FSU fusion inputs of 8.3.13 and the
fusion input of 8.3.14 on the actual S = O₂(XT). The tensor-model non-FF
proof, point-centralizer core inclusion, hyperplane geometry and r > 3
remain source obligations; these results do not assert tensor exclusion.
Their discharge and quiet fixed support remain with the selected-module
assembly, and final point-control assembly remains with its original owner.

Source: Aschbacher--Smith, 3.2.10(6,8) and 8.3.13--14,
printed pp.583--584,727.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))

include D hJ in
/-- The two-core of the normalizer of any subgroup of the quiet full module lies in M. -/
theorem quiet_subgroup_normalizer_core_le {U : Subgroup G} (hUV : U ≤ D.fullModule) :
    (normalizer (U : Set G)).pCoreIn 2 ≤ D.maximalLocal := by
  let N := normalizer (U : Set G)
  let P := N.pCoreIn 2
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hJN : J ≤ N := hJ.trans ((centralizer_le hUV).trans (Subgroup.centralizer_le_normalizer _))
  have hNP : N ≤ normalizer (P : Set G) := by
    simpa only [P, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 N).le_normalizer_map N.subtype
  have hJp : IsPGroup 2 J := T.isPGroup'.to_le (sSup_le fun _ h => h.1)
  have hPp : IsPGroup 2 (P ⊔ J : Subgroup G) :=
    (isPGroup_pCoreIn 2 N).to_sup_of_normal_left' hJp (hJN.trans hNP)
  exact le_sup_left.trans ((P ⊔ J).le_normalizer.trans
    (source_two_overgroup_normalizer_le_of_centralizes D hJ (P ⊔ J) hPp le_sup_right).2)

local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

include D in
/-- The actual L₀T automizer contains a Sylow of the full automizer, so its non-FF action excludes ambient offenders. -/
theorem fullModule_automizer_notFF_of_localJoin
    (hnf : ¬ IsFFModule ((automizerRepresentation D.fullModule).comp
      (inducedAutomizer D.fullModule (localJoin T L)).subtype)) :
    ¬ IsFFModule (automizerRepresentation D.fullModule) := by
  let V := D.fullModule
  let N := normalizer (V : Set G)
  let A := inducedAutomizer V (localJoin T L)
  let ρ := automizerRepresentation V
  have hTN : (T : Subgroup G) ≤ N :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  let S := (T.subtype hTN).mapSurjective
    (MonoidHom.rangeRestrict_surjective V.normalizerMonoidHom)
  have hSA : (S : Subgroup (Automizer V)) ≤ A.subtype.range := by
    rw [range_subtype]
    exact map_mono (show (T : Subgroup G).subgroupOf N ≤
      (localJoin T L).subgroupOf N from subgroupOf_mono N le_sup_right)
  rintro ⟨B,hB⟩
  obtain ⟨C,hC,hr,hc⟩ := elementary_geometry_of_sylow_range (ρ.comp A.subtype) ρ
    A.subtype A.subtype_injective (LinearEquiv.refl (ZMod 2) (Additive V))
    (fun _ _ => rfl) S hSA B hB.1
  exact hnf ⟨C,hC,by rw [hc,hr]; exact hB.2⟩

include D hJ in
private theorem quiet_core_conjugate_mutual_normalization
    {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hcore : D.fullModule ≤ (normalizer (U : Set G)).pCoreIn 2)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    D.fullModule.map (MulAut.conj g).toMonoidHom ≤ normalizer (D.fullModule : Set G) ∧
      D.fullModule ≤ normalizer (D.fullModule.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨c,hc,he⟩ := source_fullModule_conjugate_through D hJ hUV g hg
  rw [← he]
  let N := normalizer (U : Set G)
  let P := N.pCoreIn 2
  have hNP : N ≤ normalizer (P : Set G) := by
    simpa only [P, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 N).le_normalizer_map N.subtype
  have hPc : P.map (MulAut.conj c).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (hNP hc)
  have hPN : P ≤ normalizer (D.fullModule : Set G) :=
    (quiet_subgroup_normalizer_core_le D hJ hUV).trans D.maximalLocal_normalizes_fullModule
  have hW : D.fullModule.map (MulAut.conj c).toMonoidHom ≤ P :=
    (map_mono hcore).trans_eq hPc
  have hreverse : D.fullModule ≤ normalizer
      (D.fullModule.map (MulAut.conj c).toMonoidHom : Set G) := by
    have hm := map_mono (f := (MulAut.conj c).toMonoidHom) hPN
    rw [hPc,map_equiv_normalizer_eq] at hm
    exact hcore.trans hm
  exact ⟨hW.trans hPN,hreverse⟩

include D hJ in
/-- The full-module case of 3.2.10(6b), retaining non-FF for the literal Aut_{L₀T}(V). -/
theorem quiet_core_conjugate_commutator_eq_bot
    (hnf : ¬ IsFFModule ((automizerRepresentation D.fullModule).comp
      (inducedAutomizer D.fullModule (localJoin T L)).subtype))
    {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hcore : D.fullModule ≤ (normalizer (U : Set G)).pCoreIn 2)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨hWV,hVW⟩ := quiet_core_conjugate_mutual_normalization D hJ hUV hcore g hg
  by_contra hcomm
  exact lemma_E_3_11 D.fullModule g (fullModule_automizer_notFF_of_localJoin D hnf)
    hWV hcomm hVW

include D hJ in
/-- The full-module case of 3.2.10(6a), with the original zero-index weak closure. -/
theorem quiet_core_conjugate_commutator_eq_bot_of_weakClosure_zero
    (hzero : indexedWeakClosure D.fullModule (T : Subgroup G) 0 ≤
      centralizer (D.fullModule : Set G))
    {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hcore : D.fullModule ≤ (normalizer (U : Set G)).pCoreIn 2)
    (g : G) (hg : U ≤ D.fullModule.map (MulAut.conj g).toMonoidHom) :
    ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hTN : (T : Subgroup G) ≤ normalizer (D.fullModule : Set G) :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  have hnorm := (quiet_core_conjugate_mutual_normalization D hJ hUV hcore g hg).1
  have hcomm := (conjugate_normalization_equivalences_of_weakClosure_zero hTN hzero g).1.mp hnorm
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hcomm)

include D hJ in
/-- The intersection-fusion deduction of 8.3.13 with both FSU fusion premises discharged. The original point-core inclusion remains explicit. -/
theorem quiet_tensor_intersection_fusion
    (hnf : ¬ IsFFModule ((automizerRepresentation D.fullModule).comp
      (inducedAutomizer D.fullModule (localJoin T L)).subtype))
    {z : G} (hz : orderOf z = 2) (hzV : z ∈ D.fullModule)
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (g x : G) (hxV : x ∈ D.fullModule)
    (hxg : x ∈ D.fullModule.map (MulAut.conj g).toMonoidHom) (hxz : IsConj x z) :
    D.fullModule.map (MulAut.conj g).toMonoidHom ≤ centralizer (D.fullModule : Set G) := by
  let d : Chapter8.Section03.CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  apply Chapter8.Section03.lemma_8_3_13_of_core_and_FSU_fusion d D.fullModule hz hzV hcore
    ?_ (fun U hUV hU g hg => quiet_core_conjugate_commutator_eq_bot D hJ hnf hUV hU g hg)
    g x hxV hxg hxz
  intro x hx hxz
  obtain ⟨m,hm,he⟩ := source_fullModule_element_fusion D hJ hx hzV hxz
  exact ⟨m,D.maximalLocal_normalizes_fullModule hm,he⟩

include D hJ in
/-- Apply the proved FSU fusion to 8.3.14, retaining its numerical and tensor-hyperplane hypotheses. -/
theorem quiet_tensor_weakClosure_two
    (hnf : ¬ IsFFModule ((automizerRepresentation D.fullModule).comp
      (inducedAutomizer D.fullModule (localJoin T L)).subtype))
    {z : G} (hz : orderOf z = 2) (hzV : z ∈ D.fullModule)
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    {S : Subgroup G} (hSN : S ≤ normalizer (D.fullModule : Set G))
    (hr : (3 : ℕ∞) < globalR D.fullModule)
    (hgeometry : ∀ A ∈ gamma D.fullModule S 2, ¬ A ≤ centralizer (D.fullModule : Set G) →
      Chapter8.Section03.HasFusedHyperplane D.fullModule A z) :
    indexedWeakClosure D.fullModule S 2 ≤ centralizer (D.fullModule : Set G) :=
  Chapter8.Section03.lemma_8_3_14_of_hyperplane_geometry hSN hr hgeometry
    (quiet_tensor_intersection_fusion D hJ hnf hz hzV hcore)

include D hJ in
/-- The actual 8.3.14 subgroup S = O₂(XT) normalizes V because it lies in the original Sylow T. No separate normalization premise is needed. -/
theorem quiet_original_tensor_weakClosure_two
    (hnf : ¬ IsFFModule ((automizerRepresentation D.fullModule).comp
      (inducedAutomizer D.fullModule (localJoin T L)).subtype))
    {z : G} (hz : orderOf z = 2) (hzV : z ∈ D.fullModule)
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule)
    (hgeometry : ∀ A ∈ gamma D.fullModule
        (Chapter8.Section03.CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2,
      ¬ A ≤ centralizer (D.fullModule : Set G) →
        Chapter8.Section03.HasFusedHyperplane D.fullModule A z) :
    indexedWeakClosure D.fullModule
      (Chapter8.Section03.CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
        centralizer (D.fullModule : Set G) :=
  quiet_tensor_weakClosure_two D hJ hnf hz hzV hcore
    ((Chapter8.Section03.CentralizerSetup.S_le_T ⟨T,localOrbit T L,z⟩).trans
      ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule))
    hr hgeometry

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
