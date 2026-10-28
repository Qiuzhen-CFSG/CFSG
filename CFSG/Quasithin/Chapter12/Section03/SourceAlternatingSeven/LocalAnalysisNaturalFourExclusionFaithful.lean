module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionCore
public import CFSG.Quasithin.ChapterA.Section04.Modules

/-!
# Faithfulness of the literal central-line residual

The central-line local group has characteristic two. Its normal perfect
residual K_z inherits characteristic two, and its intrinsic two-core lies
in O₂(K_z T). Since that core centralizes the original V and V=[V,K_z],
the whole V lies in the intrinsic signalizer module V(K_z). Thus K_z
belongs to the faithful signalizer family without any quotient assumption.

Relative C-component membership then supplies the remaining local-family
condition. The final application removes both these premises from the
previous residual constructor. Component membership, characteristic-normalizer
control and the PSL₃(2) quotient remain with qt-d-1233-natural-coordinates,
which also owns the final enlargement and block contradiction.

Source: Aschbacher--Smith, Lemma 12.3.3, printed p.808, using 1.1.3(1),
1.1.4(6), 1.2.6 and Definition A.4.7. All cores and normality are relative
to the literal subgroups of the original ambient group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

private theorem perfect_le_pointLocal
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    S.fourPointPerfect z ≤ S.fourPointLocal z := by
  rw [S.four_pointLocal_eq structural hz hz1]
  exact (map_subtype_le _).trans (map_subtype_le _)

private theorem sylow_le_pointLocal' {z : G}
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    (T : Subgroup G) ≤ S.fourPointLocal z := by
  refine le_inf S.chosen.sylow_normalizes_component ?_
  intro t ht
  exact mem_centralizer_singleton_iff.mpr
    (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)

/-- The literal solvable residual is perfect. -/
theorem four_pointPerfect_perfect (z : G) : Group.IsPerfect (S.fourPointPerfect z) := by
  let f := (solvableResidual (S.fourPointResidual z)).equivMapOfInjective
    (S.fourPointResidual z).subtype (S.fourPointResidual z).subtype_injective
  exact Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective

/-- The same residual has no nontrivial two-group quotient. -/
theorem four_pointPerfect_twoPerfect (z : G) : IsPPerfect 2 (S.fourPointPerfect z) := by
  let := S.four_pointPerfect_perfect z
  intro N hn hq
  let := hn
  by_contra hne
  let : Nontrivial ((S.fourPointPerfect z) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect ((S.fourPointPerfect z) ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent ((S.fourPointPerfect z) ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable ((S.fourPointPerfect z) ⧸ N) inferInstance

/-- The central-line local overgroup has characteristic two. -/
theorem four_pointLocal_characteristicTwo
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourPointLocal z ∈ Chapter1.He G := by
  have hTM := S.sylow_le_pointLocal' hzT
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp hzT).2.2 hz1)
  have hzM : zpowers z ≤ S.fourPointLocal z :=
    zpowers_le.mpr (S.four_module_le_pointLocal hz hz)
  have hn : S.fourPointLocal z ≤ normalizer (zpowers z : Set G) := by
    apply (inf_le_right : S.fourPointLocal z ≤ centralizer ({z} : Set G)).trans
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hcore := le_pCoreIn_of_normalizes hp hzM hn
  exact Chapter1.lemma_1_1_4_6 T (S.hypothesis.simpleQTKE.evenCharacteristic T)
    ⟨fun he => hz1 (mem_bot.mp (he ▸ hcore (mem_zpowers z))), hTM⟩

/-- Characteristic two passes to the normal perfect residual. -/
theorem four_pointPerfect_characteristicTwo
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    S.fourPointPerfect z ∈ Chapter1.He G := by
  have hn : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).Normal :=
    normal_subgroupOf_of_le_normalizer (S.four_pointLocal_normalizes_perfect structural hz hz1)
  exact Chapter1.lemma_1_1_3_1 (S.four_pointLocal_characteristicTwo hz hz1 hzT)
    (fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_pointPerfect structural e hd hz hz1).trans he.le)))
    (S.perfect_le_pointLocal structural hz hz1) hn.isSubnormal

/-- The full original module lies in the omega-center of the intrinsic core. -/
theorem four_module_le_perfectCore_omegaCenter
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ omegaCenterIn ((S.fourPointPerfect z).pCoreIn 2) := by
  let := S.chosen.elementary
  have hKN : S.fourPointPerfect z ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans ((map_subtype_le _).trans inf_le_left)
  have hVK : V ≤ S.fourPointPerfect z := S.four_module_le_pointPerfect structural e hd hz hz1
  have hVc : V ≤ (S.fourPointPerfect z).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVK hKN
  have hTJ : (S.fourPointPerfect z ⊔ (T : Subgroup G) : Subgroup G) ≤
      normalizer (S.fourPointPerfect z : Set G) :=
    sup_le (S.fourPointPerfect z).le_normalizer
      ((S.sylow_le_pointLocal' hzT).trans
        (S.four_pointLocal_normalizes_perfect structural hz hz1))
  have hcQ : (S.fourPointPerfect z).pCoreIn 2 ≤ S.fourPointCore z :=
    pCoreIn_mono_of_normalizes le_sup_left hTJ
  have hVcC : V ≤ centralizer ((S.fourPointPerfect z).pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (hcQ.trans (S.four_pointCore_centralizes structural e hd hz hz1 hzT))
  intro v hv
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hVc hv, hVcC hv, elemPow_eq_one_of_isElementaryAbelian v hv⟩

/-- The original module is contained in the actual intrinsic signalizer module. -/
theorem four_module_le_intrinsicSignalizer
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    V ≤ ChapterA.Section04.intrinsicSignalizerModule (S.fourPointPerfect z) := by
  rw [ChapterA.Section04.intrinsicSignalizerModule,
    ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter, commutator_comm]
  exact (S.four_pointPerfect_moved e hd hz hz1).le.trans
    (commutator_mono (S.four_module_le_perfectCore_omegaCenter structural e hd hz hz1 hzT) le_rfl)

/-- Faithful signalizer membership follows from the original four-space. -/
theorem four_pointPerfect_faithful
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G)) :
    ChapterA.Section04.IsFaithfulSignalizerType (S.fourPointPerfect z) := by
  refine ⟨⟨?_, S.four_pointPerfect_twoPerfect z, ?_⟩, ?_⟩
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_pointPerfect structural e hd hz hz1).trans he.le))
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (S.four_pointPerfect_characteristicTwo structural e hd hz hz1 hzT))
  · exact fun he => S.chosen.ne_bot (bot_unique
      ((S.four_module_le_intrinsicSignalizer structural e hd hz hz1 hzT).trans he.le))

/-- Relative component membership supplies the genuine Sylow local family. -/
theorem four_pointPerfect_local_of_component
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (component : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent) :
    S.fourPointPerfect z ∈ Chapter1.L G (T : Subgroup G) := by
  have hTM := S.sylow_le_pointLocal' hzT
  apply Chapter1.mem_L_of_cComponent ?_
    ⟨T.subtype hTM, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]⟩
    (S.perfect_le_pointLocal structural hz hz1) component
  have hV : V ≤ (S.fourPointLocal z).pCoreIn 2 := by
    let := S.chosen.elementary
    apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (S.four_module_le_pointLocal hz)
    rw [S.four_pointLocal_eq structural hz hz1]
    exact inf_le_left
  exact fun he => S.chosen.ne_bot (bot_unique (hV.trans he.le))

/-- Apply faithfulness and local membership to the literal residual constructor. -/
theorem fourResidualData_of_component_control_quotient
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ omegaCenterIn (T : Subgroup G))
    (component : ((S.fourPointPerfect z).subgroupOf (S.fourPointLocal z)).IsCComponent)
    (control : ((S.fourPointCore z).subgroupOf (S.fourPointCentralizer z)).characteristicNormalizerClosure ≤
      (S.fourPointLocal z).subgroupOf (S.fourPointCentralizer z))
    (quotient : ClassicalGroup.IsPSL
      ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2) :
    S.FourResidualData z :=
  S.fourResidualData_of_component_control structural e hd hz hz1 hzT component control
    (S.four_pointPerfect_faithful structural e hd hz hz1 hzT)
    (S.four_pointPerfect_local_of_component structural hz hz1 hzT component) quotient

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
