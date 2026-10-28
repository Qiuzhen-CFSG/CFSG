module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallProductDegree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCoreElementary
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallQuadraticAction
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# The literal two-layer remainder after the nontrivial image exclusion

When the original module has trivial image on `Q / Φ(Q)`, its commutator with
the literal core lies in the literal Frattini subgroup. The source elementary
core argument places that Frattini subgroup in `Q ∩ O₂(L₀T)`. This is the
exact surviving branch and keeps the possible module supplement outside `K`.
The original action kernel also implies `[V,K] ≤ Q`, and the literal join
has `O₂(KV) = QV`. No placement of the whole module in `K`, and no full
normalization, is used. Source: Aschbacher--Smith 10.2.5, printed p.748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- In the literal trivial-image branch, the original module commutator is
confined to the common Frattini kernel of the containing core. -/
theorem Data.trivial_image_two_layer
    (h : Data D H) (f : LiftData s hz)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (ha : moduleFrattiniImage D H = ⊥) :
    ⁅D.fullModule,(enlargedResidual T L H).pCoreIn 2⁆ ≤
        (frattini ((enlargedResidual T L H).pCoreIn 2)).map
          ((enlargedResidual T L H).pCoreIn 2).subtype ∧
      (frattini ((enlargedResidual T L H).pCoreIn 2)).map
          ((enlargedResidual T L H).pCoreIn 2).subtype ≤
        (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 := by
  refine ⟨(h.moduleFrattiniImage_eq_bot_iff hfull).mp ha,?_⟩
  exact h.core_frattini_le_common_kernel f hi hP

/-- The original module fixes the whole Frattini subgroup pointwise, as that
subgroup lies in the original join-action kernel. -/
theorem Data.fullModule_centralizes_core_frattini
    (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    D.fullModule ≤ centralizer
      ((frattini ((enlargedResidual T L H).pCoreIn 2)).map
        ((enlargedResidual T L H).pCoreIn 2).subtype : Set G) := by
  apply le_centralizer_iff.mp
  apply (h.core_frattini_le_common_kernel f hi hP).trans
  apply inf_le_right.trans
  rintro _ ⟨q,hq,rfl⟩
  rw [←f.kernel_eq_join_core,f.kernel_eq_action_kernel,joinAction_ker] at hq
  exact hq

/-- Triviality on the original Frattini section forces the original module
to centralize the containing quotient, without requiring module placement. -/
theorem Data.module_commutator_enlargedResidual_le_core
    (h : Data D H) (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (ha : moduleFrattiniImage D H = ⊥) :
    ⁅D.fullModule,enlargedResidual T L H⁆ ≤ (enlargedResidual T L H).pCoreIn 2 := by
  let E := enlargement T L H
  let K := enlargedResidual T L H
  let a := coreFrattiniAction T L H
  have hVK : D.fullModule ≤ normalizer (K : Set G) :=
    (h.fullModule_le_enlargement hfull).trans (le_normalizer_conjugateSpanBy _ _)
  have hzero : D.fullModule.subgroupOf E ≤ a.ker := (Subgroup.map_eq_bot_iff _).mp ha
  apply commutator_le.mpr
  intro v hv k hk
  let v' : E := ⟨v,h.fullModule_le_enlargement hfull hv⟩
  let k' : E := ⟨k,h.enlargedResidual_le_enlargement hk⟩
  have hmem : ⁅v,k⁆ ∈ K :=
    le_normalizer_iff_commutator_le_right.mp hVK (commutator_mem_commutator hv hk)
  let c : K := ⟨⁅v,k⁆,hmem⟩
  have hc : c ∈ ((a.comp (inclusion h.enlargedResidual_le_enlargement)).ker) := by
    change a (⁅v',k'⁆) = 1
    rw [map_commutatorElement,show a v'=1 from hzero hv]
    simp
  rw [h.coreFrattiniAction_kernel hn] at hc
  exact mem_map_of_mem K.subtype hc

private theorem module_core_quotient_action_trivial
    (h : Data D H) (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (ha : moduleFrattiniImage D H = ⊥)
    (hVK : D.fullModule ≤ normalizer (enlargedResidual T L H : Set G))
    (v : D.fullModule) :
    pCoreJoinAction 2 hVK (inclusion le_sup_right v) = 1 := by
  let K := enlargedResidual T L H
  let q := QuotientGroup.mk' (pCore 2 K)
  ext x
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  rw [pCoreJoinAction_mk]
  change q (K.normalizerMonoidHom _ k) = q k
  have hc := h.module_commutator_enlargedResidual_le_core hfull hn ha
    (commutator_mem_commutator v.property k.property)
  obtain ⟨c,hc,he⟩ := hc
  have he' : c = K.normalizerMonoidHom
      (inclusion (sup_le K.le_normalizer hVK) (inclusion le_sup_right v)) k * k⁻¹ := by
    apply Subtype.ext
    exact he
  have hq : q (K.normalizerMonoidHom
      (inclusion (sup_le K.le_normalizer hVK) (inclusion le_sup_right v)) k * k⁻¹) = 1 := by
    rw [←he']
    exact (QuotientGroup.eq_one_iff c).mpr hc
  rw [map_mul,map_inv] at hq
  exact mul_inv_eq_one.mp hq

/-- The actual join with the original module has exactly the expected core.
The original module may still have a nontrivial supplement outside K. -/
theorem Data.module_join_core_eq
    (h : Data D H) (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (ha : moduleFrattiniImage D H = ⊥)
    (hZ : center (XiQuotient (enlargedResidual T L H)) = ⊥) :
    (enlargedResidual T L H ⊔ D.fullModule : Subgroup G).pCoreIn 2 =
      (enlargedResidual T L H).pCoreIn 2 ⊔ D.fullModule := by
  let K := enlargedResidual T L H
  let Y := K ⊔ D.fullModule
  have hVK : D.fullModule ≤ normalizer (K : Set G) :=
    (h.fullModule_le_enlargement hfull).trans (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 D.fullModule := hfull.symm ▸ D.module_elementary
  have hV : D.fullModule ≤ Y.pCoreIn 2 := by
    intro v hv
    have hh := module_core_quotient_action_trivial h hfull hn ha hVK ⟨v,hv⟩
    have hk : inclusion (show D.fullModule ≤ Y from le_sup_right) (⟨v,hv⟩ : D.fullModule) ∈
        (pCoreJoinAction 2 hVK).ker := hh
    rw [pCoreJoinAction_kernel 2 hVK (IsElementaryAbelian.isPGroup 2 D.fullModule) hZ] at hk
    exact mem_map_of_mem Y.subtype hk
  have hQ : K.pCoreIn 2 ≤ Y.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer hVK)
  apply le_antisymm ?_ (sup_le hQ hV)
  intro y hy
  have hyY : y ∈ Y := pCoreIn_le 2 Y hy
  have hyprod : y ∈ (K : Set G) * (D.fullModule : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left K D.fullModule hVK]
    exact hyY
  obtain ⟨k,hk,v,hv,rfl⟩ := hyprod
  have hkcore : k ∈ Y.pCoreIn 2 := by
    have hh := (Y.pCoreIn 2).mul_mem hy ((Y.pCoreIn 2).inv_mem (hV hv))
    simpa only [mul_inv_cancel_right] using hh
  have hkQ : k ∈ K.pCoreIn 2 := inf_pCoreIn_le_of_le 2 (show K≤Y from le_sup_left) ⟨hk,hkcore⟩
  exact mul_mem (mem_sup_left hkQ) (mem_sup_right hv)

variable {I : Subgroup G}

/-- The native source exclusion supplies the exact local kernel consequences
without adding triviality, centerlessness, or module-placement premises. -/
theorem Data.trivial_image_localization
    (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ⁅D.fullModule,enlargedResidual T L H⁆ ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      (enlargedResidual T L H ⊔ D.fullModule : Subgroup G).pCoreIn 2 =
        (enlargedResidual T L H).pCoreIn 2 ⊔ D.fullModule ∧
      D.fullModule ≤ centralizer
        ((frattini ((enlargedResidual T L H).pCoreIn 2)).map
          ((enlargedResidual T L H).pCoreIn 2).subtype : Set G) := by
  have ha := h.moduleFrattiniImage_eq_bot f hn hs hK hp ho hm hmod hP hc
  have hZ : center (XiQuotient (enlargedResidual T L H)) = ⊥ := by
    obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
    obtain ⟨F,_,_,_,⟨eF⟩⟩ := hm
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr (e.trans (eF.prodCongr eF))).toEquiv,
      Subgroup.center_prod,GorensteinWalter.psl2_center_eq_bot F,bot_prod_bot,card_bot]
  exact ⟨h.module_commutator_enlargedResidual_le_core s.full_eq_local hn ha,
    h.module_join_core_eq s.full_eq_local hn ha hZ,
    h.fullModule_centralizes_core_frattini f hs.toLocalInput hP⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open BinaryThreeAction BinaryThreeAction.Parabolics Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The unchanged original enlargement retains its literal core localization
and a cubic-fixed supplement of index at most four outside the core. -/
theorem SourceCubicNormalizerEnlargement.exists_module_core_localization
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ _h : Data D H,
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      moduleFrattiniImage D H = ⊥ ∧
      ⁅D.fullModule,enlargedResidual T L H⁆ ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      (enlargedResidual T L H ⊔ D.fullModule : Subgroup G).pCoreIn 2 =
        (enlargedResidual T L H).pCoreIn 2 ⊔ D.fullModule ∧
      D.fullModule ≤ centralizer
        ((frattini ((enlargedResidual T L H).pCoreIn 2)).map
          ((enlargedResidual T L H).pCoreIn 2).subtype : Set G) ∧
      (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2).relIndex D.fullModule ≤ 4 := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  obtain ⟨hcomm,hcore,hphi⟩ := h.trivial_image_localization f hn hs hK hp ho hm h24 hP hcollapse
  exact ⟨H,P,h,hs.toLocalInput,h.moduleFrattiniImage_eq_bot f hn hs hK hp ho hm h24 hP hcollapse,
    hcomm,hcore,hphi,(h.collapsed_module_fixed_supplement f hs.toLocalInput hP hcollapse).2⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
