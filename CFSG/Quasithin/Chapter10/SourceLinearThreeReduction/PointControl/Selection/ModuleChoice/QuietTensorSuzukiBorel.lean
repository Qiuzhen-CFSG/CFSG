module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorEscape
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.CComponent.LocalOrbitSolvable

/-!
# Suzuki Borels in the original quiet tensor point centralizer

For a C-component K in the literal section centralizer Y_z, the original
S = O₂(XT) meets K in a Sylow subgroup. Since S ≤ T, maximality identifies
S ∩ K with T ∩ K. The actual Suzuki quotient lifts the rank-one Borel facts
through K's two-core. The component-orbit solvability theorem makes the
join of this Borel and S solvable even when S permutes components. Its
Sylow subgroup is still the original S, so the proved 8.3.6 puts it in M.

In the normal-X branch the preceding source classification supplies every
component's Suzuki quotient and placement in Y_z. If K escapes M, its
intersection with M is exactly its Borel. When T normalizes K, the product
decomposition in KT makes every proper T-overgroup lie in M, giving an
actual H-star KT. No component invariance is assumed for Borel containment.

The remaining exchanged-component H-star argument, generation-parameter
exclusions, full section-centralizer containment and G_z factorization
remain source obligations. Tensor recognition and both quiet exclusions
remain with qt-d-10-nona5-point-selection; final point-control assembly
remains with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 8.3.7, printed pp.724--725, using F.1.3(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
open ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

private theorem suzuki_borel_facts {K S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 (S ⊓ K) K) {m : ℕ}
    (e : Chapter1.XiQuotient K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    RankOneBorelFacts K S := by
  obtain ⟨P,hP⟩ := hS
  apply rankOneBorelFacts_of_quotient K S P hP
  exact rankOneSylowFacts_of_equiv _ e (suzuki_rankOneSylowFacts m _)

private theorem relative_borel_adjoin {H K S : Subgroup G}
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hb : Group.IsSolvable (borel K S)) :
    Group.IsSolvable (borel K S ⊔ S : Subgroup G) := by
  apply hK.relative_local_adjoin_isSolvable hKH inf_le_left hSH hS _ hb
  have hSN : S ⊓ normalizer (K : Set G) ≤
      normalizer ((S ⊓ K : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans S.le_normalizer) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf inf_le_right (hSN.trans (normalizer ((S ⊓ K : Subgroup G) : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The original component Borel has a solvable join with S and lies in M.
Neither T nor S is required to normalize the component. -/
theorem quiet_tensor_section_component_borel_in
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (U : Subgroup G)
    (hYU : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2) ≤ U) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn U → K ≤ Y →
      (∃ m, Nonempty (Chapter1.XiQuotient K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ⊓ K = d.S ⊓ K ∧
      RankOneBorelFacts K (T : Subgroup G) ∧
      Group.IsSolvable (borel K (T : Subgroup G) ⊔ d.S : Subgroup G) ∧
      borel K (T : Subgroup G) ⊔ d.S ≤ D.maximalLocal := by
  dsimp only
  intro K hK hKY hm
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
  have hYG : Y ≤ U := hYU
  have hSY : Chapter1.IsSylowIn 2 d.S Y := quiet_point_sectionCentralizer_sylow hzT
  have hKYc := hK.2.subgroupOf_of_le hKY hYG
  have hSK : Chapter1.IsSylowIn 2 (d.S ⊓ K) K :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSY hKY hKYc.subnormal
  have hi : (T : Subgroup G) ⊓ K = d.S ⊓ K :=
    (Chapter1.isSylowIn_iff.mp hSK).2.2 _
      (T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left))
      (inf_le_inf_right K d.S_le_T) inf_le_right
  obtain ⟨m,⟨c⟩⟩ := hm
  have hb : RankOneBorelFacts K (T : Subgroup G) :=
    suzuki_borel_facts (hi.symm ▸ hSK) c
  have hbs : Group.IsSolvable (borel K (T : Subgroup G) ⊔ d.S : Subgroup G) := by
    have he : borel K (T : Subgroup G) = borel K d.S := by unfold ChapterF.Source.borel; rw [hi]
    rw [he]
    apply relative_borel_adjoin hK.1 hK.2
      ((Chapter1.isSylowIn_iff.mp hSY).2.1.trans hYG)
      (Chapter1.isSylowIn_iff.mp hSY).1
    exact he ▸ hb.solvable
  let := hbs
  refine ⟨hi,hb,hbs,quiet_tensor_solvable_overgroup_le D hn e hbase hzV hz1 hzT _ ?_⟩
  exact hSY.restrict le_sup_right
    (sup_le ((show borel K (T : Subgroup G) ≤ K from inf_le_left).trans hKY)
      (Chapter1.isSylowIn_iff.mp hSY).2.1)

/-- The preceding Borel containment in the full original point centralizer. -/
theorem quiet_tensor_section_component_borel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz → K ≤ Y →
      (∃ m, Nonempty (Chapter1.XiQuotient K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      (T : Subgroup G) ⊓ K = d.S ⊓ K ∧
      RankOneBorelFacts K (T : Subgroup G) ∧
      Group.IsSolvable (borel K (T : Subgroup G) ⊔ d.S : Subgroup G) ∧
      borel K (T : Subgroup G) ⊔ d.S ≤ D.maximalLocal := by
  exact quiet_tensor_section_component_borel_in D hn e hbase hzV hz1 hzT
    (centralizer ({z} : Set G)) ((commutatorPreimage_le _ _ _).trans inf_le_left)

/-- The normal-X branch supplies all Borel premises on every actual component.
For a component escaping M, its literal intersection with M is exactly its
Sylow Borel. -/
theorem quiet_tensor_normal_point_component_borel
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz →
      RankOneBorelFacts K (T : Subgroup G) ∧
      Group.IsSolvable (borel K (T : Subgroup G) ⊔ d.S : Subgroup G) ∧
      borel K (T : Subgroup G) ⊔ d.S ≤ D.maximalLocal ∧
      (¬ K ≤ D.maximalLocal → K ⊓ D.maximalLocal = borel K (T : Subgroup G)) := by
  dsimp only
  intro hnormal K hK
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨hKY,m,hm,he⟩ :=
    quiet_tensor_normal_point_components D hn e hbase hzV hz1 hzT hnormal K hK
  have hnorm : d.Gz ⊓ normalizer (d.X : Set G) = d.Gz :=
    inf_of_le_left ((normal_subgroupOf_iff_le_normalizer
      (d.X_le.trans inf_le_right)).mp hnormal)
  have hKY' : K ≤ commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G))
      d.X (d.X.pCoreIn 2) := by rwa [hnorm]
  obtain ⟨_,hb,hs,hM⟩ := quiet_tensor_section_component_borel
    D hn e hbase hzV hz1 hzT K hK hKY' ⟨m,he⟩
  refine ⟨hb,hs,hM,fun hnot => le_antisymm (hb.unique_maximal _ ?_ ?_) ?_⟩
  · have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
      le_sup_right.trans (D.lemma_3_2_3_uniqueness
        (source_module_nonsolvable_uniqueness D)).2.1
    exact le_inf inf_le_right (inf_le_left.trans hTM)
  · exact lt_of_le_of_ne inf_le_left (fun he => hnot (he ▸ inf_le_right))
  · exact le_inf inf_le_left (le_sup_left.trans hM)

/-- Every proper overgroup inside an original normal-branch component of
its Sylow intersection lies in M, including components permuted by T. -/
theorem quiet_tensor_normal_point_component_proper_overgroups
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz →
      ∀ A : Subgroup G, (T : Subgroup G) ⊓ K ≤ A → A < K → A ≤ D.maximalLocal := by
  dsimp only
  intro hnormal K hK A hTA hAK
  obtain ⟨hb,_,hM,_⟩ :=
    quiet_tensor_normal_point_component_borel D hn e hbase hzV hz1 hzT hnormal K hK
  exact (hb.unique_maximal A hTA hAK).trans (le_sup_left.trans hM)

/-- An invariant Suzuki component escaping M gives the actual H-star KT.
The H-star condition is derived from the Borel containment, not supplied as
an additional classification hypothesis. -/
theorem quiet_tensor_normal_point_invariant_hstar
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz →
      (T : Subgroup G) ≤ normalizer (K : Set G) →
      ¬ K ≤ D.maximalLocal →
      K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal := by
  dsimp only
  intro hnormal K hK hTK hnot
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨hb,_,hBM,_⟩ :=
    quiet_tensor_normal_point_component_borel D hn e hbase hzV hz1 hzT hnormal K hK
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness
      (source_module_nonsolvable_uniqueness D)).2.1
  have hzInT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D) hzV
  have hcyc : zpowers z ≤ d.Gz := zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr rfl)
  have hncyc : d.Gz ≤ normalizer (zpowers z : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact le_rfl
  have hcycCore := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (zpowers_le.mpr hzInT)) hcyc hncyc
  have hGz : d.Gz ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,hzT⟩
    intro he
    exact hz1 (mem_bot.mp (he ▸ hcycCore (mem_zpowers z)))
  have hH : K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right (sup_le hK.1 hzT) hGz
  refine ⟨⟨hH,fun hc => hnot (le_sup_left.trans hc)⟩,?_⟩
  intro A hA hAH
  by_contra hHA
  have hKA : K ⊓ A < K := lt_of_le_of_ne inf_le_left (fun he => hHA
    (sup_le (he ▸ inf_le_right) hA.1.2))
  have hKM : K ⊓ A ≤ D.maximalLocal :=
    (hb.unique_maximal _ (le_inf inf_le_right (inf_le_left.trans hA.1.2)) hKA).trans
      (le_sup_left.trans hBM)
  apply hA.2
  intro a ha
  have hap : a ∈ (K : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hTK]
    exact hAH ha
  obtain ⟨k,hk,t,ht,hkt⟩ := hap
  have hkA : k ∈ A := by
    have hh := A.mul_mem ha (A.inv_mem (hA.1.2 ht))
    rwa [←hkt,mul_inv_cancel_right] at hh
  rw [←hkt]
  exact D.maximalLocal.mul_mem (hKM ⟨hk,hkA⟩) (hTM ht)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
