module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorSuzukiBorel
public import Theory.GroupTheory.CComponent.PairOvergroupContainment
public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer

/-!
# Exchanged Suzuki components in the quiet tensor point centralizer

For an actual Suzuki component in the literal section centralizer,
restrict the original component to K join T.
The central nonidentity point supplies its two-core, and source 1.2.1(3)
gives index two for a moved component's normalizer. The actual Suzuki
quotient is simple of even order. Proper factor overgroups already lie
in M by the checked Borel theorem; the paired-component containment lemma
therefore puts every proper T-overgroup in M.

Together with the invariant case, every escaping component now gives
its literal H-star K join T, even without normality of X. The normal-X
branch supplies all the component premises. The numerical exclusion, full section-centralizer
containment and factorization remain with qt-d-10-nona5-point-selection,
as do tensor recognition and both quiet exclusions. Final point-control
assembly remains with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 8.3.7, printed pp.724--725.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem point_mem_HOver {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ∈ Chapter1.HOver G (T : Set G) := by
  let H := centralizer ({z} : Set G)
  have hzInT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D) hzV
  have hcyc : zpowers z ≤ H := zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr rfl)
  have hncyc : H ≤ normalizer (zpowers z : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
  have hcycCore := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (zpowers_le.mpr hzInT)) hcyc hncyc
  refine ⟨?_,hzT⟩
  intro he
  exact hz1 (mem_bot.mp (he ▸ hcycCore (mem_zpowers z)))

private theorem suzuki_exchanged_overgroups
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (U₀ : Subgroup G) (hTU : (T : Subgroup G) ≤ U₀)
    (hUG : U₀ ≤ centralizer ({z} : Set G))
    (K : Subgroup G) (hK : K ∈ Chapter1.cComponentsIn U₀)
    (hmove : ¬ (T : Subgroup G) ≤ normalizer (K : Set G))
    {m : ℕ} (hm : 1 ≤ m)
    (c : Chapter1.XiQuotient K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hproper : ∀ U : Subgroup G, (T : Subgroup G) ⊓ K ≤ U → U < K → U ≤ D.maximalLocal) :
    ∀ U : Subgroup G, (T : Subgroup G) ≤ U → U < K ⊔ (T : Subgroup G) →
      U ≤ D.maximalLocal := by
  let H := K ⊔ (T : Subgroup G)
  let A := K.subgroupOf H
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hGz := Chapter3.mem_HOver_of_sylow_interval T hTU hUG
    (point_mem_HOver D hzV hz1 hzT)
  have hKL : K ∈ Chapter1.L G (T : Subgroup G) :=
    (Chapter1.lemma_1_2_6 T hGz).1 hK |>.2
  have hA : A.IsCComponent := hKL.1
  have hi : (normalizer (A : Set H)).index = 2 :=
    source_nonnormal_normalizer_index D.simpleQTKE hKL hmove
  let a := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let aq := QuotientGroup.congr (pCore 2 A) (pCore 2 K) a (pCore_map_iso 2 a)
  let cA := aq.trans c
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let : IsSimpleGroup (A ⧸ pCore 2 A) := cA.isSimpleGroup
  have heven : 2 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr cA.toEquiv]
    exact even_iff_two_dvd.mp (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_even_card m (by omega))
  have hgen : A ⊔ (S : Subgroup H) = ⊤ := by
    change K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [←subgroupOf_sup (show K ≤ H from le_sup_left) (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
  have hlocal (U : Subgroup H) (hSU : A ⊓ (S : Subgroup H) ≤ U) (hUA : U < A) :
      U ≤ D.maximalLocal.subgroupOf H := by
    have hUM : U.map H.subtype ≤ D.maximalLocal := by
      apply hproper
      · intro x hx
        have hxH : x ∈ H := (show K ≤ H from le_sup_left) hx.2
        exact mem_map_of_mem H.subtype (hSU (show (⟨x,hxH⟩ : H) ∈ A ⊓ (S : Subgroup H) from ⟨hx.2,hx.1⟩))
      · have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hUA
        rwa [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] at hh
    exact map_le_iff_le_comap.mp hUM
  have hbound := hA.pair_overgroups_le S A (D.maximalLocal.subgroupOf H)
    heven hi hgen (fun x hx => hTM hx) hlocal
  intro U hTU hUH
  have hUt : U.subgroupOf H < ⊤ := lt_top_iff_ne_top.mpr (fun he =>
    hUH.not_ge (subgroupOf_eq_top.mp he))
  have hh := hbound (U.subgroupOf H) (fun x hx => hTU hx) hUt
  intro x hx
  exact hh (show (⟨x,hUH.le hx⟩ : H) ∈ U.subgroupOf H from hx)

/-- A Suzuki component in the literal section centralizer that escapes M
gives its actual H-star. The original X need not be normal in G_z, and T
may exchange the component with its conjugate. -/
theorem quiet_tensor_section_suzuki_hstar_in
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (U₀ : Subgroup G) (hTU : (T : Subgroup G) ≤ U₀)
    (hUG : U₀ ≤ centralizer ({z} : Set G))
    (hYU : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2) ≤ U₀) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn U₀ → K ≤ Y →
      (∃ m, 1 ≤ m ∧ Nonempty (Chapter1.XiQuotient K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      ¬ K ≤ D.maximalLocal →
      K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal := by
  dsimp only
  intro K hK hKY ⟨m,hm,⟨c⟩⟩ hnot
  obtain ⟨_,hb,_,hBM⟩ := quiet_tensor_section_component_borel_in
    D hn e hbase hzV hz1 hzT U₀ hYU K hK hKY ⟨m,⟨c⟩⟩
  have hproper (U : Subgroup G) (hTU : (T : Subgroup G) ⊓ K ≤ U) (hUK : U < K) :
      U ≤ D.maximalLocal := (hb.unique_maximal U hTU hUK).trans (le_sup_left.trans hBM)
  have hH := Chapter3.mem_HOver_of_sylow_interval T le_sup_right (sup_le (hK.1.trans hUG) hzT)
    (point_mem_HOver D hzV hz1 hzT)
  refine ⟨⟨hH,fun hc => hnot (le_sup_left.trans hc)⟩,?_⟩
  intro U hU hUH
  by_contra hHU
  apply hU.2
  by_cases hTK : (T : Subgroup G) ≤ normalizer (K : Set G)
  · have hKU : K ⊓ U < K := lt_of_le_of_ne inf_le_left (fun he => hHU
      (sup_le (he ▸ inf_le_right) hU.1.2))
    have hKM : K ⊓ U ≤ D.maximalLocal := hproper _
      (le_inf inf_le_right (inf_le_left.trans hU.1.2)) hKU
    have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
      le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
    intro u hu
    have hup : u ∈ (K : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hTK]
      exact hUH hu
    obtain ⟨k,hk,t,ht,hkt⟩ := hup
    have hkU : k ∈ U := by
      have hh := U.mul_mem hu (U.inv_mem (hU.1.2 ht))
      rwa [←hkt,mul_inv_cancel_right] at hh
    rw [←hkt]
    exact D.maximalLocal.mul_mem (hKM ⟨hk,hkU⟩) (hTM ht)
  · exact suzuki_exchanged_overgroups D hzV hz1 hzT U₀ hTU hUG K hK hTK hm c hproper
      U hU.1.2 (lt_of_le_not_ge hUH hHU)

/-- The H-star construction for a component of the full point centralizer. -/
theorem quiet_tensor_section_suzuki_hstar
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let Y := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz → K ≤ Y →
      (∃ m, 1 ≤ m ∧ Nonempty (Chapter1.XiQuotient K ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) →
      ¬ K ≤ D.maximalLocal →
      K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal := by
  exact quiet_tensor_section_suzuki_hstar_in D hn e hbase hzV hz1 hzT
    (centralizer ({z} : Set G)) hzT le_rfl
    ((commutatorPreimage_le _ _ _).trans inf_le_left)

/-- Any escaping component of the normal-X branch gives its actual H-star,
including components exchanged by T. -/
theorem quiet_tensor_normal_point_hstar
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.X.subgroupOf d.Gz).Normal →
    ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn d.Gz →
      ¬ K ≤ D.maximalLocal →
      K ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal := by
  dsimp only
  intro hnormal K hK hnot
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨hKY,hm⟩ := quiet_tensor_normal_point_components D hn e hbase hzV hz1 hzT hnormal K hK
  have hnorm : d.Gz ⊓ normalizer (d.X : Set G) = d.Gz :=
    inf_of_le_left ((normal_subgroupOf_iff_le_normalizer
      (d.X_le.trans inf_le_right)).mp hnormal)
  exact quiet_tensor_section_suzuki_hstar D hn e hbase hzV hz1 hzT K hK
    (by rwa [hnorm]) hm hnot

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
