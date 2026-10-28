module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterCoreBound
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallPersistenceSource
/-!
# Original source consumers for the PSL₃(3) residual action

The source center marks and small-component persistence make the local
residual invariant under N_G(S). Thus the original crossing can be adjusted
to centralize it. The source normalizer index supplies the adjusted square,
and the disjoint-core calculation gives the cyclic order-dividing-four
conclusion with no residual or crossing premise left over.
Source: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_residual_mark
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (e : K ≃* Matrix.PSL3Three.PSL) :
    ∃ k : K, orderOf k = 2 ∧ k.val ∈ centerIn ((S : Subgroup H).map H.subtype) ∧
      normalizer ((S : Subgroup H).map H.subtype : Set G) ≤
        normalizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G) := by
  let Y := (S : Subgroup H).map H.subtype
  obtain ⟨t,k,ht,hk,htC,hcore,hline,_,hspanK,_,_⟩ :=
    ComponentSelection.MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t ∈ centerIn Y := by
    have hh : t ∈ centerIn Y ⊓ twoCore H := hcore ▸ mem_zpowers t
    exact hh.1
  have hKY : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have horbit : componentOrbit K Y = K := le_antisymm
    (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hKY) (le_componentOrbit _ _)
  have hkZK : k ∈ centerIn Y ⊓ K := by
    rw [horbit] at hline
    exact hline ▸ mem_zpowers k
  let zK : K := ⟨k,hkZK.2⟩
  have hzK : orderOf zK = 2 := by simpa only [zK,Subgroup.orderOf_mk] using hk
  refine ⟨zK,hzK,hkZK.1,?_⟩
  exact local_residual_normalized_by_sylow_normalizer K Y (Or.inl ⟨e⟩) zK hzK t hspanK
    (MathieuSourceSetup.small_component_centralizer_residual c hG hempty hgen (Or.inl ⟨e⟩)
      t ht htC htZ).2.2

theorem linear_three_source_core_cyclic_dvd_four_of_source
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (e : K ≃* Matrix.PSL3Three.PSL) :
    IsCyclic (twoCore H) ∧ Nat.card (twoCore H) ∣ 4 := by
  let Y := (S : Subgroup H).map H.subtype
  obtain ⟨k,hk,hkZ,hN⟩ := linear_three_source_residual_mark c hG hempty hgen hb e
  obtain ⟨x,hxT,hxS,hxN,_⟩ := exists_outside_normalizer_square_mem Y c.T c.T.isPGroup' c.sylow_lt
  obtain ⟨x,hxT,hxS,hxN,hxR⟩ := local_residual_crossing_adjustment c (Or.inl ⟨e⟩)
    k hk hkZ hxT hxS hxN (hN hxN)
  have hi := MathieuSourceSetup.source_normalizer_index_two c hG hempty hgen hb
  let N := (c.T : Subgroup G) ⊓ normalizer (Y : Set G)
  have hx2 : x^2 ∈ Y := (Y.subgroupOf N).sq_mem_of_index_two hi ⟨x,hxT,hxN⟩
  exact linear_three_source_core_cyclic_dvd_four c hG hempty hgen e k hk hxT hxS hxN hx2 hxR

theorem linear_three_outer_lift_of_source
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (e : K ≃* Matrix.PSL3Three.PSL)
    (hout : ¬ (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G)) :
    let α := MathieuSourceSetup.componentAction c
    ∃ k : K, orderOf k = 2 ∧ ∃ y : H, y ∈ S ∧
      (y : G) ∈ centralizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G) ∧
      α y ∉ MulAut.innerSubgroup K ∧ orderOf (α y) = 4 ∧ (α y)^2 = MulAut.conj k ∧
      H ⊓ centralizer ((GLTwoThreeLocal.residual k).map K.subtype : Set G) =
        twoCore H ⊔ zpowers (y : G) := by
  obtain ⟨k,hk,_,hN⟩ := linear_three_source_residual_mark c hG hempty hgen hb e
  exact ⟨k,hk,linear_three_outer_residual_lift c hG hempty hgen e k hk hout
    ((Subgroup.le_normalizer).trans hN)⟩

end CFSG.Quasithin.Chapter2.Section05
