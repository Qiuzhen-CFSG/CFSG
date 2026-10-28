module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.CubicFixedVector
public import CFSG.Quasithin.Chapter10.SourceA5LayerElementComponent
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.SevenExclusion

/-!
# The original second A5 layer excludes the A7 overcomponent

The original full Sylow intersection transports to the conjugate block.
Its prescribed fixed vector is fixed by a cubic in that block. Distinct
original blocks commute, so this cubic centralizes the first A5 block.
The actual element-centralizer component cannot then have A7 two-core
quotient, by SevenExclusion. Involution order, cubic existence and block
commutation are derived from the original source data.

Source: Aschbacher–Smith 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem original_sylow_intersection
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓L) L := by
  have hLH : L≤localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hc : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T:Subgroup G)⊔(T:Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    ⟨T.subtype (show (T:Subgroup G)≤localJoin T L from le_sup_right),
      map_subgroupOf_eq_of_le le_sup_right⟩ hLH hc.subnormal

theorem source_conjugate_layer_cubic
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    (t v : G) (ht : t∈(T:Subgroup G))
    (hv : v∈(blockU (L.map (MulAut.conj t).toMonoidHom)).map
      (L.map (MulAut.conj t).toMonoidHom).subtype)
    (hvR : v∈centralizer ((T:Subgroup G)⊓L.map (MulAut.conj t).toMonoidHom:Set G)) :
    ∃ x : G, x∈L.map (MulAut.conj t).toMonoidHom ∧ orderOf x=3 ∧
      x∈centralizer ({v}:Set G) := by
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK := RankOne.Solvable.isAlternatingBlock_of_equiv
    ((MulAut.conj t).subgroupMap L) hL
  have hR := Chapter1.Section02.IndexTwo.isSylowIn_map (original_sylow_intersection D)
    (MulAut.conj t).toMonoidHom
  have hT : (T:Subgroup G).map (MulAut.conj t).toMonoidHom=(T:Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((T:Subgroup G).le_normalizer ht)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective,hT] at hR
  exact alternatingFive_exists_ambient_cubic_fixing_sylow_vector _ _ hK hR v hv hvR


/-- The distinct original blocks commute, so the second layer has a cubic
point centralizer commuting with the first block. -/
theorem source_conjugate_layer_cubic_centralizes_original
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    (t v : G) (ht : t∈(T:Subgroup G))
    (hv : v∈(blockU (L.map (MulAut.conj t).toMonoidHom)).map
      (L.map (MulAut.conj t).toMonoidHom).subtype)
    (hvR : v∈centralizer ((T:Subgroup G)⊓L.map (MulAut.conj t).toMonoidHom:Set G))
    (hvne : v≠1) (hvL : v∈centralizer (L:Set G)) :
    orderOf v=2 ∧ ∃ x : G, orderOf x=3 ∧ x∈centralizer ({v}:Set G) ∧
      x∈centralizer (L:Set G) := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let K := L.map (MulAut.conj t).toMonoidHom
  let tH : H := ⟨t,(show (T:Subgroup G)≤H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hLH : L≤H := (le_componentOrbit L T).trans le_sup_left
  obtain ⟨hA,_,hL⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  have hK : IsAlternatingBlock K 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv ((MulAut.conj t).subgroupMap L) hL
  have hKL : K≠L := by
    intro he
    exact alternatingFive_layer_not_centralizes_overgroup hK he.le hv hvne hvL
  have hmapA : A.map H.subtype=L := map_subgroupOf_eq_of_le hLH
  have hmapB : B.map H.subtype=K := by
    rw [show B=A.map (MulAut.conj tH).toMonoidHom from rfl,map_map]
    rw [show H.subtype.comp (MulAut.conj tH).toMonoidHom=
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl,←map_map,hmapA]
  have hAB : A≠B := by
    intro he
    exact hKL (hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA))
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
        (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm))
  have hc := hA.commutator_eq_bot_of_quasisimple_quotient
    (hA.map_equiv (MulAut.conj tH)) hqA hAB
  have hcomm : ⁅L,K⁆=⊥ := by
    rw [←hmapA,←hmapB,←map_commutator,hc,Subgroup.map_bot]
  have hKC : K≤centralizer (L:Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hv2 : orderOf v=2 := by
    let := hK.2.1.elementary
    obtain ⟨w,hw,rfl⟩ := hv
    apply orderOf_eq_prime _ hvne
    exact congrArg K.subtype (elemPow_eq_one_of_isElementaryAbelian w hw)
  obtain ⟨x,hxK,hx3,hxv⟩ := source_conjugate_layer_cubic D e hn hout t v ht hv hvR
  exact ⟨hv2,x,hx3,hxv,hKC hxK⟩


/-- The actual original second layer excludes an A7 quotient for every
containing component furnished by the source centralizer argument. -/
theorem source_conjugate_layer_component_not_seven
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    (t v : G) (ht : t∈(T:Subgroup G))
    (hv : v∈(blockU (L.map (MulAut.conj t).toMonoidHom)).map
      (L.map (MulAut.conj t).toMonoidHom).subtype)
    (hvR : v∈centralizer ((T:Subgroup G)⊓L.map (MulAut.conj t).toMonoidHom:Set G))
    (hvne : v≠1) (hvL : v∈centralizer (L:Set G))
    (I : Subgroup G) (hLI : L≤I) (hIX : I≤centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hNI : centralizer ({v}:Set G)≤normalizer (I:Set G)) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨hv2,x,hx3,hxv,hxL⟩ :=
    source_conjugate_layer_cubic_centralizes_original D e hn hout t v ht hv hvR hvne hvL
  rintro ⟨eI⟩
  exact source_fixed_center_not_seven_quotient D e v hv2 I hLI hIX hI hNI eI x hx3 hxv hxL

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
