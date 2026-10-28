module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NormalAtT
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.NilpotentCommutingConjugate
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Nonfusion at a bad core involution

The original component K is the unique ordinary component of C_G(t): every
other component centralizes K, whereas that centralizer has characteristic
two by source 2.5.18. Thus an involution whose centralizer has a component
not isomorphic to K cannot be conjugate to t. Normalizer growth in the
original Sylow produces a distinct commuting conjugate of i. The source
identity C_SC(i) = ⟨t,i⟩ forces that conjugate to equal ti, so ti also
avoids the conjugacy class of t.

Source: Aschbacher--Smith, 2.5.19, printed pp.561--562. These are the
nonfusion inputs used in the nonfull A₆ overcomponent and HS cover branches.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
variable {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- After the source normality conclusion, K is the only ordinary component
of the centralizer of the original central-core involution. -/
theorem source_component_eq_in_centralizer_t
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (X : Subgroup G) (hX : IsComponentIn X (centralizer ({t} : Set G))) : X = K := by
  by_contra hne
  have hK := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  have hcomm : X ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hX.commutator_eq_bot_of_ne hK hne)
  let C := centralizer ({t} : Set G) ⊓ centralizer (K : Set G)
  have hC : C ∈ Chapter1.He G :=
    (source_normal_component_centralizer_mem_He c hG hempty hgen hb hstar t ht htC htZ).2
  exact not_isComponent_of_twoCore (Chapter1.mem_He_iff.mp hC) (X.subgroupOf C)
    (hX.restrict (le_inf hX.1 hcomm) inf_le_left).2

/-- The larger source component in C_G(i) excludes fusion of i with t.
The component remains an actual subgroup of the original ambient group. -/
theorem source_nonfusion_of_nonisomorphic_component
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (X : Subgroup G) (hX : IsComponentIn X (centralizer ({i} : Set G)))
    (hnot : ¬ Nonempty (X ≃* K)) : ¬ IsConj t i := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj.symm
  let e : G ≃* G := MulAut.conj g
  have he : e i = t := hg
  have hmap : IsComponentIn (X.map e.toMonoidHom) (centralizer ({t} : Set G)) := by
    have hh := hX.map e
    rwa [CentralizerSmallKernelTransport.map_centralizer, he] at hh
  have hsame := source_component_eq_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
    (X.map e.toMonoidHom) hmap
  exact hnot ⟨(e.subgroupMap X).trans (MulEquiv.subgroupCongr hsame)⟩

/-- The same nonfusion conclusion for the literal component subgroup of G_i
used by the ordinary pump-up classifier. -/
theorem source_nonfusion_of_nonisomorphic_local_component
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (hnot : ¬ Nonempty (X ≃* K)) : ¬ IsConj t i := by
  let Gi := centralizer ({i} : Set G)
  have hXC : IsComponentIn (X.map Gi.subtype) Gi := by
    refine ⟨map_subtype_le X, ?_⟩
    change IsComponent Gi ((X.map Gi.subtype).comap Gi.subtype)
    rwa [comap_map_eq_self_of_injective Gi.subtype_injective]
  apply source_nonfusion_of_nonisomorphic_component c hG hempty hgen hb hstar
    t i ht htC htZ (X.map Gi.subtype) hXC
  rintro ⟨e⟩
  exact hnot ⟨(X.equivMapOfInjective Gi.subtype Gi.subtype_injective).trans e⟩

private theorem core_involution_conjugate_product_of_four_centralizer
    {G : Type*} [Group G] [Finite G] (Y K : Subgroup G)
    (hp : IsPGroup 2 Y) (hYN : Y ≤ normalizer (K : Set G))
    (t i : G) (htZ : t ∈ centerIn Y) (ht : orderOf t = 2)
    (hi : orderOf i = 2) (hiC : i ∈ Y ⊓ centralizer (K : Set G))
    (hiZ : i ∉ centerIn Y)
    (hR : (Y ⊓ centralizer (K : Set G)) ⊓ centralizer ({i} : Set G) =
      zpowers t ⊔ zpowers i) :
    IsConj i (t * i) := by
  let : Group.IsNilpotent Y := hp.isNilpotent
  let iY : Y := ⟨i, hiC.1⟩
  have hiYZ : iY ∉ center Y := by
    intro hz
    apply hiZ
    refine ⟨hiC.1, ?_⟩
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz (⟨y, hy⟩ : Y))
  obtain ⟨x, hne, hcomm⟩ := exists_distinct_commuting_conjugate_of_nilpotent hiYZ
  let j : G := MulAut.conj (x : G) i
  have hjY : j ∈ Y := Y.mul_mem (Y.mul_mem x.property hiC.1) (Y.inv_mem x.property)
  have hjC : j ∈ centralizer (K : Set G) :=
    (mem_normalizer_iff.mp
      (normalizer_le_normalizer_centralizer K (hYN x.property)) i).mp hiC.2
  have hij : Commute i j := congrArg Subtype.val hcomm.eq
  have hjR : j ∈ zpowers t ⊔ zpowers i :=
    hR ▸ ⟨⟨hjY, hjC⟩, mem_centralizer_singleton_iff.mpr hij.eq.symm⟩
  have ht2 : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
  have hi2 : i * i = 1 := by simpa only [hi, pow_two] using pow_orderOf_eq_one i
  have hti : Commute t i := (htZ.2 i hiC.1).symm
  have hjgen : j ∈ closure ({t, i} : Set G) := by
    exact (sup_le (zpowers_le.mpr (subset_closure (by simp)))
      (zpowers_le.mpr (subset_closure (by simp)))) hjR
  have hjne : j ≠ i := by
    intro he
    exact hne (Subtype.ext he)
  have hj1 : j ≠ 1 := by
    intro he
    have hi1 : i = 1 := (MulAut.conj (x : G)).injective
      (by simpa only [map_one] using he)
    simp [hi1] at hi
  have hjt : j ≠ t := by
    intro he
    have hfix : MulAut.conj (x : G) t = t := by
      change (x : G) * t * (x : G)⁻¹ = t
      rw [htZ.2 (x : G) x.property, mul_inv_cancel_right]
    have hieq : i = t := (MulAut.conj (x : G)).injective (he.trans hfix.symm)
    exact hiZ (hieq.symm ▸ htZ)
  have hjeq : j = t * i := by
    rcases (mem_closure_pair_iff t i ht2 hi2 hti j).mp hjgen with h | h | h | h
    · exact (hj1 h).elim
    · exact (hjt h).elim
    · exact (hjne h).elim
    · exact h
  exact isConj_iff.mpr ⟨(x : G), hjeq⟩

/-- The normalizer-growth step on printed p.561, with the actual source
centralizer identity R = ⟨t,i⟩ retained. -/
theorem source_core_involution_conjugate_product
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (t i : G) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hiC : i ∈ (S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G))
    (hiZ : i ∉ centerIn ((S : Subgroup H).map H.subtype))
    (hR : ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G) = zpowers t ⊔ zpowers i) : IsConj i (t * i) := by
  have hYN : (S : Subgroup H).map H.subtype ≤ normalizer (K : Set G) :=
    (map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  exact core_involution_conjugate_product_of_four_centralizer
    ((S : Subgroup H).map H.subtype) K (S.isPGroup'.map H.subtype) hYN
    t i htZ ht hi hiC hiZ hR

/-- Both noncentral points of the literal source four-group avoid the
central-core involution class. This supplies the HS cover nonfusion input. -/
theorem source_nonfusion_product_of_nonisomorphic_component
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : orderOf i = 2)
    (hiC : i ∈ (S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G))
    (hiZ : i ∉ centerIn ((S : Subgroup H).map H.subtype))
    (hR : ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G) = zpowers t ⊔ zpowers i)
    (X : Subgroup G) (hX : IsComponentIn X (centralizer ({i} : Set G)))
    (hnot : ¬ Nonempty (X ≃* K)) : ¬ IsConj t i ∧ ¬ IsConj t (t * i) := by
  have hn := source_nonfusion_of_nonisomorphic_component c hG hempty hgen hb hstar
    t i ht htC htZ X hX hnot
  have hf := source_core_involution_conjugate_product c t i ht hi htZ hiC hiZ hR
  exact ⟨hn, fun h => hn (h.trans hf.symm)⟩

/-- The product nonfusion input with the classifier's actual local component. -/
theorem source_nonfusion_product_of_nonisomorphic_local_component
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : orderOf i = 2)
    (hiC : i ∈ (S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G))
    (hiZ : i ∉ centerIn ((S : Subgroup H).map H.subtype))
    (hR : ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G) = zpowers t ⊔ zpowers i)
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (hnot : ¬ Nonempty (X ≃* K)) : ¬ IsConj t i ∧ ¬ IsConj t (t * i) := by
  have hn := source_nonfusion_of_nonisomorphic_local_component c hG hempty hgen hb hstar
    t i ht htC htZ X hX hnot
  have hf := source_core_involution_conjugate_product c t i ht hi htZ hiC hiZ hR
  exact ⟨hn, fun h => hn (h.trans hf.symm)⟩

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
