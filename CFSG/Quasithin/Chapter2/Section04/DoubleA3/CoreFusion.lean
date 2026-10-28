module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CoreDihedral
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.CommutingComponents
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Six-point fusion bound on an actual paired-cubic core

The independent cubic block actions conjugate all nine mixed nonzero
vectors to the product of their two fixed involutions. This product is
central in the original ambient Sylow group. An involution whose full
centralizer has only half that Sylow order cannot fuse to these vectors,
leaving at most the six nonidentity vectors in the two pure four-groups.

The general endpoint retains the target involution and its literal Sylow
centralizer, so it also applies after reselection inside a different
maximum elementary subgroup's normalizer.

Source: Aschbacher–Smith, the core fusion calculation repeated in 2.4.37,
printed p.550. The normalizer reselection is a separate earlier step.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem four_nonidentity_card (U : Subgroup G) (hU : Nat.card U = 4) :
    Nat.card {u : U // u ≠ 1} = 3 := by
  classical
  let : Fintype U := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique,←Nat.card_eq_fintype_card,hU]

private theorem pure_four_class_bound (A U V : Subgroup G) (i : G) (hi : i ≠ 1)
    (hU : Nat.card U = 4) (hV : Nat.card V = 4)
    (hpure : ∀ a : A, IsConj i (a : G) → (a : G) ∈ U ∨ (a : G) ∈ V) :
    Nat.card {a : A // IsConj i (a : G)} ≤ 6 := by
  classical
  have hne (a : {a : A // IsConj i (a : G)}) : (a.val : G) ≠ 1 := by
    intro he
    exact hi (isConj_one_left.mp (he ▸ a.property))
  let f : {a : A // IsConj i (a : G)} → {u : U // u ≠ 1} ⊕ {v : V // v ≠ 1} := fun a =>
    if ha : (a.val : G) ∈ U then
      Sum.inl ⟨⟨a.val,ha⟩,fun he => hne a (congrArg Subtype.val he)⟩
    else Sum.inr ⟨⟨a.val,(hpure a.val a.property).resolve_left ha⟩,
      fun he => hne a (congrArg Subtype.val he)⟩
  have hf : Function.Injective f := by
    intro a b he
    by_cases ha : (a.val : G) ∈ U <;> by_cases hb : (b.val : G) ∈ U
    · simp only [f,dif_pos ha,dif_pos hb,Sum.inl.injEq] at he
      exact Subtype.ext (Subtype.ext (congrArg (fun x : {u : U // u ≠ 1} => (x.val : G)) he))
    · simp only [f,dif_pos ha,dif_neg hb,Sum.inl_ne_inr] at he
    · simp only [f,dif_neg ha,dif_pos hb,Sum.inr_ne_inl] at he
    · simp only [f,dif_neg ha,dif_neg hb,Sum.inr.injEq] at he
      exact Subtype.ext (Subtype.ext (congrArg (fun x : {v : V // v ≠ 1} => (x.val : G)) he))
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_sum,four_nonidentity_card U hU,four_nonidentity_card V hV] using hh

namespace SourceCentralizerGeometry
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)

omit [Finite G] in
 theorem mixed_core_conjugacy (u v : G) (hu : u ∈ c.U₁) (hv : v ∈ c.U₂)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) : IsConj (g.z₁*g.z₂) (u*v) := by
  have hz₁ : g.z₁ ≠ 1 := by intro he; have hh := g.order_first; rw [he,orderOf_one] at hh; omega
  have hz₂ : g.z₂ ≠ 1 := by intro he; have hh := g.order_second; rw [he,orderOf_one] at hh; omega
  obtain ⟨k,hk,hku⟩ := Noncentrality.cubic_module_conjugacy _ c.cubic_first
    g.z₁ u g.first_mem hu hz₁ hu1
  obtain ⟨l,hl,hlv⟩ := Noncentrality.cubic_module_conjugacy _ c.cubic_second
    g.z₂ v g.second_mem hv hz₂ hv1
  have hlz₁ : l*g.z₁*l⁻¹=g.z₁ := by
    rw [←c.commute hl g.z₁ ((map_subtype_le _) g.first_mem),mul_inv_cancel_right]
  have hkv : k*v*k⁻¹=v := by
    rw [c.commute ((map_subtype_le _) hv) k hk,mul_inv_cancel_right]
  apply isConj_iff.mpr
  refine ⟨k*l,?_⟩
  calc
    (k*l)*(g.z₁*g.z₂)*(k*l)⁻¹ =
      (k*(l*g.z₁*l⁻¹)*k⁻¹)*(k*(l*g.z₂*l⁻¹)*k⁻¹) := by group
    _ = u*v := by rw [hlz₁,hlv,hku,hkv]

 theorem core_fusion_bound_of_not_conjugate (hQ : Nat.card (twoCore d.H) = 16)
    (i : G) (hi : i ≠ 1) (hni : ¬ IsConj i (g.z₁*g.z₂)) :
    Nat.card {a : twoCore d.H // IsConj i (a : G)} ≤ 6 := by
  have hD : c.D = ⊥ := Subgroup.card_eq_one.mp (by have hh := c.core_card; rw [hQ] at hh; omega)
  have hQeq : twoCore d.H = c.U₁ ⊔ c.U₂ := by simpa only [hD,sup_bot_eq] using c.product.1
  apply pure_four_class_bound (twoCore d.H) c.U₁ c.U₂ i hi
    (c.first.cubic_module_card c.cubic_first) (c.second.cubic_module_card c.cubic_second)
  intro a ha
  have hUC : c.U₁ ≤ centralizer (c.U₂ : Set G) :=
    le_centralizer_iff.mp ((map_subtype_le _).trans (c.commute.trans (centralizer_le (map_subtype_le _))))
  have hm : (a : G) ∈ (c.U₁ : Set G) * (c.U₂ : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ (hUC.trans (Subgroup.centralizer_le_normalizer _))]
    exact hQeq ▸ a.property
  obtain ⟨u,hu,v,hv,he⟩ := hm
  change u ∈ c.U₁ at hu
  change v ∈ c.U₂ at hv
  by_cases hu1 : u=1
  · exact Or.inr (by rw [←he]; change u*v ∈ c.U₂; rw [hu1,one_mul]; exact hv)
  by_cases hv1 : v=1
  · exact Or.inl (by rw [←he]; change u*v ∈ c.U₁; rw [hv1,mul_one]; exact hu)
  exact (hni (ha.trans ((g.mixed_core_conjugacy u v hu hv hu1 hv1).trans
    (he ▸ IsConj.refl (u*v))).symm)).elim

include g in
 theorem core_fusion_bound_of_half_sylow_centralizer
    (hQ : Nat.card (twoCore d.H) = 16) (i : G) (hi : i ≠ 1)
    (P : Sylow 2 (centralizer ({i} : Set G)))
    (hPT : (P : Subgroup _).map (centralizer ({i} : Set G)).subtype ≤ (T : Subgroup G))
    (hindex : ((P : Subgroup _).map (centralizer ({i} : Set G)).subtype).relIndex
      (T : Subgroup G) = 2) : Nat.card {a : twoCore d.H // IsConj i (a : G)} ≤ 6 := by
  apply g.core_fusion_bound_of_not_conjugate hQ i hi
  intro hic
  have hcard := card_centralizer_eq_of_isConj i (g.z₁*g.z₂) hic
  have hpart : twoPart (centralizer ({i} : Set G)) =
      twoPart (centralizer ({g.z₁*g.z₂} : Set G)) := by unfold twoPart; rw [hcard]
  have hTC : (T : Subgroup G) ≤ centralizer ({g.z₁*g.z₂} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (g.product_centralizes_sylow t ht)
  have heq : Nat.card ((P : Subgroup _).map (centralizer ({i} : Set G)).subtype) =
      Nat.card (T : Subgroup G) :=
    (sylow_image_card _ P).trans (hpart.trans (twoPart_eq_sylow_card T hTC))
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G)
    ((P : Subgroup _).map (centralizer ({i} : Set G)).subtype) (T : Subgroup G) bot_le hPT
  rw [relIndex_bot_left,relIndex_bot_left,hindex,heq] at hh
  have hpos : 0 < Nat.card (T : Subgroup G) := Nat.card_pos
  omega


 theorem core_fusion_bound (hQ : Nat.card (twoCore d.H) = 16) :
    Nat.card {a : twoCore d.H // IsConj g.z₂ (a : G)} ≤ 6 := by
  have hi : g.z₂ ≠ 1 := by intro he; have hh := g.order_second; rw [he,orderOf_one] at hh; omega
  exact g.core_fusion_bound_of_half_sylow_centralizer hQ g.z₂ hi g.P₂
    (g.second_intersection ▸ inf_le_left) g.second_sylow_index

end SourceCentralizerGeometry
end CFSG.Quasithin.Chapter2.DoubleA3
