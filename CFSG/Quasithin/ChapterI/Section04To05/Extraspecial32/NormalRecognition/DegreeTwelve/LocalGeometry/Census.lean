module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.CoreProducts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.Orbits
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.OutsideProducts
public import Theory.GroupTheory.CenterTwoCoreSylowPromotion
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Ambient involution coverage and assembly of the count at z

Sylow promotion places an ambient involution in the literal centralizer of
`z`. The local orbit inputs and the selected fusion of the outside-core
representative then identify its ambient class. For the count, cyclic
membership in the source is identified with the canonical half-order power.
The actual fiber is a dependent sum over the twelve-element core orbit;
simultaneous centralizer conjugation makes all its slices equinumerous.
Each slice is the disjoint union of the four core products and sixteen
outside-core products.

The final theorem constructs the orbit and product inputs from the local
hypotheses and relative quaternion normality. The selected configuration
remains explicit: its ambient fusion of the outside-core representative is
essential to the two-class assertion and the mixed-pair count.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.7, 4.1 and 4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census

open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder

variable {G : Type*} [Group G] {z t : G}

private theorem orderOf_conjugate {x y : G} (hc : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  exact ((MulAut.conj c).orderOf_eq x).symm

variable [Finite G]

/-- The self-centralizing fusion eight supplies the self-centralizing-core
premise of Sylow promotion, with every subgroup in its literal ambient position. -/
public theorem centralizer_sylow_promotes (h : Hypotheses z) (d : FusionEightData z)
    (T : Sylow 2 (Centralizer z)) :
    ∃ S : Sylow 2 G, (S : Subgroup G) =
      (T : Subgroup (Centralizer z)).map (Centralizer z).subtype := by
  have hc : Nat.card (center (pCore 2 (Centralizer z))) = 2 := by
    rw [← h.core_eq_pCore]
    let : IsExtraspecial 2 (Core z) := h.extraspecial
    exact IsExtraspecial.center_order_p 2 (Core z)
  have hs : centralizer (pCore 2 (Centralizer z) : Set (Centralizer z)) ≤
      pCore 2 (Centralizer z) := by
    rw [← h.core_eq_pCore]
    intro x hx
    have hxC : (x : G) ∈ centralizer (coreInG z : Set G) := by
      rintro y ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hx y hy)
    have hxF : (x : G) ∈ fusionCore z := by
      rw [← d.centralizer_eq]
      exact centralizer_le (fusionCore_le z) hxC
    have hxQ := fusionCore_le z hxF
    rw [← coreInG_subgroupOf z]
    exact hxQ
  exact (centralizer_structure_of_center_two_core z h.involution hc hs).2.2 T

/-- Every ambient involution has a conjugate in the literal centralizer. -/
public theorem involution_conjugate_into_centralizer (h : Hypotheses z)
    (d : FusionEightData z) {x : G} (hx : orderOf x = 2) :
    ∃ y : Centralizer z, IsConj x (y : G) := by
  obtain ⟨S, hS⟩ := centralizer_sylow_promotes h d
    (Sylow.nonempty.some : Sylow 2 (Centralizer z))
  obtain ⟨y, hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have hSC : (S : Subgroup G) ≤ Centralizer z := hS ▸ map_subtype_le _
  exact ⟨⟨y, hSC y.property⟩, hy⟩

/-- The selected representative turns the local outside-core orbit into an
ambient class of the distinguished involution. -/
public theorem outside_isConj (h : Hypotheses z) (a : SelectedFusionData h)
    (o : OrbitData z a.u) {x : G} (hxH : x ∈ Centralizer z)
    (hxQ : x ∉ coreInG z) (hx : orderOf x = 2) : IsConj z x := by
  obtain ⟨c, hc⟩ := o.outside_transitive x hxH hxQ hx
  exact a.u_fused.trans (isConj_iff.mpr ⟨c, hc⟩)

omit [Finite G] in
/-- Inside the core, the long orbit is precisely the second ambient class. -/
public theorem coreSecond_iff (d : FusionEightData z) {u : G} (o : OrbitData z u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    {x : G} (hxQ : x ∈ coreInG z) (hx : orderOf x = 2) :
    x ∉ fusionCore z ↔ IsConj t x := by
  have htF : t ∉ fusionCore z := fun hf =>
    hnt (d.fusion t hf (fun he => by simp [he] at ht))
  constructor
  · intro hxF
    obtain ⟨c, hc⟩ := o.core_transitive ⟨t, htQ, ht, htF⟩ ⟨x, hxQ, hx, hxF⟩
    exact isConj_iff.mpr ⟨c, hc⟩
  · intro htx hxF
    exact hnt ((d.fusion x hxF (fun he => by simp [he] at hx)).trans htx.symm)


/-- The local orbits exhaust all ambient involutions after Sylow conjugacy. -/
public theorem two_classes_of_orbits (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x := by
  intro x hx
  obtain ⟨y, hxy⟩ := involution_conjugate_into_centralizer h d hx
  have hy : orderOf (y : G) = 2 := (orderOf_conjugate hxy).symm.trans hx
  suffices IsConj z (y : G) ∨ IsConj t (y : G) from
    this.imp (fun hc => hc.trans hxy.symm) (fun hc => hc.trans hxy.symm)
  by_cases hyQ : (y : G) ∈ coreInG z
  · by_cases hyF : (y : G) ∈ fusionCore z
    · exact Or.inl (d.fusion y hyF (fun he => by simp [he] at hy))
    · exact Or.inr ((coreSecond_iff d o htQ ht hnt hyQ hy).mp hyF)
  · exact Or.inl (outside_isConj h a o y.property hyQ hy)

/-- Ambient second-class membership in H is precisely membership in the long
core orbit. This does not replace ambient fusion by internal conjugacy. -/
public theorem second_class_in_centralizer (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    {x : G} (hxH : x ∈ Centralizer z) :
    IsConj t x ↔ x ∈ coreInG z ∧ orderOf x = 2 ∧ x ∉ fusionCore z := by
  constructor
  · intro htx
    have hx : orderOf x = 2 := (orderOf_conjugate htx).symm.trans ht
    have hxQ : x ∈ coreInG z := by
      by_contra hQ
      exact hnt ((outside_isConj h a o hxH hQ hx).trans htx.symm)
    exact ⟨hxQ, hx, (coreSecond_iff d o htQ ht hnt hxQ hx).mpr htx⟩
  · rintro ⟨hxQ, hx, hxF⟩
    exact (coreSecond_iff d o htQ ht hnt hxQ hx).mp hxF

/-- The book's cyclic-membership condition is exactly the canonical half-order
condition for these mixed involution pairs. -/
public theorem halfOrder_eq_iff_cyclic (h : Hypotheses z)
    (ht : orderOf t = 2) (hnt : ¬ IsConj z t) {x : G} (hx : IsConj z x) :
    halfOrder x t = z ↔ z ∈ zpowers (x * t) := by
  have hm : halfOrder x t ∈ zpowers (x * t) := by
    rw [halfOrder_def]
    exact pow_mem (mem_zpowers _) _
  constructor
  · intro he
    exact he ▸ hm
  · intro hz
    have hh := (halfOrder_properties h.involution ht hnt hx (IsConj.refl t)).1
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨halfOrder x t, hm⟩ : zpowers (x * t)))
      (y := ⟨z, hz⟩)
      ((Subgroup.orderOf_coe _).symm.trans hh)
      ((Subgroup.orderOf_coe _).symm.trans h.involution))

private theorem halfOrder_self_ne (h : Hypotheses z)
    (htH : t ∈ Centralizer z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    halfOrder z t ≠ z := by
  have hz2 : z ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one z
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hc : Commute z t := (mem_centralizer_singleton_iff.mp htH).symm
  have hp2 : (z * t) ^ 2 = 1 := by rw [hc.mul_pow, hz2, ht2, one_mul]
  have hp1 : z * t ≠ 1 := by
    intro he
    have heq : z = t := (eq_inv_of_mul_eq_one_left he).trans (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht2))
    exact hnt (heq ▸ IsConj.refl z)
  have hpo : orderOf (z * t) = 2 := orderOf_eq_prime hp2 hp1
  rw [halfOrder_def, hpo]
  norm_num only [Nat.reduceDiv, pow_one]
  intro he
  have he1 : t = 1 := mul_left_cancel (he.trans (mul_one z).symm)
  simp [he1] at ht


private abbrev Slice (z y : G) :=
  {x : G // IsConj z x ∧ halfOrder x y = z}

private noncomputable def productsEquivSlice (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    CoreProducts z t ⊕ OutsideProducts z t ≃ Slice z t := by
  let f : CoreProducts z t ⊕ OutsideProducts z t → Slice z t := fun p =>
    match p with
    | Sum.inl x =>
      have hx := d.fusion x x.property.1 x.property.2.1
      ⟨x, hx, (halfOrder_eq_iff_cyclic h ht hnt hx).mpr x.property.2.2.2⟩
    | Sum.inr x =>
      have hx := outside_isConj h a o x.property.1 x.property.2.1 x.property.2.2.1
      ⟨x, hx, (halfOrder_eq_iff_cyclic h ht hnt hx).mpr x.property.2.2.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    have he' := congrArg Subtype.val he
    cases p with
    | inl x =>
      cases q with
      | inl y => exact congrArg Sum.inl (Subtype.ext he')
      | inr y => exact False.elim (y.property.2.1 (he' ▸ fusionCore_le z x.property.1))
    | inr x =>
      cases q with
      | inl y => exact False.elim (x.property.2.1 (he' ▸ fusionCore_le z y.property.1))
      | inr y => exact congrArg Sum.inr (Subtype.ext he')
  · intro x
    have hxorder : orderOf (x : G) = 2 := (orderOf_conjugate x.property.1).symm.trans h.involution
    have hxcyc := (halfOrder_eq_iff_cyclic h ht hnt x.property.1).mp x.property.2
    by_cases hxQ : (x : G) ∈ coreInG z
    · have hxF : (x : G) ∈ fusionCore z := subset_closure ⟨hxQ, x.property.1⟩
      have hx1 : (x : G) ≠ 1 := fun he => by simp [he] at hxorder
      have hxz : (x : G) ≠ z := by
        intro he
        have hf := x.property.2
        rw [he] at hf
        exact halfOrder_self_ne h (coreInG_le z htQ) ht hnt hf
      exact ⟨Sum.inl ⟨x, hxF, hx1, hxz, hxcyc⟩, rfl⟩
    · have hxH := (fiber_mem_centralizer h.involution ht hnt
        (⟨((x : G), t), x.property.1, IsConj.refl t, x.property.2⟩ : Fiber z t z)).1
      exact ⟨Sum.inr ⟨x, hxH, hxQ, hxorder, hxcyc⟩, rfl⟩

omit [Finite G] in
private noncomputable def sliceConjEquiv (z t : G) (c : Centralizer z) :
    Slice z t ≃ Slice z (MulAut.conj (c : G) t) := by
  let e := MulAut.conj (c : G)
  have hez : e z = z := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp c.property)
  apply Equiv.subtypeEquiv e.toEquiv
  intro x
  have hconj : IsConj x (e x) := isConj_iff.mpr ⟨c, rfl⟩
  change (IsConj z x ∧ halfOrder x t = z) ↔
    (IsConj z (e x) ∧ halfOrder (e x) (e t) = z)
  have hf : halfOrder (e x) (e t) = z ↔ halfOrder x t = z := by
    constructor
    · intro hx
      apply e.injective
      rw [hez, ← halfOrder_map, hx]
    · intro hx
      rw [halfOrder_map, hx, hez]
  exact and_congr ⟨fun hx => hx.trans hconj, fun hx => hx.trans hconj.symm⟩ hf.symm

private noncomputable def fiberEquivSigma (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Fiber z t z ≃ Σ y : CoreSecond z, Slice z (y : G) where
  toFun p :=
    have hyH := (fiber_mem_centralizer h.involution ht hnt p).2
    ⟨⟨p.val.2, (second_class_in_centralizer h d a o htQ ht hnt hyH).mp p.property.2.1⟩,
      ⟨p.val.1, p.property.1, p.property.2.2⟩⟩
  invFun p := ⟨((p.2 : G), (p.1 : G)), p.2.property.1,
    (coreSecond_iff d o htQ ht hnt p.1.property.1 p.1.property.2.1).mp p.1.property.2.2,
    p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The source product counts give the actual half-order fiber count:
each of the twelve second-class elements contributes four plus sixteen. -/
public theorem kappa_eq_of_local_data (h : Hypotheses z) (d : FusionEightData z)
    (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (p : ProductData z t) : kappa z t z = 240 := by
  classical
  have htF : t ∉ fusionCore z := fun hf =>
    hnt (d.fusion t hf (fun he => by simp [he] at ht))
  have hs : Nat.card (Slice z t) = 20 := by
    rw [← Nat.card_congr (productsEquivSlice h d a o htQ ht hnt), Nat.card_sum,
      p.core_products, p.outside_products]
  have hslice (y : CoreSecond z) : Nat.card (Slice z (y : G)) = 20 := by
    obtain ⟨c, hc⟩ := o.core_transitive ⟨t, htQ, ht, htF⟩ y
    rw [← hc, ← Nat.card_congr (sliceConjEquiv z t c)]
    exact hs
  let : Fintype (CoreSecond z) := Fintype.ofFinite _
  rw [kappa_def]
  simp only [← halfOrder_def]
  change Nat.card (Fiber z t z) = 240
  rw [Nat.card_congr (fiberEquivSigma h d a o htQ ht hnt), Nat.card_sigma]
  simp only [hslice, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, o.core_card]
  norm_num

/-- Conditional assembly of 2.7 and 4.3. The local orbit and product producers
must discharge both extra premises before this is a source census theorem. -/
public theorem localInvolutionCensus_of_local_data (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (p : ProductData z t) : LocalInvolutionCensus z t where
  classes := two_classes_of_orbits h d a o htQ ht hnt
  count_at_z := kappa_eq_of_local_data h d a o htQ ht hnt p

/-- The core contribution is proved from the original local hypotheses.
Only the orbit profile and the outside-core product count remain explicit. -/
public theorem localInvolutionCensus_of_orbits_of_outside_count (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) (o : OrbitData z a.u)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (hp : Nat.card (OutsideProducts z t) = 16) : LocalInvolutionCensus z t :=
  localInvolutionCensus_of_local_data h d a o htQ ht hnt
    ⟨core_products_card h d htQ ht hnt, hp⟩

/-- The two ambient involution classes and the source count `12 * (4 + 16)`.
Relative quaternion normality supplies the local orbits and product counts;
the selected configuration supplies the necessary ambient fusion of `u`.
No orbit profile, product count, ambient order or simplicity is assumed. -/
public theorem localInvolutionCensus_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SelectedFusionData h)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    LocalInvolutionCensus z t := by
  have o := orbitData_of_quaternion_normal h hn d a
  exact localInvolutionCensus_of_orbits_of_outside_count h d a o htQ ht hnt
    (outside_products_card h hn d a o htQ ht hnt)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
