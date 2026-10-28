module
public import Theory.GroupTheory.InvolutionPairCentralInvolution
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring

/-!
# Thompson's order formula for two involution classes

Mixed pairs of involutions have a canonical central involution: the half-order
power of their product. Conjugation preserves this construction. Counting its
fibers over the two involution classes, and using the class-size formula, gives
Thompson's order formula. Full centralizer containment and control of fusion
then allow the same count inside a subgroup.

Source motivation: Parrott (1972), p. 684, the use of Thompson's order formula.
The proof here is the elementary mixed-pair counting argument.
-/

open scoped BigOperators

namespace Theory.GroupTheory.TwoInvolutionClassOrder

public section
variable {G : Type*} [Group G]

/-- The canonical half-order power of the product of two elements. -/
noncomputable def halfOrder (a b : G) : G := (a * b) ^ (orderOf (a * b) / 2)

/-- The defining equation, available without exposing the implementation body. -/
theorem halfOrder_def (a b : G) :
    halfOrder a b = (a * b) ^ (orderOf (a * b) / 2) := by rfl

/-- The mixed-pair fiber over `u`, with the two conjugacy classes specified. -/
abbrev Fiber (z v u : G) :=
  {p : G × G // IsConj z p.1 ∧ IsConj v p.2 ∧ halfOrder p.1 p.2 = u}

/-- Thompson's mixed-pair count. -/
noncomputable def kappa (z v u : G) : ℕ := Nat.card (Fiber z v u)

/-- The count is exactly the number of mixed pairs with the specified half-order power. -/
theorem kappa_def (z v u : G) :
    kappa z v u = Nat.card {p : G × G // IsConj z p.1 ∧ IsConj v p.2 ∧
      (p.1 * p.2) ^ (orderOf (p.1 * p.2) / 2) = u} := by rfl

/-- The half-order construction respects group isomorphisms. -/
theorem halfOrder_map {K : Type*} [Group K] (e : G ≃* K) (a b : G) :
    halfOrder (e a) (e b) = e (halfOrder a b) := by
  simp only [halfOrder, ← map_mul, e.orderOf_eq, map_pow]

private theorem orderOf_isConj {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

/-- Every mixed pair produces an involution commuting with both factors. -/
theorem halfOrder_properties [Finite G] {z v a b : G}
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (ha : IsConj z a) (hb : IsConj v b) :
    orderOf (halfOrder a b) = 2 ∧ Commute (halfOrder a b) a ∧
      Commute (halfOrder a b) b := by
  exact (half_order_involution_of_not_isConj a b
    ((orderOf_isConj ha).symm.trans hz) ((orderOf_isConj hb).symm.trans hv)
    (fun h => hn (ha.trans (h.trans hb.symm)))).2

private theorem conj_isConj_iff (g z a : G) :
    IsConj z (MulAut.conj g a) ↔ IsConj z a := by
  have h : IsConj a (MulAut.conj g a) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h' => h'.trans h.symm, fun h' => h'.trans h⟩

/-- Simultaneous conjugation gives an equivalence of the actual pair fibers. -/
noncomputable def fiberConjEquiv (z v g u : G) :
    Fiber z v u ≃ Fiber z v (MulAut.conj g u) := by
  apply Equiv.subtypeEquiv (Equiv.prodCongr (MulAut.conj g).toEquiv
    (MulAut.conj g).toEquiv)
  intro p
  change (_ ∧ _ ∧ _) ↔ (IsConj z (MulAut.conj g p.1) ∧
    IsConj v (MulAut.conj g p.2) ∧
    halfOrder (MulAut.conj g p.1) (MulAut.conj g p.2) = MulAut.conj g u)
  rw [conj_isConj_iff, conj_isConj_iff, halfOrder_map, (MulAut.conj g).injective.eq_iff]

/-- The fiber cardinality is constant on each conjugacy class. -/
theorem kappa_eq_of_isConj (z v : G) {u w : G} (h : IsConj u w) :
    kappa z v u = kappa z v w := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact Nat.card_congr (fiberConjEquiv z v g u)

/-- Every pair in the fiber over `u` lies in the full centralizer of `u`. -/
theorem fiber_mem_centralizer [Finite G] {z v u : G}
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (p : Fiber z v u) :
    p.val.1 ∈ Subgroup.centralizer ({u} : Set G) ∧
      p.val.2 ∈ Subgroup.centralizer ({u} : Set G) := by
  have h := halfOrder_properties hz hv hn p.property.1 p.property.2.1
  rw [p.property.2.2] at h
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr h.2.1.symm.eq,
    Subgroup.mem_centralizer_singleton_iff.mpr h.2.2.symm.eq⟩

private abbrev MixedPairs (z v : G) :=
  {p : G × G // IsConj z p.1 ∧ IsConj v p.2}

private noncomputable def classFiberEquiv (z v c : G) :
    (Σ u : {u : G // IsConj c u}, Fiber z v u.val) ≃
      {p : MixedPairs z v // IsConj c (halfOrder p.val.1 p.val.2)} where
  toFun p := ⟨⟨p.2.val, p.2.property.1, p.2.property.2.1⟩,
    p.2.property.2.2.symm ▸ p.1.property⟩
  invFun p := ⟨⟨halfOrder p.val.val.1 p.val.val.2, p.property⟩,
    ⟨p.val.val, p.val.property.1, p.val.property.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨u, hu⟩, ⟨⟨a, b⟩, ha, hb, he⟩⟩
    dsimp at he
    subst u
    rfl
  right_inv := by intro p; rfl

private theorem card_class_part [Finite G] (z v c : G) :
    Nat.card {p : MixedPairs z v // IsConj c (halfOrder p.val.1 p.val.2)} =
      Nat.card {u : G // IsConj c u} * kappa z v c := by
  classical
  let : Fintype {u : G // IsConj c u} := Fintype.ofFinite _
  rw [← Nat.card_congr (classFiberEquiv z v c), Nat.card_sigma]
  have hf (u : {u : G // IsConj c u}) : kappa z v u.val = kappa z v c :=
    (kappa_eq_of_isConj z v u.property).symm
  change (∑ u : {u : G // IsConj c u}, kappa z v u.val) = _
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.cast_id]

/-- Count mixed pairs by the two possible conjugacy classes of their canonical involution. -/
theorem mixed_pair_count [Finite G] (z v : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hclasses : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u) :
    Nat.card {p : G × G // IsConj z p.1 ∧ IsConj v p.2} =
      Nat.card {u : G // IsConj z u} * kappa z v z +
      Nat.card {u : G // IsConj v u} * kappa z v v := by
  classical
  have hiff (p : MixedPairs z v) :
      (¬ IsConj z (halfOrder p.val.1 p.val.2)) ↔
        IsConj v (halfOrder p.val.1 p.val.2) := by
    have hu := hclasses _ (halfOrder_properties hz hv hn p.property.1 p.property.2).1
    exact ⟨fun h => hu.resolve_left h, fun h h' => hn (h'.trans h.symm)⟩
  have hc := Nat.card_congr (Equiv.sumCompl
    (fun p : MixedPairs z v => IsConj z (halfOrder p.val.1 p.val.2)))
  rw [Nat.card_sum,
    Nat.card_congr (Equiv.subtypeEquivRight hiff),
    card_class_part, card_class_part] at hc
  exact hc.symm

/-- At least one of the two representative fibers is nonempty. -/
theorem kappa_pos_or [Finite G] (z v : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hclasses : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u) :
    0 < kappa z v z ∨ 0 < kappa z v v := by
  have hu := (halfOrder_properties hz hv hn (IsConj.refl z) (IsConj.refl v)).1
  have : Nonempty (Fiber z v (halfOrder z v)) :=
    ⟨⟨(z, v), IsConj.refl z, IsConj.refl v, rfl⟩⟩
  have hp : 0 < kappa z v (halfOrder z v) := Nat.card_pos
  rcases hclasses _ hu with h | h
  · exact Or.inl ((kappa_eq_of_isConj z v h).symm ▸ hp)
  · exact Or.inr ((kappa_eq_of_isConj z v h).symm ▸ hp)

/-- Thompson's order formula for a finite group with exactly two involution classes. -/
theorem card_eq [Finite G] (z v : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hclasses : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u) :
    Nat.card G = kappa z v z * Nat.card (Subgroup.centralizer ({v} : Set G)) +
      kappa z v v * Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  have hc := mixed_pair_count z v hz hv hn hclasses
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
    (p := IsConj z) (q := IsConj v)), Nat.card_prod] at hc
  have hzclass : Nat.card {u : G // IsConj z u} *
      Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card G :=
    ConjClasses.nat_card_carrier_mul_card_centralizer z
  have hvclass : Nat.card {u : G // IsConj v u} *
      Nat.card (Subgroup.centralizer ({v} : Set G)) = Nat.card G :=
    ConjClasses.nat_card_carrier_mul_card_centralizer v
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
  calc
    Nat.card G * Nat.card G =
        (Nat.card {u : G // IsConj z u} * Nat.card {u : G // IsConj v u}) *
          (Nat.card (Subgroup.centralizer ({z} : Set G)) *
            Nat.card (Subgroup.centralizer ({v} : Set G))) := by
      calc
        _ = (Nat.card {u : G // IsConj z u} *
              Nat.card (Subgroup.centralizer ({z} : Set G))) *
            (Nat.card {u : G // IsConj v u} *
              Nat.card (Subgroup.centralizer ({v} : Set G))) :=
          congrArg₂ (· * ·) hzclass.symm hvclass.symm
        _ = _ := by ring
    _ = (Nat.card {u : G // IsConj z u} *
          Nat.card (Subgroup.centralizer ({z} : Set G))) *
          (kappa z v z * Nat.card (Subgroup.centralizer ({v} : Set G))) +
        (Nat.card {u : G // IsConj v u} *
          Nat.card (Subgroup.centralizer ({v} : Set G))) *
          (kappa z v v * Nat.card (Subgroup.centralizer ({z} : Set G))) := by
      rw [hc]; ring
    _ = _ := by rw [hzclass, hvclass]; ring

/-- The canonical power computed in a subgroup is the same ambient element. -/
theorem halfOrder_coe (H : Subgroup G) (a b : H) :
    (↑(halfOrder a b) : G) = halfOrder (a : G) (b : G) := by
  simp only [halfOrder, ← Subgroup.coe_mul, Subgroup.orderOf_coe, Subgroup.coe_pow]

/-- A subgroup containing the full centralizer has exactly that centralizer internally. -/
def centralizerEquiv (H : Subgroup G) (u : H)
    (hC : Subgroup.centralizer ({(u : G)} : Set G) ≤ H) :
    Subgroup.centralizer ({u} : Set H) ≃
      Subgroup.centralizer ({(u : G)} : Set G) where
  toFun x := ⟨x.val.val, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.property))⟩
  invFun x := ⟨⟨x.val, hC x.property⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Fusion control and centralizer containment identify the actual pair fibers. -/
noncomputable def fiberSubgroupEquiv [Finite G] (H : Subgroup G) (z v u : H)
    (hz : orderOf (z : G) = 2) (hv : orderOf (v : G) = 2)
    (hn : ¬ IsConj (z : G) (v : G))
    (hC : Subgroup.centralizer ({(u : G)} : Set G) ≤ H)
    (hfz : ∀ a : H, IsConj z a ↔ IsConj (z : G) (a : G))
    (hfv : ∀ a : H, IsConj v a ↔ IsConj (v : G) (a : G)) :
    Fiber z v u ≃ Fiber (z : G) (v : G) (u : G) where
  toFun p := ⟨((p.val.1 : G), (p.val.2 : G)),
    H.subtype.map_isConj p.property.1, H.subtype.map_isConj p.property.2.1,
    (halfOrder_coe H p.val.1 p.val.2).symm.trans
      (congrArg Subtype.val p.property.2.2)⟩
  invFun p := by
    have hm := fiber_mem_centralizer hz hv hn p
    let a : H := ⟨p.val.1, hC hm.1⟩
    let b : H := ⟨p.val.2, hC hm.2⟩
    exact ⟨(a, b), (hfz a).mpr p.property.1, (hfv b).mpr p.property.2.1,
      Subtype.ext ((halfOrder_coe H a b).trans p.property.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Thompson counts do not change on restricting to such a subgroup. -/
theorem kappa_subgroup_eq [Finite G] (H : Subgroup G) (z v u : H)
    (hz : orderOf (z : G) = 2) (hv : orderOf (v : G) = 2)
    (hn : ¬ IsConj (z : G) (v : G))
    (hC : Subgroup.centralizer ({(u : G)} : Set G) ≤ H)
    (hfz : ∀ a : H, IsConj z a ↔ IsConj (z : G) (a : G))
    (hfv : ∀ a : H, IsConj v a ↔ IsConj (v : G) (a : G)) :
    kappa z v u = kappa (z : G) (v : G) (u : G) :=
  Nat.card_congr (fiberSubgroupEquiv H z v u hz hv hn hC hfz hfv)

/-- A subgroup containing representatives and their full centralizers, and controlling
fusion of both involution classes, is the whole group. -/
theorem eq_top_of_centralizers_le [Finite G] (H : Subgroup G) (z v : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hclasses : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj v u)
    (hzH : z ∈ H) (hvH : v ∈ H)
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hCv : Subgroup.centralizer ({v} : Set G) ≤ H)
    (hfz : ∀ a : H, IsConj (⟨z, hzH⟩ : H) a ↔ IsConj z (a : G))
    (hfv : ∀ a : H, IsConj (⟨v, hvH⟩ : H) a ↔ IsConj v (a : G)) :
    H = ⊤ := by
  let zH : H := ⟨z, hzH⟩
  let vH : H := ⟨v, hvH⟩
  have hz2 : orderOf zH = 2 := (Subgroup.orderOf_coe zH).symm.trans hz
  have hv2 : orderOf vH = 2 := (Subgroup.orderOf_coe vH).symm.trans hv
  have hnH : ¬ IsConj zH vH := fun h => hn (H.subtype.map_isConj h)
  have hclassesH (u : H) (hu : orderOf u = 2) : IsConj zH u ∨ IsConj vH u := by
    rcases hclasses u ((Subgroup.orderOf_coe u).trans hu) with h | h
    · exact Or.inl ((hfz u).mpr h)
    · exact Or.inr ((hfv u).mpr h)
  have hH := card_eq zH vH hz2 hv2 hnH hclassesH
  rw [kappa_subgroup_eq H zH vH zH hz hv hn hCz hfz hfv,
    kappa_subgroup_eq H zH vH vH hz hv hn hCv hfz hfv,
    Nat.card_congr (centralizerEquiv H zH hCz),
    Nat.card_congr (centralizerEquiv H vH hCv)] at hH
  exact H.eq_top_of_card_eq (hH.trans (card_eq z v hz hv hn hclasses).symm)

end
end Theory.GroupTheory.TwoInvolutionClassOrder
