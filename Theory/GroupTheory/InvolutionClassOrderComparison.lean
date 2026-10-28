module
public import Theory.GroupTheory.TwoInvolutionClassOrder
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.NormNum

/-!
# Thompson order comparison from involution centralizers

For two distinct involution classes, partition their mixed pairs by the
conjugacy class of the canonical half-order power. A complete irredundant
finite family of involution representatives gives Thompson's order formula
with one summand per class. There is no restriction to two classes.

Every pair in a fiber lies in the centralizer of its canonical involution.
Consequently an isomorphism of centralizers preserving the distinguished
involution and ambient membership in the two selected classes identifies the
actual fibers. Matching such data for every involution class determines the
group order, without assuming an ambient group isomorphism.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §F.4,
F.4.43, printed p. 296, referring to Aschbacher's (45.6). The proof is the
mixed-pair counting argument, extending `TwoInvolutionClassOrder`.
-/

open scoped BigOperators
namespace Theory.GroupTheory.InvolutionClassOrderComparison
open TwoInvolutionClassOrder
public section
variable {G : Type*} [Group G]

private theorem kappa_card (z v u : G) : kappa z v u = Nat.card (Fiber z v u) := by
  simp only [kappa_def, Fiber, halfOrder_def]

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
  simp only [← kappa_card]
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.cast_id]

/-- Partition mixed pairs by a complete irredundant family of involution classes. -/
theorem mixed_pair_count [Finite G] {I : Type*} [Fintype I]
    (z v : G) (u : I → G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hcomplete : ∀ a : G, orderOf a = 2 → ∃ i, IsConj (u i) a)
    (hirred : ∀ i j, IsConj (u i) (u j) → i = j) :
    Nat.card {p : G × G // IsConj z p.1 ∧ IsConj v p.2} =
      ∑ i, Nat.card {a : G // IsConj (u i) a} * kappa z v (u i) := by
  classical
  let f : (Σ i, {p : MixedPairs z v // IsConj (u i) (halfOrder p.val.1 p.val.2)}) →
      MixedPairs z v := fun p => p.2.val
  have hinj : Function.Injective f := by
    rintro ⟨i, p⟩ ⟨j, q⟩ h
    change p.val = q.val at h
    have hij : i = j := hirred i j (p.property.trans (h ▸ q.property.symm))
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext h)
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨i, hi⟩ := hcomplete _ (halfOrder_properties hz hv hn p.property.1 p.property.2).1
    exact ⟨⟨i, ⟨p, hi⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => card_class_part z v (u i))

private theorem class_card_rat [Finite G] (x : G) :
    (Nat.card {a : G // IsConj x a} : ℚ) =
      (Nat.card G : ℚ) / Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hc := ConjClasses.nat_card_carrier_mul_card_centralizer x
  have hn : (Nat.card (Subgroup.centralizer ({x} : Set G)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos.ne')
  apply (eq_div_iff hn).mpr
  exact_mod_cast hc

/-- Thompson's order formula for any finite complete irredundant class family. -/
theorem order_formula [Finite G] {I : Type*} [Fintype I]
    (z v : G) (u : I → G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hcomplete : ∀ a : G, orderOf a = 2 → ∃ i, IsConj (u i) a)
    (hirred : ∀ i j, IsConj (u i) (u j) → i = j) :
    (Nat.card G : ℚ) /
        (Nat.card (Subgroup.centralizer ({z} : Set G)) *
          Nat.card (Subgroup.centralizer ({v} : Set G))) =
      ∑ i, (kappa z v (u i) : ℚ) /
        Nat.card (Subgroup.centralizer ({u i} : Set G)) := by
  have hc := mixed_pair_count z v u hz hv hn hcomplete hirred
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
    (p := IsConj z) (q := IsConj v)), Nat.card_prod] at hc
  have hq : (Nat.card {a : G // IsConj z a} : ℚ) *
      Nat.card {a : G // IsConj v a} =
      ∑ i, (Nat.card {a : G // IsConj (u i) a} : ℚ) * kappa z v (u i) := by
    exact_mod_cast hc
  simp_rw [class_card_rat] at hq
  have hg : (Nat.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  apply mul_left_cancel₀ hg
  calc
    _ = (Nat.card G : ℚ) / Nat.card (Subgroup.centralizer ({z} : Set G)) *
        ((Nat.card G : ℚ) / Nat.card (Subgroup.centralizer ({v} : Set G))) := by ring
    _ = _ := hq
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
/-- An element regarded as a point of its own centralizer. -/
def centralizerPoint (u : G) : Subgroup.centralizer ({u} : Set G) :=
  ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[simp] theorem centralizerPoint_coe (u : G) : (centralizerPoint u : G) = u := by rfl

private abbrev CentralFiber (z v u : G) :=
  {p : Subgroup.centralizer ({u} : Set G) × Subgroup.centralizer ({u} : Set G) //
    IsConj z (p.1 : G) ∧ IsConj v (p.2 : G) ∧
      halfOrder p.1 p.2 = centralizerPoint u}

private noncomputable def fiberCentralEquiv [Finite G] (z v u : G)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v) :
    Fiber z v u ≃ CentralFiber z v u where
  toFun p := by
    have hm := fiber_mem_centralizer hz hv hn p
    let a : Subgroup.centralizer ({u} : Set G) := ⟨p.val.1, hm.1⟩
    let b : Subgroup.centralizer ({u} : Set G) := ⟨p.val.2, hm.2⟩
    exact ⟨(a, b), p.property.1, p.property.2.1,
      Subtype.ext ((halfOrder_coe _ a b).trans p.property.2.2)⟩
  invFun p := ⟨((p.val.1 : G), (p.val.2 : G)), p.property.1, p.property.2.1,
    (halfOrder_coe _ p.val.1 p.val.2).symm.trans
      (congrArg Subtype.val p.property.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A centralizer isomorphism preserving its distinguished point and ambient fusion
in the two selected classes identifies the actual mixed-pair fibers. -/
noncomputable def fiberEquiv [Finite G] {K : Type*} [Group K] [Finite K]
    (z v u : G) (z' v' u' : K)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hz' : orderOf z' = 2) (hv' : orderOf v' = 2) (hn' : ¬ IsConj z' v')
    (e : Subgroup.centralizer ({u} : Set G) ≃*
      Subgroup.centralizer ({u'} : Set K))
    (he : e (centralizerPoint u) = centralizerPoint u')
    (hfz : ∀ a : Subgroup.centralizer ({u} : Set G), IsConj z (a : G) ↔ IsConj z' (e a : K))
    (hfv : ∀ a : Subgroup.centralizer ({u} : Set G), IsConj v (a : G) ↔ IsConj v' (e a : K)) :
    Fiber z v u ≃ Fiber z' v' u' := by
  let ec : CentralFiber z v u ≃ CentralFiber z' v' u' :=
    Equiv.subtypeEquiv (Equiv.prodCongr e.toEquiv e.toEquiv) (by
      intro p
      change (_ ∧ _ ∧ _) ↔ (IsConj z' (e p.1 : K) ∧ IsConj v' (e p.2 : K) ∧
        halfOrder (e p.1) (e p.2) = centralizerPoint u')
      rw [← hfz, ← hfv, halfOrder_map, ← he, e.injective.eq_iff])
  exact (fiberCentralEquiv z v u hz hv hn).trans
    (ec.trans (fiberCentralEquiv z' v' u' hz' hv' hn').symm)

/-- The Thompson counts are determined by centralizers with the specified fusion data. -/
theorem kappa_eq [Finite G] {K : Type*} [Group K] [Finite K]
    (z v u : G) (z' v' u' : K)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hz' : orderOf z' = 2) (hv' : orderOf v' = 2) (hn' : ¬ IsConj z' v')
    (e : Subgroup.centralizer ({u} : Set G) ≃*
      Subgroup.centralizer ({u'} : Set K))
    (he : e (centralizerPoint u) = centralizerPoint u')
    (hfz : ∀ a : Subgroup.centralizer ({u} : Set G), IsConj z (a : G) ↔ IsConj z' (e a : K))
    (hfv : ∀ a : Subgroup.centralizer ({u} : Set G), IsConj v (a : G) ↔ IsConj v' (e a : K)) :
    kappa z v u = kappa z' v' u' := by
  rw [kappa_card, kappa_card]
  exact Nat.card_congr (fiberEquiv z v u z' v' u' hz hv hn hz' hv' hn' e he hfz hfv)

/-- Matching involution centralizers, distinguished involutions, and ambient fusion
in two distinct classes determine the group order. The class family may have any
finite size, so in particular this applies to three involution classes. -/
theorem card_eq_of_centralizer_equivs [Finite G]
    {K : Type*} [Group K] [Finite K] {I : Type*} [Fintype I]
    (u : I → G) (w : I → K)
    (hu : ∀ i, orderOf (u i) = 2) (hw : ∀ i, orderOf (w i) = 2)
    (hcomplete : ∀ a : G, orderOf a = 2 → ∃ i, IsConj (u i) a)
    (hcomplete' : ∀ a : K, orderOf a = 2 → ∃ i, IsConj (w i) a)
    (hirred : ∀ i j, IsConj (u i) (u j) → i = j)
    (hirred' : ∀ i j, IsConj (w i) (w j) → i = j)
    (i j : I) (hij : i ≠ j)
    (e : ∀ k, Subgroup.centralizer ({u k} : Set G) ≃*
      Subgroup.centralizer ({w k} : Set K))
    (he : ∀ k, e k (centralizerPoint (u k)) = centralizerPoint (w k))
    (hfi : ∀ k (a : Subgroup.centralizer ({u k} : Set G)),
      IsConj (u i) (a : G) ↔ IsConj (w i) (e k a : K))
    (hfj : ∀ k (a : Subgroup.centralizer ({u k} : Set G)),
      IsConj (u j) (a : G) ↔ IsConj (w j) (e k a : K)) :
    Nat.card G = Nat.card K := by
  have hn : ¬ IsConj (u i) (u j) := fun h => hij (hirred i j h)
  have hn' : ¬ IsConj (w i) (w j) := fun h => hij (hirred' i j h)
  have hc (k : I) : Nat.card (Subgroup.centralizer ({u k} : Set G)) =
      Nat.card (Subgroup.centralizer ({w k} : Set K)) := Nat.card_congr (e k).toEquiv
  have hk (k : I) : kappa (u i) (u j) (u k) = kappa (w i) (w j) (w k) :=
    kappa_eq _ _ _ _ _ _ (hu i) (hu j) hn (hw i) (hw j) hn'
      (e k) (he k) (hfi k) (hfj k)
  have hG := order_formula (u i) (u j) u (hu i) (hu j) hn hcomplete hirred
  have hK := order_formula (w i) (w j) w (hw i) (hw j) hn' hcomplete' hirred'
  simp_rw [hc, hk] at hG
  have hd : (Nat.card (Subgroup.centralizer ({w i} : Set K)) : ℚ) *
      Nat.card (Subgroup.centralizer ({w j} : Set K)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact_mod_cast (div_left_inj' hd).mp (hG.trans hK.symm)

end
end Theory.GroupTheory.InvolutionClassOrderComparison
