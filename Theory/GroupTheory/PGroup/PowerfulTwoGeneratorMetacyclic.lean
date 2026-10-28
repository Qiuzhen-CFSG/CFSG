module

public import Mathlib.Data.Set.Finite.Lemmas
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupTheory.PGroup.PowerfulTwoGeneratorCyclicDerived
public import Theory.GroupTheory.PGroup.PowerfulTwoGeneratorRoots

/-!
# Metacyclic witnesses from cyclic derived subgroups and Frattini roots

For a two-generated finite two-group, a cyclic derived subgroup and square-root
extraction on the Frattini subgroup suffice to construct a cyclic normal
subgroup with cyclic quotient.

Choose a generator of the derived subgroup and a cyclic overgroup of maximal
element order. Square-root extraction forces its generator outside the Frattini
subgroup. The elementary abelian Frattini quotient has at most four elements,
so this generator extends to a generating pair. Its cyclic subgroup contains
the derived subgroup, hence is normal, and the other generator generates the
quotient. The trivial derived subgroup is handled directly.

This is the final, elementary part of the powerful two-generator argument in
Traustason–Williams, *Powerfully nilpotent groups of rank 2 or small order*,
Section 2, https://arxiv.org/abs/2002.02694. The theorem below states the cyclicity
and square-root premises explicitly; deriving them from powerfulness is the
separate powerful-group input to this argument.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

/-- A non-Frattini element extends to a generating pair in a two-generated two-group. -/
private theorem extend_pair {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (a b c : Q)
    (hgen : zpowers a ⊔ zpowers b = ⊤) (hc : c ∉ frattini Q) :
    ∃ d : Q, zpowers c ⊔ zpowers d = ⊤ := by
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let F := frattini Q
  let q := QuotientGroup.mk' F
  let : IsElementaryAbelian 2 (Q ⧸ F) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  let : CommGroup (Q ⧸ F) := IsMulCommutative.instCommGroup
  have hqgen : zpowers (q a) ⊔ zpowers (q b) = ⊤ := by
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.map_sup, hgen]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective F)
  have hpair : closure ({q a, q b} : Set (Q ⧸ F)) = ⊤ := by
    rw [show ({q a, q b} : Set (Q ⧸ F)) = {q a} ∪ {q b} from rfl,
      closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
    exact hqgen
  have hsquare (x : Q ⧸ F) : x * x = 1 := by
    simpa [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Q ⧸ F)) x
  have hc1 : q c ≠ 1 := fun h => hc ((QuotientGroup.eq_one_iff c).mp h)
  have lift_pair (d : Q) (hd : zpowers (q c) ⊔ zpowers (q d) = ⊤) :
      zpowers c ⊔ zpowers d = ⊤ := by
    apply frattini_nongenerating
    have hm : (zpowers c ⊔ zpowers d).map q = ⊤ := by
      simpa only [Subgroup.map_sup, MonoidHom.map_zpowers] using hd
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using
      congrArg (comap q) hm
  have hforms := (mem_closure_pair_iff (q a) (q b) (hsquare _) (hsquare _)
    (Commute.all _ _) (q c)).mp (hpair ▸ mem_top _)
  rcases hforms with h | h | h | h
  · exact (hc1 h).elim
  · exact ⟨b, lift_pair b (h ▸ hqgen)⟩
  · exact ⟨a, lift_pair a (by rw [h, sup_comm]; exact hqgen)⟩
  · refine ⟨b, lift_pair b ?_⟩
    apply top_unique
    rw [← hqgen]
    refine sup_le (zpowers_le.mpr ?_) le_sup_right
    have hm := (zpowers (q c) ⊔ zpowers (q b)).mul_mem
      ((le_sup_left : zpowers (q c) ≤ zpowers (q c) ⊔ zpowers (q b)) (mem_zpowers (q c)))
      ((le_sup_right : zpowers (q b) ≤ zpowers (q c) ⊔ zpowers (q b)) (mem_zpowers (q b)))
    simpa only [h, mul_assoc, hsquare, mul_one] using hm

/-- A generating pair whose first cyclic subgroup contains the derived subgroup gives a witness. -/
private theorem witness {Q : Type*} [Group Q] (c d : Q)
    (hgen : zpowers c ⊔ zpowers d = ⊤)
    (hD : _root_.commutator Q ≤ zpowers c) :
    ∃ (N : Subgroup Q) (_ : N.Normal), IsCyclic N ∧ IsCyclic (Q ⧸ N) := by
  let N := zpowers c
  let : N.Normal := ⟨fun n hn g => by
    have hm := N.mul_mem (hD (commutator_mem_commutator (mem_top g) (mem_top n))) hn
    simpa [commutatorElement_def, mul_assoc] using hm⟩
  refine ⟨N, inferInstance, inferInstance, ?_⟩
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨QuotientGroup.mk' N d, ?_⟩
  have hm := congrArg (map (QuotientGroup.mk' N)) hgen
  have hc : (zpowers c).map (QuotientGroup.mk' N) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  simpa only [Subgroup.map_sup, hc, bot_sup_eq, MonoidHom.map_zpowers,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using hm

/-- Maximal element order makes square-root extraction terminate outside Frattini. -/
private theorem primitive_root {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (hroot : ∀ x ∈ frattini Q, ∃ y : Q, y ^ 2 = x)
    (x : Q) (hx : x ≠ 1) :
    ∃ c : Q, c ∉ frattini Q ∧ x ∈ zpowers c := by
  obtain ⟨c, hc, hmax⟩ := Set.exists_max_image {c : Q | x ∈ zpowers c}
    orderOf (Set.toFinite _) ⟨x, mem_zpowers x⟩
  refine ⟨c, ?_, hc⟩
  intro hcF
  obtain ⟨y, hy⟩ := hroot c hcF
  have hcy : zpowers c ≤ zpowers y := zpowers_le.mpr (hy ▸ pow_mem (mem_zpowers y) 2)
  have hy1 : y ≠ 1 := by
    intro h
    have hc1 : c = 1 := by simpa [h] using hy.symm
    exact hx (by simpa [hc1] using hc)
  have hle := hmax y (hcy hc)
  have hlt : orderOf c < orderOf y := by
    rw [← hy, orderOf_pow_of_dvd (by decide : (2 : ℕ) ≠ 0) (hQ.dvd_orderOf hy1)]
    exact Nat.div_lt_self (orderOf_pos y) (by decide)
  exact (not_lt_of_ge hle) hlt

/-- A two-generated finite two-group is metacyclic if its derived subgroup is cyclic
and every Frattini element admits a square root in the ambient group. -/
public theorem IsPGroup.exists_cyclic_normal_cyclic_quotient_of_cyclic_derived_of_frattini_square_roots {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (a b : Q) (hgen : zpowers a ⊔ zpowers b = ⊤)
    (hD : IsCyclic (_root_.commutator Q))
    (hroot : ∀ x ∈ frattini Q, ∃ y : Q, y ^ 2 = x) :
    ∃ (N : Subgroup Q) (_ : N.Normal), IsCyclic N ∧ IsCyclic (Q ⧸ N) := by
  obtain ⟨x, hx⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (_root_.commutator Q)).mp hD
  by_cases hx1 : x = 1
  · apply witness a b hgen
    rw [← hx, hx1]
    simp
  · obtain ⟨c, hc, hxc⟩ := primitive_root hQ hroot x hx1
    obtain ⟨d, hcd⟩ := extend_pair hQ a b c hgen hc
    apply witness c d hcd
    rw [← hx]
    exact zpowers_le.mpr hxc

/-- A finite two-generated powerful two-group is metacyclic. -/
public theorem IsPGroup.exists_cyclic_normal_cyclic_quotient_of_le_fourthPowers
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (hpower : _root_.commutator Q ≤
      Subgroup.closure (Set.range (fun x : Q => x ^ (4 : ℕ))))
    (a b : Q) (hgen : Subgroup.zpowers a ⊔ Subgroup.zpowers b = ⊤) :
    ∃ (N : Subgroup Q) (_ : N.Normal), IsCyclic N ∧ IsCyclic (Q ⧸ N) := by
  apply hQ.exists_cyclic_normal_cyclic_quotient_of_cyclic_derived_of_frattini_square_roots
    a b hgen
  · exact hQ.isCyclic_commutator_of_le_fourthPowers hpower a b hgen
  · intro x hx
    exact hQ.exists_square_eq_of_mem_frattini_of_commutator_le_fourthPowers hpower hx
