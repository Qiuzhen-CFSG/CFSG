module

public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupAction.FourAutomorphismOrbit

/-!
# Odd fusion excludes an invariant involution line in a four-group

A nonidentity odd-order automorphism of a group of order four fixes no
nonidentity element: a point stabilizer in its automorphism group has order
at most two. An invariant subgroup of order two would supply a fixed point.

The ambient version keeps both subgroups and the conjugating element. If g
normalizes E and X, has odd order, and moves an element of E, then no
characteristic subgroup of X of order two can lie in E. This is the
invariant-line contradiction for the covered sporadic cases in
Aschbacher–Smith, combined manuscript of 1 March 2004, 16.5.11, p.1199.
Identifying the line in a specific covering group remains model mathematics.
-/

namespace Theory.GroupAction

open Subgroup

/-- Killing a supplied Sylow two-subgroup forces every image element to
have odd order. No solvability or simplicity assumption is needed. -/
public theorem odd_order_map_of_sylow_le_ker
    {A B : Type*} [Group A] [Finite A] [Group B]
    (S : Sylow 2 A) (f : A →* B) (hS : (S : Subgroup A) ≤ f.ker) (a : A) :
    Odd (orderOf (f a)) := by
  have hn : ¬ 2 ∣ Nat.card f.range := by
    rw [← Subgroup.index_ker]
    exact fun h => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hS))
  have ho : Odd (Nat.card f.range) := (Nat.not_even_iff_odd).mp
    (fun h => hn (even_iff_two_dvd.mp h))
  apply ho.of_dvd_nat
  simpa only [← Subgroup.orderOf_coe] using
    orderOf_dvd_natCard (⟨f a, a, rfl⟩ : f.range)

/-- The normalizer of a Sylow two-subgroup acts with odd order on any
invariant subgroup centralized by that Sylow subgroup. Apply this to
E = Ω₁(Z(T)); the ambient conjugator itself need not have odd order. -/
public theorem normalizer_action_order_odd
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (E : Subgroup G)
    (hinv : normalizer (T : Set G) ≤ normalizer (E : Set G))
    (hcentral : (T : Subgroup G) ≤ centralizer (E : Set G))
    (g : normalizer (T : Set G)) :
    Odd (orderOf (E.normalizerMonoidHom ⟨(g : G), hinv g.property⟩)) := by
  let S := T.subtype (T : Subgroup G).le_normalizer
  let f := E.normalizerMonoidHom.comp (Subgroup.inclusion hinv)
  apply odd_order_map_of_sylow_le_ker S f _ g
  intro s hs
  change f s = 1
  ext x
  change (s : G) * (x : G) * (s : G)⁻¹ = x
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp (hcentral hs) x x.property).symm

/-- Odd-order nonidentity automorphisms of a group of order four have no
nonidentity fixed point. -/
public theorem odd_aut_card_four_fixed_point_free
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 4)
    (a : MulAut E) (hodd : Odd (orderOf a)) (hne : a ≠ 1)
    (x : E) (hx : x ≠ 1) : a x ≠ x := by
  intro hfix
  have hb := card_mulAut_subgroup_le_two_of_fixed_point hE x hx (zpowers a)
    (fun _ hb => smul_eq_self_of_mem_zpowers hb hfix)
  rw [Nat.card_zpowers] at hb
  obtain ⟨k, hk⟩ := hodd
  have hone : orderOf a = 1 := by omega
  exact hne (orderOf_eq_one_iff.mp hone)

/-- Consequently no line of order two is invariant under that automorphism. -/
public theorem odd_aut_card_four_no_invariant_two
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 4)
    (a : MulAut E) (hodd : Odd (orderOf a)) (hne : a ≠ 1)
    (Y : Subgroup E) (hY : Nat.card Y = 2)
    (hstable : ∀ y ∈ Y, a y ∈ Y) : False := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hY
  have hyne : (y : E) ≠ 1 := fun h => hy (Subtype.ext h)
  have hay : a (y : E) ∈ Y := hstable y y.property
  have hayne : (⟨a y, hay⟩ : Y) ≠ 1 := by
    intro h
    exact hyne (a.injective ((congrArg Subtype.val h).trans (map_one a).symm))
  exact odd_aut_card_four_fixed_point_free hE a hodd hne y hyne
    (congrArg Subtype.val (huniq _ hayne))

/-- Ambient characteristic-line obstruction. Neither E nor X is assumed
normal in the ambient group; only the specified conjugator normalizes them. -/
public theorem no_characteristic_two_in_four_of_odd_action
    {G : Type*} [Group G] [Finite G]
    (E X : Subgroup G) (hE : Nat.card E = 4)
    (Y : Subgroup X) [Y.Characteristic] (hY : Nat.card Y = 2)
    (hYE : Y.map X.subtype ≤ E) (g : G)
    (hgE : g ∈ normalizer (E : Set G)) (hgX : g ∈ normalizer (X : Set G))
    (hodd : Odd (orderOf (E.normalizerMonoidHom ⟨g, hgE⟩)))
    (z : E) (hmove : MulAut.conj g (z : G) ≠ z) : False := by
  let a : MulAut E := E.normalizerMonoidHom ⟨g, hgE⟩
  have hne : a ≠ 1 := by
    intro he
    apply hmove
    exact congrArg (fun b : MulAut E => ((b z : E) : G)) he
  let D := (Y.map X.subtype).subgroupOf E
  have hD : Nat.card D = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hYE).toEquiv,
      Subgroup.card_map_of_injective X.subtype_injective, hY]
  apply odd_aut_card_four_no_invariant_two hE a hodd hne D hD
  intro y hy
  have hn := normalizer_le_normalizer_characteristic_image X Y hgX
  exact (mem_normalizer_iff.mp hn (y : G)).mp hy

/-- An odd-order conjugator is a sufficient special case of odd induced
action, when that is how the conjugator was chosen. -/
public theorem no_characteristic_two_in_four_of_odd_conjugator
    {G : Type*} [Group G] [Finite G]
    (E X : Subgroup G) (hE : Nat.card E = 4)
    (Y : Subgroup X) [Y.Characteristic] (hY : Nat.card Y = 2)
    (hYE : Y.map X.subtype ≤ E) (g : G)
    (hgE : g ∈ normalizer (E : Set G)) (hgX : g ∈ normalizer (X : Set G))
    (hodd : Odd (orderOf g)) (z : E) (hmove : MulAut.conj g (z : G) ≠ z) : False := by
  apply no_characteristic_two_in_four_of_odd_action E X hE Y hY hYE g hgE hgX _ z hmove
  exact hodd.of_dvd_nat (by
    simpa only [← Subgroup.orderOf_coe] using
      orderOf_map_dvd E.normalizerMonoidHom ⟨g, hgE⟩)

/-- Every invariant predicate is constant on the nonidentity elements of
an elementary four-group moved by an odd-order automorphism. This also
applies to square-root existence, which is a set condition, not a subgroup. -/
public theorem odd_aut_card_four_invariant_predicate
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (a : MulAut E) (hodd : Odd (orderOf a)) (hne : a ≠ 1)
    (P : E → Prop) (hstable : ∀ x, P (a x) ↔ P x)
    (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) : P x ↔ P y := by
  let S : Subgroup (MulAut E) := {
    carrier := {b | ∀ w, P (b w) ↔ P w}
    one_mem' := fun _ => Iff.rfl
    mul_mem' := fun hb hc w => (hb _).trans (hc w)
    inv_mem' := by
      intro b hb w
      simpa only [MulAut.mul_apply, MulAut.apply_inv_self] using (hb (b⁻¹ w)).symm }
  have hle : zpowers a ≤ S := zpowers_le.mpr hstable
  have hcard : 2 < Nat.card (zpowers a) := by
    rw [Nat.card_zpowers]
    have hone : orderOf a ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup hE (zpowers a)
      hcard x hx y hy)
  have hp : P ((b : MulAut E) x) ↔ P x := hle b.property x
  rw [show (b : MulAut E) x = y from hb] at hp
  exact hp.symm

/-- Odd fusion inside E preserves square-root existence in every normalized
subgroup Q. In particular a two-element coset in E cannot contain exactly
one element that is a square in Q. -/
public theorem square_root_iff_of_odd_four_action
    {G : Type*} [Group G] [Finite G]
    (E Q : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (g : G) (hgE : g ∈ normalizer (E : Set G))
    (hgQ : g ∈ normalizer (Q : Set G))
    (hodd : Odd (orderOf (E.normalizerMonoidHom ⟨g, hgE⟩)))
    (z : E) (hmove : MulAut.conj g (z : G) ≠ z)
    (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    (∃ r ∈ Q, r ^ 2 = (x : G)) ↔ ∃ r ∈ Q, r ^ 2 = (y : G) := by
  let a : MulAut E := E.normalizerMonoidHom ⟨g, hgE⟩
  have hne : a ≠ 1 := by
    intro he
    exact hmove (congrArg (fun b : MulAut E => ((b z : E) : G)) he)
  apply odd_aut_card_four_invariant_predicate hE a hodd hne
    (fun w : E => ∃ r ∈ Q, r ^ 2 = (w : G)) _ x y hx hy
  intro w
  constructor
  · rintro ⟨r, hr, he⟩
    refine ⟨MulAut.conj g⁻¹ r,
      (mem_normalizer_iff.mp ((normalizer (Q : Set G)).inv_mem hgQ) r).mp hr, ?_⟩
    rw [← map_pow, he]
    change MulAut.conj g⁻¹ (MulAut.conj g (w : G)) = (w : G)
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨r, hr, he⟩
    refine ⟨MulAut.conj g r, (mem_normalizer_iff.mp hgQ r).mp hr, ?_⟩
    rw [← map_pow, he]
    rfl

/-- Specialization when the chosen ambient conjugator has odd order. -/
public theorem square_root_iff_of_odd_four_normalizer
    {G : Type*} [Group G] [Finite G]
    (E Q : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (g : G) (hgE : g ∈ normalizer (E : Set G))
    (hgQ : g ∈ normalizer (Q : Set G)) (hodd : Odd (orderOf g))
    (z : E) (hmove : MulAut.conj g (z : G) ≠ z)
    (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    (∃ r ∈ Q, r ^ 2 = (x : G)) ↔ ∃ r ∈ Q, r ^ 2 = (y : G) := by
  apply square_root_iff_of_odd_four_action E Q hE g hgE hgQ _ z hmove x y hx hy
  exact hodd.of_dvd_nat (by
    simpa only [← Subgroup.orderOf_coe] using
      orderOf_map_dvd E.normalizerMonoidHom ⟨g, hgE⟩)

end Theory.GroupAction
