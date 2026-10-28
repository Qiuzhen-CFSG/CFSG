module

public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Recognition of a four-group with a transitive cubic complement

Let U have order four and let a subgroup X of order three normalize U
and act transitively on its nonidentity elements. Their join has order
12. Its action on the four cosets of X is faithful: a nontrivial kernel
would make X normal, hence force X to commute with the disjoint normal
subgroup U, contradicting transitivity. The image has index two in S₄,
so it is the actual alternating group A₄.

Independently, U is a normal Sylow two-subgroup of the join, and hence
its intrinsic two-core. Transport through the constructed equivalence
retains the literal ambient embedding of this core. Order four and the
cubic action suffice; no elementary-abelian hypothesis is required.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260,
the identification of X₃U(t) with A₄.
-/

public section

open Subgroup
namespace AlternatingFourTransitiveCubic
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_not_normal (U X : Subgroup G)
    (hU : Nat.card U = 4) (hX : Nat.card X = 3)
    (hn : X ≤ normalizer (U : Set G))
    (ht : ∀ u ∈ U, u ≠ 1 → ∀ v ∈ U, v ≠ 1 →
      ∃ x : X, (x : G) * u * (x : G)⁻¹ = v) :
    ¬ (X.subgroupOf (U ⊔ X)).Normal := by
  intro hnormal
  let J := U ⊔ X
  let U₀ := U.subgroupOf J
  let X₀ := X.subgroupOf J
  have hUn : U₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le U.le_normalizer hn)
  have hd : Disjoint U X := disjoint_of_coprime_natCard (by rw [hU, hX]; decide)
  have hd₀ : Disjoint U₀ X₀ := by
    apply disjoint_iff_inf_le.mpr
    intro a ha
    apply Subtype.ext
    exact hd.le_bot ⟨ha.1, ha.2⟩
  have hc (u : U) (x : X) : (x : G) * (u : G) * (x : G)⁻¹ = u := by
    have h := commute_of_normal_of_disjoint X₀ U₀ hnormal hUn hd₀.symm
      (⟨x, mem_sup_right x.property⟩ : J) (⟨u, mem_sup_left u.property⟩ : J)
      x.property u.property
    have h' := congrArg Subtype.val h.eq
    change (x : G) * (u : G) = (u : G) * (x : G) at h'
    rw [h', mul_inv_cancel_right]
  have hthree : 3 ≤ ENat.card U := by rw [ENat.card_eq_coe_natCard, hU]; norm_num
  obtain ⟨u, hu, _⟩ := ENat.exists_ne_ne_of_three_le hthree (1 : U) 1
  obtain ⟨v, hv, hvu⟩ := ENat.exists_ne_ne_of_three_le hthree (1 : U) u
  obtain ⟨x, hx⟩ := ht u u.property (fun h => hu (Subtype.ext h))
    v v.property (fun h => hv (Subtype.ext h))
  exact hvu (Subtype.ext (hx.symm.trans (hc u x)))

private theorem cubic_normalCore_eq_bot (U X : Subgroup G)
    (hU : Nat.card U = 4) (hX : Nat.card X = 3)
    (hn : X ≤ normalizer (U : Set G))
    (ht : ∀ u ∈ U, u ≠ 1 → ∀ v ∈ U, v ≠ 1 →
      ∃ x : X, (x : G) * u * (x : G)⁻¹ = v) :
    (X.subgroupOf (U ⊔ X)).normalCore = ⊥ := by
  let Y := X.subgroupOf (U ⊔ X)
  have hY : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show X ≤ U ⊔ X from le_sup_right)).toEquiv).trans hX
  have hd := card_dvd_of_le Y.normalCore_le
  rw [hY] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hb | he
  · exact Y.normalCore.eq_bot_iff_card.mpr hb
  · have heq : Y.normalCore = Y := eq_of_le_of_card_ge Y.normalCore_le (by omega)
    have hnorm : Y.Normal := heq ▸ Y.normalCore_normal
    exact False.elim (cubic_not_normal U X hU hX hn ht hnorm)

omit [Finite G] in
private theorem join_card (U X : Subgroup G)
    (hU : Nat.card U = 4) (hX : Nat.card X = 3)
    (hn : X ≤ normalizer (U : Set G)) : Nat.card (U ⊔ X : Subgroup G) = 12 := by
  have hd : Disjoint U X := disjoint_of_coprime_natCard (by rw [hU, hX]; decide)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint U X hn hd, hU, hX]

/-- The four-coset action identifies a transitive cubic extension with A₄. -/
theorem nonempty_equiv (U X : Subgroup G)
    (hU : Nat.card U = 4) (hX : Nat.card X = 3)
    (hn : X ≤ normalizer (U : Set G))
    (ht : ∀ u ∈ U, u ≠ 1 → ∀ v ∈ U, v ≠ 1 →
      ∃ x : X, (x : G) * u * (x : G)⁻¹ = v) :
    Nonempty ((U ⊔ X : Subgroup G) ≃* alternatingGroup (Fin 4)) := by
  classical
  let J := U ⊔ X
  let Y := X.subgroupOf J
  have hJ : Nat.card J = 12 := join_card U X hU hX hn
  have hY : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show X ≤ U ⊔ X from le_sup_right)).toEquiv).trans hX
  have hindex : Y.index = 4 := by
    have hh := Y.index_mul_card
    rw [hY, hJ] at hh
    omega
  let e : (J ⧸ Y) ≃ Fin 4 := Finite.equivFinOfCardEq hindex
  let f : J →* Equiv.Perm (Fin 4) := e.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom J (J ⧸ Y))
  have hi : Function.Injective f := e.permCongrHom.injective.comp <|
    (MonoidHom.ker_eq_bot_iff _).mp (by
      rw [← Y.normalCore_eq_ker]
      exact cubic_normalCore_eq_bot U X hU hX hn ht)
  have hr : Nat.card f.range = 12 := (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hJ
  have hri : f.range.index = 2 := by
    have hh := f.range.index_mul_card
    rw [hr] at hh
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh
    omega
  exact ⟨(MonoidHom.ofInjective hi).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hri))⟩

omit [Finite G] in
/-- The normal four-subgroup is the intrinsic two-core of the join. -/
theorem twoCore_eq (U X : Subgroup G)
    (hU : Nat.card U = 4) (hX : Nat.card X = 3)
    (hn : X ≤ normalizer (U : Set G)) :
    pCore 2 (U ⊔ X : Subgroup G) = U.subgroupOf (U ⊔ X) := by
  let J := U ⊔ X
  let V := U.subgroupOf J
  let : V.Normal := normal_subgroupOf_of_le_normalizer (sup_le U.le_normalizer hn)
  have hV : Nat.card V = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show U ≤ U ⊔ X from le_sup_left)).toEquiv).trans hU
  have hp : IsPGroup 2 V := IsPGroup.of_card (n := 2) hV
  have hindex : V.index = 3 := by
    have hh := V.index_mul_card
    rw [hV, join_card U X hU hX hn] at hh
    omega
  have hodd : ¬ 2 ∣ V.index := by rw [hindex]; decide
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal (hp.toSylow hodd))
    (le_sSup ⟨inferInstance, hp⟩)

/-- Recognition with the literal embedding of the two-core retained. -/
theorem exists_marked_equiv (U X : Subgroup G)
    (hU : Nat.card U = 4) (hX : Nat.card X = 3)
    (hn : X ≤ normalizer (U : Set G))
    (ht : ∀ u ∈ U, u ≠ 1 → ∀ v ∈ U, v ≠ 1 →
      ∃ x : X, (x : G) * u * (x : G)⁻¹ = v) :
    ∃ e : (U ⊔ X : Subgroup G) ≃* alternatingGroup (Fin 4),
      (pCore 2 (alternatingGroup (Fin 4))).map
        ((U ⊔ X).subtype.comp e.symm.toMonoidHom) = U := by
  obtain ⟨e⟩ := nonempty_equiv U X hU hX hn ht
  refine ⟨e, ?_⟩
  rw [← map_map, pCore_map_iso, twoCore_eq U X hU hX hn,
    map_subgroupOf_eq_of_le (show U ≤ U ⊔ X from le_sup_left)]

end AlternatingFourTransitiveCubic
