module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Outer automorphism groups and the class `Alt`

This module hosts the general machinery of the **Schreier property** (GLS vol. 3,
Theorem 7.1.1(a)) that is shared between the families of known simple groups:

* the inner and outer automorphism groups (`innerAutGroup`, `Out`), the kernel of
  the conjugation action on a normal subgroup (`conjNormal_ker`), and
  functoriality of `Out` under group isomorphisms (`outCongr`);
* the lemma that a finite group of order at most four is solvable
  (`isSolvable_of_card_le_four`), the smallness mechanism behind the `Alt ∪ Spor`
  arm of the Schreier property;
* the class `Alt` of alternating groups (`IsAltGroup`).  It is declared here
  rather than next to `IsChevGroup`/`IsSporGroup` in `GroupTheory.KGroup`
  because the alternating arm of the Schreier property is developed in
  `GroupTheory.AutAlternating`, which lies below `GroupTheory.KGroup` in the
  import graph; `GroupTheory.KGroup` imports this module and
  `GroupTheory.AutAlternating` and hosts the dispatch over `IsKnownSimpleGroup`.
-/

noncomputable section

namespace GroupTheory

universe u v

/-! ## The class `Alt` of alternating groups -/

/-- The class `Alt` of alternating groups. -/
public inductive IsAltGroup (S : Type u) [Group S] : Prop where
  | isAlternating (n : ℕ) (_ : 5 ≤ n) (e : S ≃* alternatingGroup (Fin n)) : IsAltGroup S

/-! ## The Schreier property (Chapter 4, Lemma 1.1(a)) -/

/-- The group of **inner automorphisms** of `G`, the image of the conjugation map
`G →* Aut(G)`.  `@[expose]`: the definitional unfolding is needed to reason about
membership in `Out(G)` (e.g. in `AutAlternating.isSolvable_Out_of_isAltGroup`). -/
@[expose]
public def innerAutGroup (G : Type u) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

/-- The inner automorphisms form a normal subgroup of the automorphism group. -/
public instance innerAutGroup_normal (G : Type u) [Group G] : (innerAutGroup G).Normal where
  conj_mem := by
    intro n hn g
    rcases (by simpa [innerAutGroup, MonoidHom.range_eq_map] using hn) with ⟨x, hxn⟩
    have h : MulAut.conj (g x) = g * MulAut.conj x * g⁻¹ := by
      ext y
      rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
        MulAut.inv_apply, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply]
    exact (by
      simpa [innerAutGroup, MonoidHom.range_eq_map] using
        (Subgroup.mem_map).2 ⟨g x, Subgroup.mem_top (g x), by rw [h, hxn]⟩)

/-- The **outer automorphism group** `Out(G) = Aut(G)/Inn(G)`. -/
public abbrev Out (G : Type u) [Group G] : Type u := MulAut G ⧸ innerAutGroup G

/-- `Out` is functorial: a group isomorphism `K ≃* A` induces an isomorphism of
outer automorphism groups `Out K ≃* Out A`.  This is the transfer used by the
Schreier property (GLS vol. 3, Theorem 7.1.1(a)): solvability of `Out` is
invariant under isomorphism. -/
public noncomputable def outCongr {K : Type u} {A : Type v} [Group K] [Group A]
    (e : K ≃* A) : Out K ≃* Out A := by
  classical
  -- the induced isomorphism of automorphism groups (conjugation by `e`)
  let eAut : MulAut K ≃* MulAut A :=
    { toFun := fun f : MulAut K =>
        ⟨(e.symm.toEquiv.trans f.toEquiv).trans e.toEquiv, by
          intro x y
          simp [map_mul]⟩
      invFun := fun g : MulAut A =>
        ⟨(e.toEquiv.trans g.toEquiv).trans e.symm.toEquiv, by
          intro x y
          simp [map_mul]⟩
      left_inv := by
        intro f
        ext x
        simp
      right_inv := by
        intro g
        ext x
        simp
      map_mul' := by
        intro f g
        ext x
        simp [MulAut.mul_apply] }
  have he : Subgroup.map eAut.toMonoidHom (innerAutGroup K) = innerAutGroup A := by
    apply le_antisymm
    · intro w hw
      rw [Subgroup.mem_map] at hw
      rcases hw with ⟨z, hz, rfl⟩
      unfold innerAutGroup at hz
      rcases (MonoidHom.mem_range).1 hz with ⟨k, hk⟩
      unfold innerAutGroup
      rw [MonoidHom.mem_range]
      refine ⟨e k, ?_⟩
      -- eAut (conj k) = conj (e k)
      rw [← hk]
      ext x
      dsimp [eAut]
      simp [map_mul, map_inv]
    · intro w hw
      unfold innerAutGroup at hw
      rcases (MonoidHom.mem_range).1 hw with ⟨a, ha⟩
      rw [Subgroup.mem_map]
      refine ⟨MulAut.conj (e.symm a), ?_, ?_⟩
      · unfold innerAutGroup
        rw [MonoidHom.mem_range]
        exact ⟨e.symm a, rfl⟩
      · -- eAut (conj (e⁻¹ a)) = conj a
        rw [← ha]
        ext x
        dsimp [eAut]
        simp [map_mul, map_inv]
  exact QuotientGroup.congr (innerAutGroup K) (innerAutGroup A) eAut he

/-- The kernel of the conjugation action of `G` on its normal subgroup `K` is the
centralizer of `K` in `G`. -/
public theorem conjNormal_ker {G : Type u} [Group G] {K : Subgroup G} [K.Normal] :
    (MulAut.conjNormal (H := K)).ker = Subgroup.centralizer (K : Set G) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 : MulAut.conjNormal x ⟨k, hk⟩ = ⟨k, hk⟩ := by
      have h1' := congrArg (fun e : MulAut K => e ⟨k, hk⟩) hx
      rw [MulAut.one_apply] at h1'
      exact h1'
    have h : x * k * x⁻¹ = k := by
      exact (MulAut.conjNormal_apply x ⟨k, hk⟩).symm.trans (congrArg Subtype.val h1)
    calc
      k * x = (x * k * x⁻¹) * x := by rw [h]
      _ = x * k := by simp [mul_assoc]
  · intro hx
    ext k
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hx' : (k : G) * x = x * (k : G) := (Subgroup.mem_centralizer_iff.mp hx) (k : G) k.2
    calc
      x * (k : G) * x⁻¹ = ((k : G) * x) * x⁻¹ := by rw [hx']
      _ = (k : G) := by simp [mul_assoc]

/-- Conjugation by an element of a subgroup, viewed as an automorphism of the
subgroup, is the restriction of conjugation in the ambient group: for `x ∈ K`,
`conjNormal x` agrees with `conj x`. -/
public theorem conjNormal_eq_conj {G : Type u} [Group G] {K : Subgroup G} [K.Normal]
    (x : K) : MulAut.conjNormal (H := K) (x : G) = MulAut.conj x := by
  ext y
  change (x : G) * (y : G) * (x : G)⁻¹ = (x : G) * (y : G) * (x : G)⁻¹
  rfl

/-- A homomorphism with trivial kernel is injective. -/
public theorem injective_of_ker_eq_bot {G N : Type u} [Group G] [Group N] (f : G →* N)
    (h : f.ker = ⊥) : Function.Injective f := by
  intro x y hxy
  have : x * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    simp
  have hxy' : x * y⁻¹ = 1 := by
    have : x * y⁻¹ ∈ (⊥ : Subgroup G) := by simpa [h] using this
    exact (Subgroup.mem_bot).1 this
  simpa [mul_assoc] using congrArg (fun t : G => t * y) hxy'

/-- A finite group of order at most four is solvable.  This is the mechanism behind
the alternating and sporadic arm of the Schreier property: GLS vol. 3, Theorem
7.1.1(a) proves `|Out(K)| ≤ 4` for `K ∈ Alt ∪ Spor` (via Theorem 5.2.1 — `Aut(Aₙ) = Sₙ`
for `n ≥ 5`, `n ≠ 6`, and `Aut(A₆)` contains `S₆` with index two — and Table 5.3 for
the sporadic groups), and the solvability follows from this smallness. -/
public theorem isSolvable_of_card_le_four {G : Type u} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsSolvable G := by
  by_cases h1 : Nat.card G = 1
  · have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    haveI := hsub
    exact isSolvable_of_subsingleton G
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hge2 : 2 ≤ Nat.card G := by omega
  by_cases htwo : ∀ x : G, x ≠ 1 → orderOf x = 2
  · -- every nonidentity element has order two, so `x² = 1` for all `x` and the group
    -- is commutative
    have hsq : ∀ x : G, x * x = 1 := by
      intro x
      by_cases hx : x = 1
      · simp [hx]
      · simpa [htwo x hx, pow_two] using (pow_orderOf_eq_one x)
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have hab : (a * b)⁻¹ = a * b := (eq_inv_of_mul_eq_one_right (hsq (a * b))).symm
      calc
        a * b = (a * b)⁻¹ := hab.symm
        _ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev]
        _ = b * a := by
          rw [← eq_inv_of_mul_eq_one_right (hsq a), ← eq_inv_of_mul_eq_one_right (hsq b)]
    letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    exact (inferInstance : IsSolvable G)
  · -- some nonidentity element has order different from two; since the order of an
    -- element divides the order of the group (≤ 4), its order is the order of the
    -- group, so the group is cyclic and commutative
    have hnot : ∃ x : G, x ≠ 1 ∧ orderOf x ≠ 2 := by
      by_contra h
      apply htwo
      intro x hx
      by_contra hord
      exact h ⟨x, hx, hord⟩
    rcases hnot with ⟨x, hxne, hord2⟩
    letI : Fintype G := Fintype.ofFinite G
    have hdiv : orderOf x ∣ Nat.card G := by
      rw [Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    have hord : orderOf x = Nat.card G := by
      have hne1 : orderOf x ≠ 1 := by
        intro h
        exact hxne ((orderOf_eq_one_iff).1 h)
      have hne0 : orderOf x ≠ 0 := by
        intro h
        rw [h] at hdiv
        rcases hdiv with ⟨k, hk⟩
        exact hpos.ne' (by rw [hk]; simp)
      have hge3 : 3 ≤ orderOf x := by omega
      have hle4 : orderOf x ≤ 4 := le_trans (Nat.le_of_dvd hpos hdiv) h
      have hcases : orderOf x = 3 ∨ orderOf x = 4 := by
        by_cases h3 : orderOf x = 3
        · exact Or.inl h3
        · right
          apply le_antisymm hle4
          have hge4 : 4 ≤ orderOf x := by omega
          exact hge4
      rcases hcases with h3 | h4
      · rcases hdiv with ⟨k, hk⟩
        rw [h3] at hk
        rw [h3, hk]
        have hk1 : k = 1 := by omega
        rw [hk1]
      · rcases hdiv with ⟨k, hk⟩
        rw [h4] at hk
        rw [h4, hk]
        have hk1 : k = 1 := by omega
        rw [hk1]
    have hz : Subgroup.zpowers x = ⊤ := by
      have hzcard : Nat.card (Subgroup.zpowers x) = Nat.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_zpowers]
        exact hord.trans Nat.card_eq_fintype_card
      exact Subgroup.eq_top_of_card_eq (Subgroup.zpowers x) hzcard
    have hcomm : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.zpowers x := by simp [hz]
      rcases (Subgroup.mem_zpowers_iff).1 ha with ⟨m, hm⟩
      have hb : b ∈ Subgroup.zpowers x := by simp [hz]
      rcases (Subgroup.mem_zpowers_iff).1 hb with ⟨n, hn⟩
      rw [← hm, ← hn]
      calc
        x ^ m * x ^ n = x ^ (m + n) := (zpow_add x m n).symm
        _ = x ^ (n + m) := congrArg (fun t : ℤ => x ^ t) (add_comm m n)
        _ = x ^ n * x ^ m := zpow_add x n m
    letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    exact (inferInstance : IsSolvable G)

end GroupTheory
