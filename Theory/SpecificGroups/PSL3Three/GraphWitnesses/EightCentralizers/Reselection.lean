module

public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.Reduction
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.FixedMonomial
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.SymmetricFour
public import Theory.SpecificGroups.PSL3Three.CandidateOrders

/-!
# Reselecting the outer involution in an elementary eight-subgroup

A centralizer splitting and the known inner two-rank bound identify the
inner intersection as an elementary four-group. If its full normalizer is
the first fixed S₄, multiply the chosen outer involution by a nonidentity
inner element. Were the four normal in the new fixed group, the two fixed
groups would coincide by their common order 24. This would make that inner
element central in S₄, a contradiction.

The final lemma transports the nonnormal-four cubic commutator through an
actual fixed-group isomorphism. Its witness retains the literal expression
`a c * c⁻¹`. The full normalizer and fixed-group isomorphism remain explicit
structural inputs here; their native construction belongs to separate modules.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10, including the change from g to the second outer involution g′.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers

theorem inner_four (B : Subgroup (MulAut PSL)) (hB : IsElementaryAbelian 2 B)
    (hcard : Nat.card B = 8) (b : MulAut PSL) (hb : b ∈ B)
    (hsplit : ∀ a : MulAut PSL, Commute a b →
      ∃ x : PSL, a = MulAut.conj x ∨ a = MulAut.conj x * b) :
    IsElementaryAbelian 2 (B.comap MulAut.conj) ∧
      Nat.card (B.comap MulAut.conj) = 4 ∧ B.comap MulAut.conj ≤ b.fixedSubgroup := by
  let : IsElementaryAbelian 2 B := hB
  have hinj := MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
  let D := B.comap MulAut.conj
  have he : IsElementaryAbelian 2 D := {
    toIsMulCommutative := B.comap_injective_isMulCommutative hinj
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      apply hinj
      change MulAut.conj ((x : PSL) ^ 2) = MulAut.conj (1 : PSL)
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (MulAut.conj (x : PSL)) x.property }
  have hbound := (primeRank_le_iff_elementary_card_le PSL).mp
    (Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le
      Nat.prime_three (by decide) (by simp)) D he
  have hcomm (a : MulAut PSL) (ha : a ∈ B) : Commute a b := by
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : B) ⟨b, hb⟩)
  let f : D × Bool → B := fun p => if p.2 then
    ⟨MulAut.conj p.1.val * b, B.mul_mem p.1.property hb⟩ else
    ⟨MulAut.conj p.1.val, p.1.property⟩
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x, hx | hx⟩ := hsplit a (hcomm a a.property)
    · exact ⟨(⟨x, show MulAut.conj x ∈ B from hx ▸ a.property⟩, false), Subtype.ext hx.symm⟩
    · have hxB : MulAut.conj x ∈ B := by
        have hh := B.mul_mem a.property (B.inv_mem hb)
        simpa only [hx, mul_inv_cancel_right] using hh
      exact ⟨(⟨x, hxB⟩, true), Subtype.ext hx.symm⟩
  have hcount := Nat.card_le_card_of_surjective f hf
  have hBool : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, hBool, hcard] at hcount
  refine ⟨he, ?_, ?_⟩
  · change Nat.card D = 4
    omega
  · intro x hx
    rw [MulAut.mem_fixedSubgroup]
    apply hinj
    have hconj : MulAut.conj (b x) = b * MulAut.conj x * b⁻¹ := by ext y; simp
    rw [hconj, ← (hcomm _ hx).eq, mul_inv_cancel_right]

theorem fixed_card_of_graph_conjugate (b : MulAut PSL)
    (h : ∃ u : MulAut PSL, b = u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹) :
    Nat.card b.fixedSubgroup = 24 := by
  obtain ⟨u, rfl⟩ := h
  have he : MulAut.congr u (Matrix.PSL3.OuterSolvable.graph (ZMod 3)) =
      u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹ := by ext x; rfl
  rw [← he, ← Nat.card_congr
    (MulAut.fixedSubgroupCongr u (Matrix.PSL3.OuterSolvable.graph (ZMod 3))).toEquiv,
    graph_fixed_eq_monomial, card_monomial]

theorem reselect_outer
    (hconj : ∀ b : MulAut PSL, orderOf b = 2 →
      b ∉ MulAut.innerSubgroup PSL → ∃ u : MulAut PSL,
        b = u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹)
    (B : Subgroup (MulAut PSL)) (hB : IsElementaryAbelian 2 B)
    (b : MulAut PSL) (hb : b ∈ B) (hout : b ∉ MulAut.innerSubgroup PSL)
    (D : Subgroup PSL) (hD : D ≤ b.fixedSubgroup)
    (hDB : D.map MulAut.conj ≤ B) (hnontrivial : D ≠ ⊥)
    (hnorm : normalizer (D : Set PSL) = b.fixedSubgroup)
    (hcenter : center b.fixedSubgroup = ⊥) :
    ∃ b' ∈ B, b' ∉ MulAut.innerSubgroup PSL ∧
      D ≤ b'.fixedSubgroup ∧ ¬ (D.subgroupOf b'.fixedSubgroup).Normal := by
  let : IsElementaryAbelian 2 B := hB
  have hinj := MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
  obtain ⟨d0, hd01⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnontrivial
  let d : PSL := d0
  have hd : d ∈ D := d0.property
  have hd1 : d ≠ 1 := fun h => hd01 (Subtype.ext h)
  have hdb : MulAut.conj d ∈ B := hDB ⟨d, hd, rfl⟩
  let b' := MulAut.conj d * b
  have hb' : b' ∈ B := B.mul_mem hdb hb
  have hout' : b' ∉ MulAut.innerSubgroup PSL := by
    intro h
    have h' := (MulAut.innerSubgroup PSL).mul_mem
      ((MulAut.innerSubgroup PSL).inv_mem ⟨d, rfl⟩) h
    exact hout (by simpa only [b', inv_mul_cancel_left] using h')
  have hle : D ≤ b'.fixedSubgroup := by
    intro x hx
    rw [MulAut.mem_fixedSubgroup]
    apply hinj
    have hc : Commute (MulAut.conj x) b' :=
      congrArg Subtype.val (mul_comm (⟨_, hDB ⟨x, hx, rfl⟩⟩ : B) ⟨_, hb'⟩)
    have he : MulAut.conj (b' x) = b' * MulAut.conj x * b'⁻¹ := by ext y; simp
    rw [he, ← hc.eq, mul_inv_cancel_right]
  refine ⟨b', hb', hout', hle, ?_⟩
  intro hnormal
  let : (D.subgroupOf b'.fixedSubgroup).Normal := hnormal
  have hle' : b'.fixedSubgroup ≤ b.fixedSubgroup := by
    rw [← hnorm]
    exact le_normalizer_of_normal_subgroupOf hle
  have horder (a : MulAut PSL) (ha : a ∈ B) (ho : a ∉ MulAut.innerSubgroup PSL) :
      orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha)
    (fun he => ho (he ▸ (MulAut.innerSubgroup PSL).one_mem))
  have heq : b'.fixedSubgroup = b.fixedSubgroup := eq_of_le_of_card_ge hle' (by
    rw [fixed_card_of_graph_conjugate b (hconj b (horder b hb hout) hout),
      fixed_card_of_graph_conjugate b' (hconj b' (horder b' hb' hout') hout')])
  have hdcenter : (⟨d, hD hd⟩ : b.fixedSubgroup) ∈ center b.fixedSubgroup := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    have hx : b' (x : PSL) = x := (MulAut.mem_fixedSubgroup b' x).mp
      (heq.symm ▸ x.property)
    have hbx : b (x : PSL) = x := (MulAut.mem_fixedSubgroup b x).mp x.property
    change d * b (x : PSL) * d⁻¹ = (x : PSL) at hx
    rw [hbx] at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hdone : (⟨d, hD hd⟩ : b.fixedSubgroup) = 1 := by
    simpa only [hcenter, mem_bot] using hdcenter
  exact hd1 (congrArg Subtype.val hdone)

theorem cubic_witness_of_nonnormal_four (b : MulAut PSL)
    (e : b.fixedSubgroup ≃* Equiv.Perm (Fin 4))
    (B : Subgroup (MulAut PSL)) (D : Subgroup PSL)
    (hD : IsElementaryAbelian 2 D) (hc : Nat.card D = 4)
    (hle : D ≤ b.fixedSubgroup) (hDB : D.map MulAut.conj ≤ B)
    (hn : ¬ (D.subgroupOf b.fixedSubgroup).Normal) :
    ∃ a ∈ B, ∃ c : PSL, b c = c ∧ orderOf (a c * c⁻¹) = 3 := by
  let : IsElementaryAbelian 2 D := hD
  let E := D.subgroupOf b.fixedSubgroup
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hle
  have hcE : Nat.card (E.map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, hc]
  have hnE : ¬ (E.map e.toMonoidHom).Normal := by
    intro h
    apply hn
    have ht := h.comap e.toMonoidHom
    simpa only [Subgroup.comap_map_eq, e.toMonoidHom.ker_eq_bot e.injective,
      sup_bot_eq] using ht
  obtain ⟨x, hx, y, hy⟩ := symmetricFour_four_cubic (E.map e.toMonoidHom)
    (IsElementaryAbelian.map _) hcE hnE
  obtain ⟨d, hd, rfl⟩ := hx
  let c := e.symm y
  refine ⟨MulAut.conj (d : PSL), hDB ⟨d, hd, rfl⟩, c,
    (MulAut.mem_fixedSubgroup b c).mp c.property, ?_⟩
  change orderOf ((d : PSL) * (c : PSL) * (d : PSL)⁻¹ * (c : PSL)⁻¹) = 3
  change orderOf ((d * c * d⁻¹ * c⁻¹ : b.fixedSubgroup) : PSL) = 3
  rw [Subgroup.orderOf_coe, ← e.orderOf_eq]
  simpa only [map_mul, map_inv, c, e.apply_symm_apply, MulEquiv.coe_toMonoidHom] using hy

end Matrix.PSL3Three.GraphWitnesses.EightCentralizers
