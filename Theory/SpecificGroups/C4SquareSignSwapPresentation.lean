module

public import Theory.SpecificGroups.C4SquareSignSwap
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Recognition from sign-and-swap generators

Four generators satisfying the C₄-square sign-and-swap relations give a
homomorphism from the explicit model. If they generate a group of order 64,
this homomorphism is an equivalence. This separates the presentation argument
from the extraction of generators in Stellmacher (8.6)(a).
-/

namespace C4SquareSignSwap

/-- The defining relations of the sign-and-swap presentation. -/
public structure Relations {G : Type*} [Group G] (a b t u : G) : Prop where
  a_four : a ^ 4 = 1
  b_four : b ^ 4 = 1
  t_two : t ^ 2 = 1
  u_two : u ^ 2 = 1
  ab : Commute a b
  tu : Commute t u
  ta : t * a * t⁻¹ = a⁻¹
  tb : t * b * t⁻¹ = b⁻¹
  ua : u * a * u⁻¹ = b
  ub : u * b * u⁻¹ = a

private def cyclicHom {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (a : G) (ha : a ^ n = 1) : Multiplicative (ZMod n) →* G where
  toFun i := a ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change a ^ (i.toAdd + j.toAdd).val = a ^ i.toAdd.val * a ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ ha).symm

private def pairHom {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (a b : G) (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : Commute a b) :
    (Multiplicative (ZMod n) × Multiplicative (ZMod n)) →* G where
  toFun x := cyclicHom a ha x.1 * cyclicHom b hb x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    have h : Commute (cyclicHom b hb x.2) (cyclicHom a ha y.1) :=
      hab.symm.pow_pow _ _
    calc
      _ = cyclicHom a ha x.1 *
        (cyclicHom a ha y.1 * cyclicHom b hb x.2) * cyclicHom b hb y.2 := by group
      _ = _ := by rw [h.eq.symm]; group

private theorem base_hom_ext {G : Type*} [Group G] (f g : Base →* G)
    (h₁ : f (Multiplicative.ofAdd 1, 1) = g (Multiplicative.ofAdd 1, 1))
    (h₂ : f (1, Multiplicative.ofAdd 1) = g (1, Multiplicative.ofAdd 1)) : f = g := by
  ext x
  have hx : x = (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd.val *
      (1, Multiplicative.ofAdd 1) ^ x.2.toAdd.val :=
    (by decide : ∀ x : Base, x = (Multiplicative.ofAdd 1, 1) ^ x.1.toAdd.val *
      (1, Multiplicative.ofAdd 1) ^ x.2.toAdd.val) x
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [map_mul, map_pow, h₁, h₂]

private theorem compatibility {G : Type*} [Group G] {a b t u : G}
    (h : Relations a b t u) (c : Actor) :
    (pairHom a b h.a_four h.b_four h.ab).comp (action c).toMonoidHom =
      (MulAut.conj (pairHom t u h.t_two h.u_two h.tu c)).toMonoidHom.comp
        (pairHom a b h.a_four h.b_four h.ab) := by
  have hc : c = 1 ∨ c = (Multiplicative.ofAdd 1, 1) ∨
      c = (1, Multiplicative.ofAdd 1) ∨
      c = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) :=
    (by decide : ∀ c : Actor, c = 1 ∨ c = (Multiplicative.ofAdd 1, 1) ∨
      c = (1, Multiplicative.ofAdd 1) ∨
      c = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) c
  have hta3 : a ^ 3 = a⁻¹ := by
    apply mul_right_cancel (b := a)
    rw [inv_mul_cancel, ← pow_succ, h.a_four]
  have htb3 : b ^ 3 = b⁻¹ := by
    apply mul_right_cancel (b := b)
    rw [inv_mul_cancel, ← pow_succ, h.b_four]
  rcases hc with rfl | rfl | rfl | rfl <;>
    apply base_hom_ext <;>
    simp [pairHom, cyclicHom, action, twist, MulAut.conj_apply,
      h.ta, h.tb, h.ua, h.ub, hta3, htb3,
      show (1 : ZMod 4).val = 1 by decide, show (1 : ZMod 2).val = 1 by decide]

/-- The homomorphism specified by four elements satisfying the relations. -/
public def presentationHom {G : Type*} [Group G] {a b t u : G}
    (h : Relations a b t u) : Model →* G := by
  exact SemidirectProduct.lift (pairHom a b h.a_four h.b_four h.ab)
    (pairHom t u h.t_two h.u_two h.tu) (compatibility h)

public theorem presentationHom_rotation₁ {G : Type*} [Group G] {a b t u : G}
    (h : Relations a b t u) : presentationHom h rotation₁ = a := by
  simp [presentationHom, SemidirectProduct.lift, rotation₁, pairHom, cyclicHom,
    show (1 : ZMod 4).val = 1 by decide]

public theorem presentationHom_rotation₂ {G : Type*} [Group G] {a b t u : G}
    (h : Relations a b t u) : presentationHom h rotation₂ = b := by
  simp [presentationHom, SemidirectProduct.lift, rotation₂, pairHom, cyclicHom,
    show (1 : ZMod 4).val = 1 by decide]

public theorem presentationHom_inverter {G : Type*} [Group G] {a b t u : G}
    (h : Relations a b t u) : presentationHom h inverter = t := by
  simp [presentationHom, SemidirectProduct.lift, inverter, pairHom, cyclicHom,
    show (1 : ZMod 2).val = 1 by decide]

public theorem presentationHom_swapper {G : Type*} [Group G] {a b t u : G}
    (h : Relations a b t u) : presentationHom h swapper = u := by
  simp [presentationHom, SemidirectProduct.lift, swapper, pairHom, cyclicHom,
    show (1 : ZMod 2).val = 1 by decide]

/-- Generation and the order determine the group from these relations. -/
public theorem exists_equiv_of_relations {G : Type*} [Group G]
    (hcard : Nat.card G = 64) {a b t u : G} (h : Relations a b t u)
    (hgen : Subgroup.closure ({a, b, t, u} : Set G) = ⊤) :
    ∃ e : Model ≃* G, e rotation₁ = a ∧ e rotation₂ = b ∧
      e inverter = t ∧ e swapper = u := by
  let f := presentationHom h
  have hs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨rotation₁, presentationHom_rotation₁ h⟩
    · exact ⟨rotation₂, presentationHom_rotation₂ h⟩
    · exact ⟨inverter, presentationHom_inverter h⟩
    · exact ⟨swapper, presentationHom_swapper h⟩
  let e := MulEquiv.ofBijective f (hs.bijective_of_nat_card_le (by
    rw [hcard, card_model]))
  exact ⟨e, presentationHom_rotation₁ h, presentationHom_rotation₂ h,
    presentationHom_inverter h, presentationHom_swapper h⟩

/-- The transfer subgroup is generated by the two rotations and the swapper. -/
public theorem transfer_eq_closure : transfer =
    Subgroup.closure ({rotation₁, rotation₂, swapper} : Set Model) := by
  apply le_antisymm
  · intro g hg
    have hn : g = rotation₁ ^ g.left.1.toAdd.val * rotation₂ ^ g.left.2.toAdd.val *
        swapper ^ g.right.2.toAdd.val :=
      (by decide +kernel : ∀ g : Model, g ∈ transfer →
        g = rotation₁ ^ g.left.1.toAdd.val * rotation₂ ^ g.left.2.toAdd.val *
          swapper ^ g.right.2.toAdd.val) g hg
    rw [hn]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem <;> apply Subgroup.pow_mem <;>
        exact Subgroup.subset_closure (by simp)
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    exact (by decide : ∀ g ∈ ({rotation₁, rotation₂, swapper} : Set Model), g ∈ transfer)

/-- The inverter core is generated by the two rotations and the inverter. -/
public theorem inverterCore_eq_closure : inverterCore =
    Subgroup.closure ({rotation₁, rotation₂, inverter} : Set Model) := by
  apply le_antisymm
  · intro g hg
    have hn : g = rotation₁ ^ g.left.1.toAdd.val * rotation₂ ^ g.left.2.toAdd.val *
        inverter ^ g.right.1.toAdd.val :=
      (by decide +kernel : ∀ g : Model, g ∈ inverterCore →
        g = rotation₁ ^ g.left.1.toAdd.val * rotation₂ ^ g.left.2.toAdd.val *
          inverter ^ g.right.1.toAdd.val) g hg
    rw [hn]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem <;> apply Subgroup.pow_mem <;>
        exact Subgroup.subset_closure (by simp)
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    exact (by decide : ∀ g ∈ ({rotation₁, rotation₂, inverter} : Set Model), g ∈ inverterCore)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Diagonal and antidiagonal rotations and the two actors generate the second core. -/
public theorem extraspecialCore_eq_closure : extraspecialCore =
    Subgroup.closure ({rotation₁ * rotation₂, rotation₁ * rotation₂⁻¹,
      inverter, swapper} : Set Model) := by
  apply le_antisymm
  · intro g hg
    have hn : ∃ i j : Fin 4,
        g = (rotation₁ * rotation₂) ^ i.val * (rotation₁ * rotation₂⁻¹) ^ j.val *
          inverter ^ g.right.1.toAdd.val * swapper ^ g.right.2.toAdd.val :=
      (by decide +kernel : ∀ g : Model, g ∈ extraspecialCore → ∃ i j : Fin 4,
        g = (rotation₁ * rotation₂) ^ i.val * (rotation₁ * rotation₂⁻¹) ^ j.val *
          inverter ^ g.right.1.toAdd.val * swapper ^ g.right.2.toAdd.val) g hg
    obtain ⟨i, j, hn⟩ := hn
    rw [hn]
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · apply Subgroup.mul_mem <;> apply Subgroup.pow_mem <;>
          exact Subgroup.subset_closure (by simp)
      · apply Subgroup.pow_mem
        exact Subgroup.subset_closure (by simp)
    · apply Subgroup.pow_mem
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    exact (by decide : ∀ g ∈ ({rotation₁ * rotation₂, rotation₁ * rotation₂⁻¹,
      inverter, swapper} : Set Model), g ∈ extraspecialCore)

/-- A marked presentation identifies all three distinguished subgroups at once. -/
public theorem exists_marked_equiv_of_relations {G : Type*} [Group G]
    (hcard : Nat.card G = 64) (U Qa Qb : Subgroup G) {a b t u : G}
    (h : Relations a b t u)
    (hgen : Subgroup.closure ({a, b, t, u} : Set G) = ⊤)
    (hU : U = Subgroup.closure ({a, b, u} : Set G))
    (hQa : Qa = Subgroup.closure ({a, b, t} : Set G))
    (hQb : Qb = Subgroup.closure ({a * b, a * b⁻¹, t, u} : Set G)) :
    ∃ e : G ≃* Model, U.map e.toMonoidHom = transfer ∧
      Qa.map e.toMonoidHom = inverterCore ∧ Qb.map e.toMonoidHom = extraspecialCore := by
  obtain ⟨e, ha, hb, ht, hu⟩ := exists_equiv_of_relations hcard h hgen
  have hmU : transfer.map e.toMonoidHom = U := by
    rw [transfer_eq_closure, MonoidHom.map_closure, hU]
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom, ha, hb, hu]
  have hmQa : inverterCore.map e.toMonoidHom = Qa := by
    rw [inverterCore_eq_closure, MonoidHom.map_closure, hQa]
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom, ha, hb, ht]
  have hmQb : extraspecialCore.map e.toMonoidHom = Qb := by
    rw [extraspecialCore_eq_closure, MonoidHom.map_closure, hQb]
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      map_mul, map_inv, ha, hb, ht, hu]
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · rw [← hmU, Subgroup.map_map]
    simp
  · rw [← hmQa, Subgroup.map_map]
    simp
  · rw [← hmQb, Subgroup.map_map]
    simp

end C4SquareSignSwap
