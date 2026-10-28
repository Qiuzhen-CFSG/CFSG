module

public import Theory.GroupTheory.PGroup.InvariantFiberAutomorphisms

/-!
# Coordinate evaluation of intrinsic fiber counts

An isomorphism from a concrete group transports its Frattini projection and
the order/centralizer counts on every fiber. Fiber parametrizations further
reduce these counts to finite filters, without requiring a computable
membership test for the original subgroup defined by generators.

The proofs use bijections of the counted sets and functoriality of the
Frattini subgroup under surjections. No enumeration oracle is involved.
-/

namespace MulEquiv
variable {G H : Type*} [Group G] [Group H]

/-- Isomorphisms identify the Frattini subgroups by inverse image. -/
public theorem comap_frattini (e : G ≃* H) :
    (frattini H).comap e.toMonoidHom = frattini G := by
  apply le_antisymm
  · intro x hx
    have h := frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hx
    simpa only [Subgroup.mem_comap, toMonoidHom_eq_coe, MonoidHom.coe_coe,
      symm_apply_apply] using h
  · exact frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective

/-- Centralizer counts can be evaluated in any isomorphic coordinate group. -/
public theorem commutingCard_apply (e : G ≃* H) (x : G) :
    MulAut.commutingCard (e x) = MulAut.commutingCard x := by
  apply (Nat.card_congr (e.toEquiv.subtypeEquiv (fun y => ?_))).symm
  change y * x = x * y ↔ e y * e x = e x * e y
  simp only [← map_mul, e.injective.eq_iff]

/-- The three intrinsic tests are unchanged by a coordinate isomorphism. -/
public theorem orderCentralizerTest_apply (e : G ≃* H) (t : ℕ × ℕ × ℕ) (x : G) :
    MulAut.orderCentralizerTest t (e x) ↔ MulAut.orderCentralizerTest t x := by
  simp only [MulAut.orderCentralizerTest, e.orderOf_eq,
    commutingCard_apply, ← map_pow]
end MulEquiv

namespace MonoidHom
variable {G H V W : Type*} [Group G] [Group H] [Group V]

/-- Transport a Frattini-kernel certificate from a coordinate group. -/
public theorem ker_comp_mulEquiv_eq_frattini (π : H →* V) (e : G ≃* H)
    (hker : π.ker = frattini H) :
    (π.comp e.toMonoidHom).ker = frattini G := by
  change π.ker.comap e.toMonoidHom = frattini G
  rw [hker, e.comap_frattini]

/-- Transport a predicate and its fiber count along a coordinate isomorphism. -/
public theorem predicateFiberCard_comp_mulEquiv (π : H →* V) (e : G ≃* H)
    (P : H → Prop) (v : V) :
    (π.comp e.toMonoidHom).predicateFiberCard (fun x => P (e x)) v =
      π.predicateFiberCard P v := by
  apply Nat.card_congr
  exact e.toEquiv.subtypeEquiv (fun _ => Iff.rfl)

/-- Order and centralizer fiber counts transport without an extra invariance premise. -/
public theorem orderCentralizerFiberCard_comp_mulEquiv (π : H →* V) (e : G ≃* H)
    (t : ℕ × ℕ × ℕ) (v : V) :
    (π.comp e.toMonoidHom).predicateFiberCard (MulAut.orderCentralizerTest t) v =
      π.predicateFiberCard (MulAut.orderCentralizerTest t) v := by
  rw [← predicateFiberCard_comp_mulEquiv π e]
  congr 1
  funext x
  exact propext (e.orderCentralizerTest_apply t x).symm

/-- A finite coordinate group turns a predicate fiber count into a filter. -/
public theorem predicateFiberCard_eq_card_filter [Fintype G] [DecidableEq V]
    (π : G →* V) (P : G → Prop) [DecidablePred P] (v : V) :
    π.predicateFiberCard P v =
      (Finset.univ.filter (fun x => π x = v ∧ P x)).card := by
  unfold predicateFiberCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Parametrizing just one fiber avoids enumerating the entire source group. -/
public theorem predicateFiberCard_eq_card_filter_of_equiv [Fintype W]
    (π : G →* V) (P : G → Prop) (v : V)
    (e : W ≃ {x : G // π x = v})
    [DecidablePred (fun w => P (e w).val)] :
    π.predicateFiberCard P v =
      (Finset.univ.filter (fun w => P (e w).val)).card := by
  have h : π.predicateFiberCard P v = Nat.card {w : W // P (e w).val} := by
    apply Nat.card_congr
    refine {
      toFun := fun x => ⟨e.symm ⟨x.val, x.property.1⟩, ?_⟩
      invFun := fun w => ⟨(e w.val).val, (e w.val).property, w.property⟩
      left_inv := ?_
      right_inv := ?_ }
    · simpa only [e.apply_symm_apply] using x.property.2
    · intro x
      apply Subtype.ext
      change (e (e.symm ⟨x.val, x.property.1⟩)).val = x.val
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x.val, x.property.1⟩)
    · intro w
      apply Subtype.ext
      exact e.symm_apply_apply w.val
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
end MonoidHom

namespace MulAut
variable {G W : Type*} [Group G]

/-- Enumerate commuting elements in any finite parametrization of the group. -/
public theorem commutingCard_eq_card_filter_of_equiv [Fintype W] [DecidableEq G]
    (e : W ≃ G) (x : G) :
    commutingCard x = (Finset.univ.filter (fun w => e w * x = x * e w)).card := by
  have h : commutingCard x = Nat.card {w : W // e w * x = x * e w} :=
    (Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))).symm
  rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
end MulAut
