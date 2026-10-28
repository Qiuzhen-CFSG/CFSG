module

public import Theory.GroupAction.KleinFourFactorization
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Three centralizers in an ambient odd subgroup

Transport the Klein-four factorization and Brauer–Wielandt formula through
the literal conjugation action on a normalized odd-order subgroup. The
common fixed group is retained, so these statements also allow nonfaithful
actions. This is the ambient form used in Aschbacher–Smith J.2.7(5).

Source: Gorenstein–Walter, *On finite groups with dihedral Sylow
2-subgroups*, Section 2, Lemma 4(ii), as in `KleinFourFactorization`.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] (P : Subgroup G)

private theorem normalizer_fixed_iff (a : normalizer (P : Set G)) (x : P) :
    x ∈ (P.normalizerMonoidHom a).fixedSubgroup ↔
      (x : G) ∈ centralizer ({(a : G)} : Set G) := by
  rw [MulAut.mem_fixedSubgroup, Subtype.ext_iff, mem_centralizer_singleton_iff]
  change (a : G) * (x : G) * (a : G)⁻¹ = (x : G) ↔ _
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

/-- The conjugation-fixed group is the literal ambient intersection. -/
def normalizerFixedEquiv (a : normalizer (P : Set G)) :
    (P.normalizerMonoidHom a).fixedSubgroup ≃*
      (P ⊓ centralizer ({(a : G)} : Set G) : Subgroup G) where
  toFun x := ⟨x.val.val, x.val.property,
    (normalizer_fixed_iff P a x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩,
    (normalizer_fixed_iff P a _).mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem normalizer_involutive (a : normalizer (P : Set G)) (ha : a ^ 2 = 1) :
    Function.Involutive (P.normalizerMonoidHom a) := by
  intro x
  have h : P.normalizerMonoidHom a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  exact congrArg (fun f : MulAut P => f x) h

variable [Finite P]

/-- Three involution centralizers factor the subgroup as an ordered set product. -/
theorem exists_three_odd_centralizers (hodd : Odd (Nat.card P))
    (a b : normalizer (P : Set G)) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : Commute a b) (x : G) (hx : x ∈ P) :
    ∃ u ∈ P ⊓ centralizer ({(a : G)} : Set G),
      ∃ v ∈ P ⊓ centralizer ({(b : G)} : Set G),
        ∃ w ∈ P ⊓ centralizer ({((a * b : normalizer (P : Set G)) : G)} : Set G),
          x = u * v * w := by
  obtain ⟨u, v, w, hu, hv, hw, he⟩ :=
    MulAut.exists_fixed_mul_fixed_mul_fixed_of_odd_card hodd
      (P.normalizerMonoidHom a) (P.normalizerMonoidHom b)
      (normalizer_involutive P a ha) (normalizer_involutive P b hb)
      (hab.map P.normalizerMonoidHom) (⟨x, hx⟩ : P)
  refine ⟨u, ⟨u.property, (normalizer_fixed_iff P a u).mp
      ((MulAut.mem_fixedSubgroup _ _).mpr hu)⟩,
    v, ⟨v.property, (normalizer_fixed_iff P b v).mp
      ((MulAut.mem_fixedSubgroup _ _).mpr hv)⟩,
    w, ⟨w.property, (normalizer_fixed_iff P (a*b) w).mp ?_⟩,
    congrArg Subtype.val he⟩
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  simpa only [map_mul] using hw

/-- The ambient Brauer–Wielandt formula, with the common centralizer included. -/
theorem card_three_odd_centralizers (hodd : Odd (Nat.card P))
    (a b : normalizer (P : Set G)) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : Commute a b) :
    Nat.card P * Nat.card
        ((P ⊓ centralizer ({(a : G)} : Set G)) ⊓ centralizer ({(b : G)} : Set G) : Subgroup G)^2 =
      Nat.card (P ⊓ centralizer ({(a : G)} : Set G) : Subgroup G) *
      Nat.card (P ⊓ centralizer ({(b : G)} : Set G) : Subgroup G) *
      Nat.card (P ⊓ centralizer ({((a*b : normalizer (P : Set G)) : G)} : Set G) : Subgroup G) := by
  have h := Theory.GroupAction.brauerWielandt_fixedSubgroup_card hodd
    (P.normalizerMonoidHom a) (P.normalizerMonoidHom b)
    (normalizer_involutive P a ha) (normalizer_involutive P b hb)
    (hab.map P.normalizerMonoidHom)
  have hcommon : Nat.card
      ((P.normalizerMonoidHom a).fixedSubgroup ⊓
        (P.normalizerMonoidHom b).fixedSubgroup : Subgroup P) =
      Nat.card ((P ⊓ centralizer ({(a : G)} : Set G)) ⊓
        centralizer ({(b : G)} : Set G) : Subgroup G) := by
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨x.val.val, ⟨x.val.property,
        (normalizer_fixed_iff P a x.val).mp x.property.1⟩,
        (normalizer_fixed_iff P b x.val).mp x.property.2⟩
      invFun := fun x => ⟨⟨x.val, x.property.1.1⟩,
        (normalizer_fixed_iff P a _).mpr x.property.1.2,
        (normalizer_fixed_iff P b _).mpr x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hcommon, ← map_mul, Nat.card_congr (P.normalizerFixedEquiv a).toEquiv,
    Nat.card_congr (P.normalizerFixedEquiv b).toEquiv,
    Nat.card_congr (P.normalizerFixedEquiv (a*b)).toEquiv] at h
  exact h

omit [Finite P] in
/-- Conjugating an actor by a normalizer element preserves its fixed-subgroup order. -/
theorem card_inf_centralizer_conj (t : G) (ht : t ∈ normalizer (P : Set G)) (a : G) :
    Nat.card (P ⊓ centralizer ({a} : Set G) : Subgroup G) =
      Nat.card (P ⊓ centralizer ({t*a*t⁻¹} : Set G) : Subgroup G) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (MulAut.conj t).toEquiv ?_
  intro x
  simp only [mem_inf, mem_centralizer_singleton_iff]
  apply and_congr (ht x)
  let e := MulAut.conj t
  change x*a = a*x ↔ e x * e a = e a * e x
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

end Subgroup
