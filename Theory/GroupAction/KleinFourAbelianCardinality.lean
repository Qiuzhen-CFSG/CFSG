module
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.Tactic.Ring

/-!
# The abelian Klein-four fixed-point cardinality formula

For commuting involutive automorphisms `a` and `b` of a finite abelian group
of odd order, the group order times the square of the common fixed-subgroup
order is the product of the three fixed-subgroup orders. The action need not
be faithful. This is the abelian base case of the Brauer--Wielandt relation
used in Gorenstein--Walter, Section 2, Lemma 3.

The proof uses the unique fixed/inverted factorization from
`Theory.GroupTheory.FixedInvertedFactorization`. If two endomorphisms commute
with an involution, uniqueness shows that their equalizer splits into its
fixed and inverted parts. Apply this counting lemma to the whole group, the
fixed subgroup of `b`, the fixed subgroup of `a * b`, and the elements inverted
by `a`. In the last application inversion is an endomorphism because the
group is abelian. The resulting factors are the simultaneous fixed/inverted
parts for `a` and `b`; their cardinal identities imply the formula.
-/

namespace Theory.GroupAction

private theorem card_locus_split {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (a : MulAut G) (ha : Function.Involutive a)
    (f g : G →* G) (hf : ∀ x, a (f x) = f (a x))
    (hg : ∀ x, a (g x) = g (a x)) :
    Nat.card {x : G // f x = g x} =
      Nat.card {x : G // a x = x ∧ f x = g x} *
      Nat.card {x : G // a x = x⁻¹ ∧ f x = g x} := by
  let F := {x : G // a x = x ∧ f x = g x}
  let I := {x : G // a x = x⁻¹ ∧ f x = g x}
  let m : F × I → {x : G // f x = g x} := fun p =>
    ⟨p.1.val * p.2.val, by simp only [map_mul, p.1.property.2, p.2.property.2]⟩
  have hm : Function.Bijective m := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ heq
      obtain ⟨p, hp, hu⟩ :=
        Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd a ha
          (u.val * v.val)
      have h1 := hu (u.val, v.val) ⟨u.property.1, v.property.1, rfl⟩
      have h2 := hu (u'.val, v'.val)
        ⟨u'.property.1, v'.property.1, (congrArg Subtype.val heq).symm⟩
      have hh := h1.trans h2.symm
      exact Prod.ext (Subtype.ext (congrArg Prod.fst hh))
        (Subtype.ext (congrArg Prod.snd hh))
    · intro x
      obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, huniq⟩ :=
        Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd a ha x.val
      obtain ⟨p, hp, huniq'⟩ :=
        Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd a ha (f x.val)
      have hfu := huniq' (f u, f v) (by
        refine ⟨?_, ?_, ?_⟩
        · rw [hf, hu]
        · rw [hf, hv, map_inv]
        · rw [← map_mul, huv])
      have hgu := huniq' (g u, g v) (by
        refine ⟨?_, ?_, ?_⟩
        · rw [hg, hu]
        · rw [hg, hv, map_inv]
        · rw [← map_mul, huv, x.property])
      have heq := hfu.trans hgu.symm
      refine ⟨(⟨u, hu, congrArg Prod.fst heq⟩, ⟨v, hv, congrArg Prod.snd heq⟩), ?_⟩
      exact Subtype.ext huv
  calc
    _ = Nat.card (F × I) := (Nat.card_congr (Equiv.ofBijective m hm)).symm
    _ = _ := Nat.card_prod F I

open scoped IsMulCommutative
private theorem card_subtype_congr {G : Type*} (P Q : G → Prop)
    (h : ∀ x, P x ↔ Q x) : Nat.card {x // P x} = Nat.card {x // Q x} :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

private theorem formula {G : Type*} [Group G] [Finite G] [IsMulCommutative G]
    (hodd : Odd (Nat.card G)) (a b : MulAut G)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (hab : Commute a b) :
    Nat.card G * Nat.card {x : G // a x = x ∧ b x = x} ^ 2 =
      Nat.card {x : G // a x = x} * Nat.card {x : G // b x = x} *
      Nat.card {x : G // (a*b) x = x} := by
  have hc (x : G) : a (b x) = b (a x) := congrArg (fun e : MulAut G => e x) hab.eq
  have hG := card_locus_split hodd a ha (MonoidHom.id G) (MonoidHom.id G)
    (fun _ => rfl) (fun _ => rfl)
  simp only [MonoidHom.id_apply, and_true] at hG
  rw [Nat.card_subtype_true] at hG
  have hB := card_locus_split hodd a ha b.toMonoidHom (MonoidHom.id G) hc (fun _ => rfl)
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at hB
  have hI := card_locus_split hodd b hb a.toMonoidHom (invMonoidHom : G →* G)
    (fun x => (hc x).symm) (fun x => map_inv b x)
  simp only [MulEquiv.coe_toMonoidHom, invMonoidHom_apply] at hI
  have hs : Nat.card {x : G // b x = x ∧ a x = x⁻¹} =
      Nat.card {x : G // a x = x⁻¹ ∧ b x = x} :=
    card_subtype_congr _ _ (fun _ => and_comm)
  rw [hs] at hI
  have hAB := card_locus_split hodd a ha (a*b).toMonoidHom (MonoidHom.id G)
    (fun x => by change a (a (b x)) = a (b (a x)); rw [hc]) (fun _ => rfl)
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at hAB
  have hfix : Nat.card {x : G // a x = x ∧ (a*b) x = x} =
      Nat.card {x : G // a x = x ∧ b x = x} := by
    apply card_subtype_congr
    intro x
    change (a x = x ∧ a (b x) = x) ↔ (a x = x ∧ b x = x)
    constructor
    · rintro ⟨hx, habx⟩
      exact ⟨hx, a.injective (habx.trans hx.symm)⟩
    · rintro ⟨hx, hbx⟩
      exact ⟨hx, by rw [hbx, hx]⟩
  have hinv : Nat.card {x : G // a x = x⁻¹ ∧ (a*b) x = x} =
      Nat.card {x : G // b x = x⁻¹ ∧ a x = x⁻¹} := by
    apply card_subtype_congr
    intro x
    change (a x = x⁻¹ ∧ a (b x) = x) ↔ (b x = x⁻¹ ∧ a x = x⁻¹)
    constructor
    · rintro ⟨hx, habx⟩
      refine ⟨a.injective ?_, hx⟩
      rw [habx, map_inv, hx, inv_inv]
    · rintro ⟨hbx, hx⟩
      exact ⟨hx, by rw [hbx, map_inv, hx, inv_inv]⟩
  rw [hfix, hinv] at hAB
  rw [hG, hB, hAB, hI]
  ring
/-- The Brauer--Wielandt order relation for commuting involutions of a finite
abelian group of odd order. -/
public theorem brauerWielandt_fixedSubgroup_card_of_isMulCommutative
    {G : Type*} [Group G] [Finite G] [IsMulCommutative G]
    (hodd : Odd (Nat.card G)) (a b : MulAut G)
    (ha : Function.Involutive a) (hb : Function.Involutive b) (hab : Commute a b) :
    Nat.card G * Nat.card ↥(MulAut.fixedSubgroup a ⊓ MulAut.fixedSubgroup b) ^ 2 =
      Nat.card (MulAut.fixedSubgroup a) * Nat.card (MulAut.fixedSubgroup b) *
        Nat.card (MulAut.fixedSubgroup (a * b)) := by
  simpa only [← MulAut.mem_fixedSubgroup, ← Subgroup.mem_inf] using
    formula hodd a b ha hb hab
end Theory.GroupAction
