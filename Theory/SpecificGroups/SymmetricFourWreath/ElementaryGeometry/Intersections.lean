module
public import Theory.SpecificGroups.SymmetricFourWreath.ElementaryGeometry

/-!
# The square of maximum elementary subgroups

Two of the four coordinate E16 subgroups intersect in order four exactly
when their two plane choices are both opposite. The four labels are distinct.
Every permutation preserving intersection orders therefore commutes with the
fixed-point-free opposite involution; its permutation group has order eight.
This bounds the ambient normalizer action without enumerating automorphisms
of the dihedral direct product.

Source: Aschbacher–Smith 13.9.2(1–2), printed pp.969–970.
-/

public section
namespace SymmetricFourWreath
open Subgroup

private theorem prod_inf_prod {G H : Type*} [Group G] [Group H]
    (A C : Subgroup G) (B D : Subgroup H) : A.prod B ⊓ C.prod D = (A⊓C).prod (B⊓D) := by
  ext x
  simp only [mem_inf,mem_prod]
  tauto

private theorem card_plane_inf (b c : Bool) : Nat.card (plane b ⊓ plane c : Subgroup D8) = if b=c then 4 else 2 := by
  let : DecidablePred (· ∈ (plane b ⊓ plane c : Subgroup D8)) := fun x =>
    inferInstanceAs (Decidable (x∈plane b ∧ x∈plane c))
  rw [Nat.card_eq_fintype_card]
  cases b <;> cases c <;> decide +kernel

theorem card_elementary_inf (a b c d : Bool) : Nat.card (elementary a b ⊓ elementary c d : Subgroup W) =
    (if a=c then 4 else 2)*(if b=d then 4 else 2) := by
  rw [elementary,elementary,←map_inf _ _ sylowEmbedding sylowEmbedding_injective,
    card_map_of_injective sylowEmbedding_injective]
  rw [elementaryInP,elementaryInP,←map_inf _ _ pair pair_injective,
    card_map_of_injective pair_injective,prod_inf_prod]
  rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_plane_inf,card_plane_inf]

theorem elementary_injective : Function.Injective (fun p : Bool×Bool=>elementary p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ he
  change elementary a b = elementary c d at he
  have hc : Nat.card (elementary a b ⊓ elementary c d : Subgroup W) = 16 := by
    rw [←he,inf_idem,card_elementary]
  rw [card_elementary_inf] at hc
  by_cases ha : a=c <;> by_cases hb : b=d <;> simp only [ha,hb,if_true,if_false] at hc
  · exact Prod.ext ha hb
  all_goals omega

@[expose] def opposite : Equiv.Perm (Bool×Bool) where
  toFun p := (!p.1,!p.2)
  invFun p := (!p.1,!p.2)
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

theorem inf_card_four_iff (p q : Bool×Bool) :
    Nat.card (elementary p.1 p.2 ⊓ elementary q.1 q.2 : Subgroup W) = 4 ↔ q = opposite p := by
  rw [card_elementary_inf]
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel

@[expose] def intersectionPerms : Subgroup (Equiv.Perm (Bool×Bool)) := centralizer ({opposite} : Set _)

private instance : DecidablePred (·∈intersectionPerms) := fun g=>
  decidable_of_iff (g*opposite=opposite*g) (mem_centralizer_singleton_iff).symm

theorem card_intersectionPerms : Nat.card intersectionPerms = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem intersectionPerms_isPGroup : IsPGroup 2 intersectionPerms :=
  IsPGroup.of_card (n:=3) (by simpa only [show (2:ℕ)^3=8 from rfl] using card_intersectionPerms)

theorem mem_intersectionPerms (σ : Equiv.Perm (Bool×Bool))
    (h : ∀p q, Nat.card (elementary (σ p).1 (σ p).2 ⊓ elementary (σ q).1 (σ q).2 : Subgroup W) =
      Nat.card (elementary p.1 p.2 ⊓ elementary q.1 q.2 : Subgroup W)) : σ∈intersectionPerms := by
  apply mem_centralizer_singleton_iff.mpr
  apply Equiv.ext
  intro p
  change σ (opposite p)=opposite (σ p)
  apply (inf_card_four_iff (σ p) (σ (opposite p))).mp
  rw [h]
  exact (inf_card_four_iff p (opposite p)).mpr rfl

end SymmetricFourWreath
