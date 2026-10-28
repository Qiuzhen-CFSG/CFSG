module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction.Components.Structure
public import Theory.Representation.NormalInvariants
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The constituent dimension bound in 15.3.58

A nontrivial normal subgroup has no trivial irreducible submodule in a
faithful irreducible ambient action: a nonzero fixed vector would make the
whole normal subgroup lie in the kernel. A perfect group acts trivially on
a binary space of dimension at most two, since its permutation image on the
at most four vectors is solvable. Combining these facts with perfectness of
the nonsolvable minimal normal subgroup gives the required dimension bound.
No complete reducibility or classification of small linear groups is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1149,
proof of 15.3.58, specialized here to its nonsolvable minimal-normal branch.
-/

@[expose] public section

open Representation
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction

private theorem binary_action_eq_one_of_finrank_le_two {G V : Type*} [Group G] [Group.IsPerfect G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hd : Module.finrank (ZMod 2) V ≤ 2) :
    ρ = 1 := by
  classical
  have hc : Nat.card V ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hd
  let : Fintype V := Fintype.ofFinite V
  let e : V ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hc))
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm V) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f : G →* Equiv.Perm V := {
    toFun := fun g => {
      toFun := ρ g
      invFun := ρ g⁻¹
      left_inv := fun v => by
        change (ρ g⁻¹ * ρ g) v = v
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun v => by
        change (ρ g * ρ g⁻¹) v = v
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
    map_one' := by ext v; exact DFunLike.congr_fun (map_one ρ) v
    map_mul' := fun g h => by ext v; exact DFunLike.congr_fun (map_mul ρ g h) v }
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  ext g v
  exact congrArg (fun a : f.range => a.val v)
    (Subsingleton.elim (f.rangeRestrict g) 1)

/-- A nontrivial normal subgroup cannot have a trivial constituent in a
faithful irreducible ambient representation. -/
theorem IsMinimalNormal.constituent_ne_one
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible)
    (hfaith : Function.Injective ρ) (K : Subgroup G) (hK : IsMinimalNormal K)
    (A : Subrepresentation (ρ.comp K.subtype))
    (hA : A.toRepresentation.IsIrreducible) : A.toRepresentation ≠ 1 := by
  let := hK.1
  have hne := hK.2.1
  intro ht
  let := hirr
  let := hA
  let := Subrepresentation.irreducible_module_nontrivial A.toRepresentation
  obtain ⟨v, hv⟩ := exists_ne (0 : A.toSubmodule)
  have hv0 : (v : V) ≠ 0 := fun he => hv (Subtype.ext he)
  have hfix : Representation.invariants (ρ.comp K.subtype) ≠ ⊥ := by
    intro hb
    have hm : (v : V) ∈ Representation.invariants (ρ.comp K.subtype) := by
      intro k
      exact congrArg Subtype.val (DFunLike.congr_fun (DFunLike.congr_fun ht k) v)
    exact hv0 (by simpa only [hb, Submodule.mem_bot] using hm)
  have hker := le_ker_of_normal_invariants_ne_bot ρ K hfix
  apply hne
  apply bot_unique
  intro k hk
  exact hfaith ((MonoidHom.mem_ker.mp (hker hk)).trans (map_one ρ).symm)

/-- Every irreducible constituent for a nonsolvable minimal normal subgroup
in a faithful irreducible binary representation has dimension at least three. -/
theorem IsMinimalNormal.constituent_finrank_ge_three
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible)
    (hfaith : Function.Injective ρ) (K : Subgroup G)
    (hK : IsMinimalNormal K) (hns : ¬ Group.IsSolvable K)
    (A : Subrepresentation (ρ.comp K.subtype))
    (hA : A.toRepresentation.IsIrreducible) :
    3 ≤ Module.finrank (ZMod 2) A.toSubmodule := by
  let := hK.isPerfect_of_not_isSolvable K hns
  by_contra! hd
  exact hK.constituent_ne_one ρ hirr hfaith K A hA
    (binary_action_eq_one_of_finrank_le_two A.toRepresentation (by omega))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
