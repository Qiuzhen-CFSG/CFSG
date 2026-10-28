module

public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Index

/-!
# Rank-one images of elementary groups of order eight

The image of an elementary abelian group of order eight has generator rank
at most one exactly when the kernel has order at least four. The kernel is
the literal intersection with the ambient homomorphism kernel; in particular
the quotient version uses the actual normal subgroup being factored out.

The proof combines the kernel-image order formula with the exponent bound
on the order of a finitely generated abelian group. This is the cardinal
calculation needed for rank-three actors in Aschbacher--Smith E.1.5, p.210.
It does not assert that a particular local radical contains a four-group.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace IsElementaryAbelian
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] [Finite H] in
/-- The kernel-image formula with the kernel written as an ambient intersection. -/
theorem card_inf_ker_mul_card_map (A : Subgroup G) (f : G →* H) :
    Nat.card (A ⊓ f.ker : Subgroup G) * Nat.card (A.map f) = Nat.card A := by
  let g : A →* A.map f := f.subgroupMap A
  let e : g.ker ≃* (A ⊓ f.ker : Subgroup G) := {
    toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have h := g.ker.card_mul_index
  rw [index_ker, g.range_eq_top_of_surjective (f.subgroupMap_surjective A),
    card_top, Nat.card_congr e.toEquiv] at h
  exact h

/-- Killing a four-group is both necessary and sufficient for a rank-one image. -/
theorem rank_map_le_one_iff_of_card_eight (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 8) (f : G →* H) :
    Group.rank (A.map f) ≤ 1 ↔ 4 ≤ Nat.card (A ⊓ f.ker : Subgroup G) := by
  let : Finite (A.map f) := Finite.of_surjective _ (f.subgroupMap_surjective A)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hprod := card_inf_ker_mul_card_map A f
  rw [hA] at hprod
  constructor
  · intro hr
    let : CommGroup (A.map f) := IsMulCommutative.instCommGroup
    have hd := card_dvd_exponent_pow_rank' (A.map f)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (A.map f)))
    have hc : Nat.card (A.map f) ≤ 2 :=
      (Nat.le_of_dvd (by positivity) hd).trans
        (by simpa using (pow_le_pow_right' (by decide : 1 ≤ 2) hr))
    nlinarith
  · intro hk
    apply IsElementaryAbelian.rank_le_of_card_le (p := 2)
    have hc : Nat.card (A.map f) ≤ 2 := by nlinarith
    simpa using hc

/-- Specialization to the literal quotient by a normal subgroup. -/
theorem rank_quotient_image_le_one_iff_of_card_eight (A N : Subgroup G)
    [IsElementaryAbelian 2 A] [N.Normal] (hA : Nat.card A = 8) :
    Group.rank (A.map (QuotientGroup.mk' N)) ≤ 1 ↔
      4 ≤ Nat.card (A ⊓ N : Subgroup G) := by
  simpa only [QuotientGroup.ker_mk'] using
    rank_map_le_one_iff_of_card_eight A hA (QuotientGroup.mk' N)

end IsElementaryAbelian
