module

public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.CubicCore
public import Mathlib.GroupTheory.Complement

/-!
# The cubic Sylow subgroup and its normalizer

The inverse image of the retained cubic kernel is the intrinsic O₂,₃(H),
by `cubicLift_eq_twoThreeCore`. Its order is 3 · 2¹³. Every Sylow
three-subgroup X therefore complements Q inside this inverse image.
Frattini's argument gives H = Q N_H(X), as an actual ordered product.
Projection identifies X with the original quotient's order-three kernel.

This proves the first clause of (4.1). The fixed-space, quasisimplicity and
GF(4) module clauses require additional arguments and are not asserted here.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.1), printed p.597.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

open Subgroup LocalGeometry LocalGeometry.LocalSubgroups

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))

/-- The chosen cubic Sylow, inside the original involution centralizer. -/
noncomputable def cubicSylowImage (X : Sylow 3 (CubicLift.subgroup e)) :
    Subgroup (centralizer z) :=
  (X : Subgroup (CubicLift.subgroup e)).map (CubicLift.subgroup e).subtype

theorem cubicSylow_card (h : IsTypeJ4 z) (X : Sylow 3 (CubicLift.subgroup e)) :
    Nat.card X = 3 := by
  rw [X.card_eq_multiplicity, CubicLift.subgroup_card e h]
  rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, (by decide : Nat.Prime 3).factorization]

theorem core_isComplement_cubicSylow (h : IsTypeJ4 z)
    (X : Sylow 3 (CubicLift.subgroup e)) :
    IsComplement' ((core z).subgroupOf (CubicLift.subgroup e))
      (X : Subgroup (CubicLift.subgroup e)) := by
  have hc : Nat.card ((core z).subgroupOf (CubicLift.subgroup e)) = 2 ^ 13 :=
    (Nat.card_congr (subgroupOfEquivOfLe (CubicLift.core_le e)).toEquiv).trans h.core_card
  apply isComplement'_of_coprime
  · rw [hc, cubicSylow_card e h X, CubicLift.subgroup_card e h, Nat.mul_comm]
  · rw [hc, cubicSylow_card e h X]
    norm_num

theorem core_sup_cubicSylow (h : IsTypeJ4 z)
    (X : Sylow 3 (CubicLift.subgroup e)) :
    core z ⊔ cubicSylowImage e X = CubicLift.subgroup e := by
  have hh := congrArg (Subgroup.map (CubicLift.subgroup e).subtype)
    (core_isComplement_cubicSylow e h X).sup_eq_top
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le (CubicLift.core_le e), ← MonoidHom.range_eq_map,
    range_subtype, cubicSylowImage] using hh

/-- The first assertion of source (4.1), expressed as generation inside H. -/
theorem core_sup_cubicNormalizer (h : IsTypeJ4 z)
    (X : Sylow 3 (CubicLift.subgroup e)) :
    core z ⊔ normalizer (cubicSylowImage e X : Set (centralizer z)) = ⊤ := by
  apply top_unique
  rw [← X.normalizer_sup_eq_top]
  apply sup_le le_sup_right
  exact (core_sup_cubicSylow e h X).ge.trans
    (sup_le le_sup_left (le_normalizer.trans le_sup_right))

/-- The actual product decomposition H = Q N_H(X), in that order. -/
theorem exists_core_mul_cubicNormalizer (h : IsTypeJ4 z)
    (X : Sylow 3 (CubicLift.subgroup e)) (g : centralizer z) :
    ∃ q : core z, ∃ n : normalizer (cubicSylowImage e X : Set (centralizer z)),
      (q : centralizer z) * n = g := by
  obtain ⟨q, hq, n, hn, he⟩ := mem_sup_of_normal_left.mp
    ((core_sup_cubicNormalizer e h X).ge (mem_top g))
  exact ⟨⟨q, hq⟩, ⟨n, hn⟩, he⟩

/-- Projection identifies this complement with the very same cubic kernel. -/
noncomputable def cubicKernelEquiv (h : IsTypeJ4 z)
    (X : Sylow 3 (CubicLift.subgroup e)) : X ≃* e.projection.ker :=
  (core_isComplement_cubicSylow e h X).symm.QuotientMulEquiv.symm.trans
    (CubicLift.quotientEquiv e)

@[simp] theorem cubicKernelEquiv_apply (h : IsTypeJ4 z)
    (X : Sylow 3 (CubicLift.subgroup e)) (x : X) :
    (cubicKernelEquiv e h X x : (centralizer z) ⧸ core z) =
      QuotientGroup.mk' (core z) ((x : CubicLift.subgroup e) : centralizer z) := rfl

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

end
