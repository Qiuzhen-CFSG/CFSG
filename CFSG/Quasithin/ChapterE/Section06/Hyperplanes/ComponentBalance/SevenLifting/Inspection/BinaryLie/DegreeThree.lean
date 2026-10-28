module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.Representation.FiveCycleDegreeThree
public import Theory.GroupTheory.FiveCycleSquareLift
public import Theory.SpecificGroups.Alternating.SevenFiveCycle
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Seven-component exclusion in binary degree-three models

A₇ contains a cyclic five-subgroup with its squaring automorphism. The same
pair lifts to its perfect central three-cover, by existence and uniqueness
of coprime torsion lifts through the center of order three. A faithful
three-dimensional matrix group away from characteristic five cannot contain
this pair: its cyclic five-subgroup has at most three character weights,
and the automizer acts faithfully on those weights.

For PSL₃, lift through the actual SL₃ center, which consists of cube roots
of unity. For PSU₃, use the actual special-to-projective map and its proved
central cube-one kernel, retaining the arbitrary Hermitian form. Thus these
models have no embedded seven-group at all. This proves the inspection for
every two-subgroup of automorphisms without transferring component membership
from the common fixed subgroup to a single involution's fixed subgroup.

The resulting theorems need neither simplicity nor strong quasithinness.
Their field-degree bounds match the corresponding Theorem C constructors.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252/PDF p.263; Theorem C and Remark A.2.4, printed p.33/PDF p.44.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
variable {S : Type*} [Group S]

/-- Both seven models contain an order-five element conjugated to its square. -/
theorem seven_has_five_square_pair {L : Subgroup S} (h : IsSeven L) :
    ∃ x y : L, orderOf x = 5 ∧ y * x * y⁻¹ = x ^ 2 := by
  obtain ⟨x, y, hx, hxy⟩ := alternatingGroup.exists_five_cycle_square_pair_seven
  rcases h with ha | hc
  · obtain ⟨e⟩ := ha
    refine ⟨e.symm x, e.symm y, ?_, ?_⟩
    · simpa only [MulEquiv.orderOf_eq] using hx
    · simpa only [map_mul, map_inv, map_pow] using congrArg e.symm hxy
  · obtain ⟨_, ⟨c⟩, ⟨e⟩⟩ := hc
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = center L := by
      ext a
      change e (QuotientGroup.mk a) = 1 ↔ a ∈ center L
      rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have hc : Nat.card (center L) = 3 ^ 1 := by
      rw [Nat.card_congr c.toEquiv]
      simp
    exact q.exists_five_cycle_square_lift hq hk.le
      (hk ▸ IsPGroup.of_card hc) x y hx hxy

/-- Central three-group quotients of faithful degree-three matrix groups
away from characteristic five exclude every embedded seven-group. -/
theorem inspection_of_matrix_central_quotient
    {F E Q : Type*} [Field F] [Group E] [Group Q]
    (rho : E →* GL (Fin 3) F) (hrho : Function.Injective rho)
    (hfive : (5 : F) ≠ 0) (q : E →* Q) (hq : Function.Surjective q)
    (hz : q.ker ≤ center E) (hk : IsPGroup 3 q.ker)
    (e : S ≃* Q) : SevenActionInspection S := by
  intro P _ L _ _ hL
  obtain ⟨x, y, hx, hxy⟩ := seven_has_five_square_pair hL
  let f := e.toMonoidHom.comp L.subtype
  have hf : Function.Injective f := e.injective.comp L.subtype_injective
  have hfx : orderOf (f x) = 5 := (orderOf_injective f hf x).trans hx
  have hfxy : f y * f x * (f y)⁻¹ = (f x) ^ 2 := by
    simpa only [map_mul, map_inv, map_pow] using congrArg f hxy
  obtain ⟨a, b, ha, hab⟩ := q.exists_five_cycle_square_lift hq hz hk (f x) (f y) hfx hfxy
  exact (Representation.FiveCycleDegreeThree.not_conjugate_square_of_matrix
    rho hrho hfive a b ha hab).elim

/-- The complete binary PSU₃ branch, for every permitted field and Hermitian form. -/
theorem unitary_rank_one {f : ℕ} (_hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSU S 3 (2 ^ f)) : SevenActionInspection S := by
  obtain ⟨F, _, _, J, hcard, _, ⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
    (by simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  exact inspection_of_matrix_central_quotient J.specialSubgroup.subtype
    J.specialSubgroup.subtype_injective
    (CharP.cast_ne_zero_of_ne_of_prime F (by decide : Nat.Prime 5) (by decide : 2 ≠ 5))
    J.specialToProjective J.specialToProjective_surjective
    J.specialToProjective_ker_le_center
    (fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩) e

/-- The complete binary PSL₃ branch, including the field of order two. -/
theorem linear_rank_two {f : ℕ} (_hf : 1 ≤ f)
    (h : ClassicalGroup.IsPSL S 3 (2 ^ f)) : SevenActionInspection S := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let q : SL(3, F) →* PSL(3, F) := QuotientGroup.mk' (center SL(3, F))
  have hk : q.ker = center SL(3, F) := QuotientGroup.ker_mk' _
  have hcube (x : center SL(3, F)) : x ^ 3 = 1 := by
    let c := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 3)
    apply c.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    exact (c x).property
  have hp : IsPGroup 3 q.ker := by
    rw [hk]
    exact fun x => ⟨1, by simpa using hcube x⟩
  exact inspection_of_matrix_central_quotient Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective
    (CharP.cast_ne_zero_of_ne_of_prime F (by decide : Nat.Prime 5) (by decide : 2 ≠ 5))
    q (QuotientGroup.mk'_surjective _) hk.le hp e

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
