module

public import GorensteinWalter.SL2SchurTwoCover
public import Theory.SpecificGroups.SL2.PSL2ThreeCentralCover

/-!
# Nonsplit cyclic central two-covers of PSL2

For every finite field of odd prime-power order, a nonsplit central extension
of PSL2 by a nontrivial cyclic two-group contains a normal SL2 subgroup.
That subgroup generates the original extension together with the central
kernel, and intersects the kernel in exactly two elements.

At field order three, the binary tetrahedral construction gives the subgroup
inside the original extension. At larger odd orders, the two-primary cover
comparison identifies the derived subgroup with SL2; perfectness of the
projective quotient gives generation. In particular field order nine is
included. This assembles the Schur [26] input used in ABG Chapter II,
Section 3, Proposition 2 (article p.22).
-/

namespace Matrix.ProjectiveSpecialLinearGroup

/-- A nonsplit cyclic central two-cover of odd PSL2 contains its normal
SL2 cover, with central intersection of order two. -/
public theorem exists_sl2_of_nonsplit_cyclic_two_central_extension
    {E : Type*} [Group E] [Finite E]
    (F : Type*) [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (Z : Subgroup E) [Z.Normal]
    (hZnontrivial : Z ≠ ⊥) (hZcyclic : IsCyclic Z)
    (hZtwo : IsPGroup 2 Z) (hZcentral : Z ≤ Subgroup.center E)
    (e : E ⧸ Z ≃* ProjectiveSpecialLinearGroup (Fin 2) F)
    (hnonsplit : ¬ ∃ s : (E ⧸ Z) →* E,
      (QuotientGroup.mk' Z).comp s = MonoidHom.id (E ⧸ Z)) :
    ∃ L : Subgroup E, L.Normal ∧
      Nonempty (L ≃* SpecialLinearGroup (Fin 2) F) ∧
      Z ⊔ L = ⊤ ∧ Nat.card (Z ⊓ L : Subgroup E) = 2 := by
  by_cases hthree : Nat.card F = 3
  · exact exists_sl2_of_nonsplit_cyclic_two_cover_card_three hthree Z
      hZnontrivial hZcyclic hZtwo hZcentral e hnonsplit
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _, hpodd, _, hcard⟩ := hF
    rw [hcard]
    exact hpodd.pow
  have hgt : 3 < Nat.card F := by
    have hnontrivial : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨hequiv, hcard⟩ :=
    commutator_equiv_specialLinearGroup_of_nonsplit_two_cover
      F hodd hgt Z hZcyclic hZnontrivial hZtwo hZcentral e hnonsplit
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F hgt
  let : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := GorensteinWalter.sl2ProjectiveProjection F)
      (GorensteinWalter.sl2ProjectiveProjection_surjective F)
  let : Group.IsPerfect (E ⧸ Z) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨_root_.commutator E, inferInstance, hequiv,
    CentralExtension.quotientKernel_sup_commutator_eq_top Z, hcard⟩

end Matrix.ProjectiveSpecialLinearGroup

