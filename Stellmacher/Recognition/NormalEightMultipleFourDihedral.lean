module

public import Stellmacher.Recognition.NormalEightMultipleFourReduction
public import Theory.GroupTheory.PGroup.DihedralDihedralCentralFactorSylow

/-!
# Excluding a dihedral centralizer without a normal eight

Suppose distinct normal elementary fours generate a dihedral central factor
in a Sylow two-subgroup containing an elementary eight but no normal elementary
eight. If the centralizer has dihedral model `DihedralGroup m`, then `m` is a
power of two with exponent at least two. The rotation order gives the power
of two. The cyclic case is excluded by the existing transfer argument, and
`m = 2` would make the whole centralizer a forbidden normal elementary four.

The intrinsic dihedral central-product calculation then supplies a central
involution which is the square of every element of order four, with a fourth
root commuting with every Sylow element. The square-fusion theorem makes this
involution weakly closed, contradicting simple-group involution fusion.

Source: the reduction toward Janko–Thompson, Math. Z. 113 (1970), result 1.2,
printed pp.385–386; see `NormalEightMultipleFour` for the earlier branches.
-/

open Subgroup

private theorem dihedral_parameter_of_no_normal_four
    {C : Type*} [Group C] [Finite C] (hC : IsPGroup 2 C)
    (hno : ¬ ∃ U : Subgroup C, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (hnc : ¬ IsCyclic C) (m : ℕ) (f : C ≃* DihedralGroup m) :
    ∃ k : ℕ, 2 ≤ k ∧ m = 2 ^ k := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hC.of_equiv f).exists_orderOf_eq_pow (DihedralGroup.r 1)
  rw [DihedralGroup.orderOf_r_one] at hk
  refine ⟨k, ?_, hk⟩
  by_contra! hsmall
  have hcases : k = 0 ∨ k = 1 := by omega
  rcases hcases with rfl | rfl
  · have hm : m = 1 := by simpa using hk
    let : IsCyclic (DihedralGroup m) := DihedralGroup.isCyclic_iff.mpr hm
    exact hnc (isCyclic_of_injective f.toMonoidHom f.injective)
  · have hm : m = 2 := by simpa using hk
    let e : (⊤ : Subgroup C) ≃* DihedralGroup m := Subgroup.topEquiv.trans f
    have he : Monoid.exponent (⊤ : Subgroup C) = 2 := by
      rw [Monoid.exponent_eq_of_mulEquiv e, hm, IsKleinFour.exponent_two]
    let : IsElementaryAbelian 2 (⊤ : Subgroup C) := {
      toIsMulCommutative := ⟨⟨mul_comm_of_exponent_two he⟩⟩
      exponent_dvd_p := by rw [he] }
    apply hno
    refine ⟨⊤, inferInstance, inferInstance, ?_⟩
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm]

namespace Stellmacher.Recognition.NormalEightMultipleFour

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The remaining dihedral centralizer has a rotation subgroup whose order
is divisible by four. No bound on arbitrary elementary subgroups is used. -/
public theorem dihedral_centralizer_parameter_of_distinct_normal_fours
    (S : Sylow 2 G) (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W F : Subgroup S) [W.Normal] [F.Normal]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 F]
    (hW : Nat.card W = 4) (hF : Nat.card F = 4) (hne : F ≠ W)
    (e : (W ⊔ F : Subgroup S) ≃* DihedralGroup 4)
    (hgen : W ⊔ F ⊔ centralizer ((W ⊔ F : Subgroup S) : Set S) = ⊤)
    (m : ℕ) (f : centralizer ((W ⊔ F : Subgroup S) : Set S) ≃* DihedralGroup m) :
    ∃ k : ℕ, 2 ≤ k ∧ m = 2 ^ k := by
  apply dihedral_parameter_of_no_normal_four (S.isPGroup'.to_subgroup _)
    (no_normal_four_centralizer_of_distinct_normal_fours_of_no_normal_eight
      S.isPGroup' hno W F hW hF hne.symm) _ m f
  intro hcyc
  let : IsCyclic (centralizer ((W ⊔ F : Subgroup S) : Set S)) := hcyc
  exact false_of_cyclic_centralizer S A hA hno (W ⊔ F) e hgen

/-- The dihedral-centralizer alternative for distinct normal fours is
impossible: its common central involution is weakly closed in the Sylow,
contradicting Z-star for a nonsolvable simple group. -/
public theorem false_of_dihedral_centralizer
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (W F : Subgroup S) [W.Normal] [F.Normal]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 F]
    (hW : Nat.card W = 4) (hF : Nat.card F = 4) (hne : F ≠ W)
    (e : (W ⊔ F : Subgroup S) ≃* DihedralGroup 4)
    (hgen : W ⊔ F ⊔ centralizer ((W ⊔ F : Subgroup S) : Set S) = ⊤)
    (m : ℕ) (f : centralizer ((W ⊔ F : Subgroup S) : Set S) ≃* DihedralGroup m) :
    False := by
  obtain ⟨k, hk, hm⟩ := dihedral_centralizer_parameter_of_distinct_normal_fours
    S A hA hno W F hW hF hne e hgen m f
  have hmpos : 0 < m := by rw [hm]; positivity
  have hdiv : 4 ∣ m := by
    rw [hm]
    exact pow_dvd_pow 2 hk
  obtain ⟨z, hz, hzC, hsquare, hroot⟩ :=
    dihedral_dihedral_factor_square_data S.isPGroup' (W ⊔ F) e hgen m hmpos hdiv f
  obtain ⟨t, hne, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := hconj
    rw [← Subgroup.orderOf_coe, ← hg.orderOf_eq (g : G), Subgroup.orderOf_coe, hz]
  exact hne (S.eq_of_isConj_of_unique_involution_square z hzC hsquare
    (fun t _ => hroot t) t ht hconj.symm)

end Stellmacher.Recognition.NormalEightMultipleFour
