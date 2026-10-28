module
public import Theory.SpecificGroups.HeisenbergPrime.CyclicOuterExclusion
public import Theory.SpecificGroups.PSL3.BinaryCenterRank
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.CyclicNormal
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner

/-!
# Centerless binary SL₃ excludes ternary Heisenberg automorphisms

Trivial center makes the diagonal outer image trivial: its order divides
both three and the field-unit order, whose gcd is one. Standard automorphism
coverage then leaves the cyclic field image and a commuting graph involution,
so every outer three-subgroup is cyclic. The existing quadratic-torus theorem
gives the same cyclicity for inner three-subgroups. The exponent-three
Heisenberg group cannot act faithfully through this cyclic-by-cyclic structure.

Source: the SL₃ row in Aschbacher–Smith 14.7.26, printed p.1053;
GLS3 2.5.12 supplies the automorphism description used in the imported proofs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace Matrix.SL3
open Matrix.PSL3.OuterSolvable
variable {F : Type*} [Field F] [Finite F]

private theorem diagonal_bot (hz : center SL(3,F) = ⊥) : innerDiagonalOuter F = ⊥ := by
  classical
  let := Fintype.ofFinite F
  let d : GL (Fin 3) F →* Fˣ := GeneralLinearGroup.det
  let e := QuotientGroup.quotientKerEquivOfSurjective d GeneralLinearGroup.det_surjective
  let f : GL (Fin 3) F ⧸ d.ker →* innerDiagonalOuter F :=
    QuotientGroup.lift d.ker (linearOuterAction F).rangeRestrict (fun g hg => by
      apply Subtype.ext
      exact det_ker_le_linearOuterAction_ker F hg)
  have hf : Function.Surjective f := by
    rintro ⟨_,g,rfl⟩
    exact ⟨QuotientGroup.mk g,rfl⟩
  have hd : Nat.card (innerDiagonalOuter F) ∣ Nat.card F - 1 := by
    have hh := card_dvd_of_surjective f hf
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card (α := Fˣ),Fintype.card_units,
      ←Nat.card_eq_fintype_card (α := F)] at hh
    exact hh
  have h3 : Nat.card (innerDiagonalOuter F) ∣ 3 := by
    let := innerDiagonalOuter_isCyclic F
    rw [←IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨_,g,rfl⟩
    apply Subtype.ext
    change QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F g) ^ 3 = 1
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Matrix.PSL3.CartanActions.ResidualInner.linearConj_cube_inner g)
  have hc : Nat.gcd 3 (Nat.card F - 1) = 1 := by
    have hh := Atlas.ExceptionalSupport.card_sl_center (ι := Fin 3) (F := F)
    simpa only [hz,card_bot,Fintype.card_fin] using hh.symm
  exact card_eq_one.mp (Nat.dvd_one.mp (hc ▸ Nat.dvd_gcd h3 hd))

private theorem outer_three_rank {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hz : center SL(3,F) = ⊥) : primeRank 3 (MulAut.Outer PSL(3,F)) ≤ 1 := by
  have hcover := standard_eq_top_of_two_power_card F hn hF
  have hD := diagonal_bot hz
  let := innerDiagonalOuter_normal_of_coverage F hcover
  let := outerDiagonalQuotient_isMulCommutative_of_coverage F hcover
  let e : MulAut.Outer PSL(3,F) ≃* (MulAut.Outer PSL(3,F) ⧸ innerDiagonalOuter F) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hD.symm)
  let : IsMulCommutative (MulAut.Outer PSL(3,F)) :=
    ⟨⟨fun x y => e.injective ((e.map_mul x y).trans
      ((IsMulCommutative.is_comm.comm (e x) (e y)).trans (e.map_mul y x).symm))⟩⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let f := q.comp (fieldAction F)
  have hgen : f.range ⊔ zpowers (q (graph F)) = ⊤ := by
    have hh := congrArg (Subgroup.map q) hcover
    rw [standard,Subgroup.map_sup,Subgroup.map_sup,innerDiagonal_map_outer,hD,bot_sup_eq,
      MonoidHom.map_zpowers,←MonoidHom.range_comp] at hh
    exact hh.trans (map_top_of_surjective _ (QuotientGroup.mk'_surjective _))
  have ht : q (graph F) ^ 2 = 1 := by rw [←map_pow,graph_sq,map_one]
  let := BenderSuzuki.MatrixGroups.HermitianForm.finiteFieldAut_isCyclic (E := F)
  let : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let P := (default : Sylow 3 (MulAut.Outer PSL(3,F)))
  exact P.primeRank_le_one_of_isCyclic
    (isCyclic_pSubgroup_of_cyclic_sup_involution f.range _ ht hgen 3 (by decide)
      (P : Subgroup (MulAut.Outer PSL(3,F))) P.isPGroup')

/-- Every centerless binary SL₃ model excludes the faithful Heisenberg action. -/
theorem no_heisenberg_automorphism_action {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hz : center SL(3,F) = ⊥)
    (f : HeisenbergPrime 3 →* MulAut SL(3,F)) (hf : Function.Injective f) : False := by
  let e : SL(3,F) ≃* PSL(3,F) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  have ho : primeRank 3 (MulAut.Outer SL(3,F)) ≤ 1 := by
    rw [primeRank_equiv 3 (MulAut.outerCongr e)]
    exact outer_three_rank hn hF hz
  exact HeisenbergPrime.no_faithful_action_of_rank_one hz
    (binary_threeRank_le_one_of_center_eq_bot hF hz) ho f hf
end Matrix.SL3
