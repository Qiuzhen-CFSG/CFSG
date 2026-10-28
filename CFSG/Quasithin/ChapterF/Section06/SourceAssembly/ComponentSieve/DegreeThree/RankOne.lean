module

public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.WreathedThirtyTwo
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Rank-one exclusions for the full wreathed two-part

An odd PSL₂ Sylow subgroup with at least 32 elements contains a rotation
of order at least 16, so it cannot have exponent dividing eight. An even
PSL₂ Sylow subgroup is the additive field group and is commutative. Both
possibilities are therefore excluded for a section retaining the entire
order-32 Sylow subgroup C₄ wreath C₂. The section consumer uses the literal
map K → K/Z(K), without discarding its central kernel.

Source: Aschbacher--Smith F.6.18(10), p.310, and the usual PSL₂ Sylow models.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- Odd rank one is incompatible with a large Sylow of exponent at most eight. -/
theorem not_odd_psl2_of_large_sylow_exponent_eight
    (P : Sylow 2 G) (hcard : 32 ≤ Nat.card P) (hexp : ∀ x : P, x ^ 8 = 1)
    {q : ℕ} (hq : GorensteinWalter.IsOddPrimePower q) :
    ¬ ClassicalGroup.IsPSL G 2 q := by
  rintro ⟨F, _, _, hF, ⟨j⟩⟩
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let eP : P ≃* Q := (P : Subgroup G).equivMapOfInjective j.toMonoidHom j.injective
  obtain ⟨m, _, ⟨eQ⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model
    F (hF ▸ hq) Q
  let e := eP.trans eQ
  have hc : Nat.card P = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hr : (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ 8 = 1 := by
    simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using
      congrArg e (hexp (e.symm (DihedralGroup.r 1)))
  have hd : 2 ^ m ∣ 8 := by
    rw [← DihedralGroup.orderOf_r_one (n := 2 ^ m)]
    exact orderOf_dvd_of_pow_eq_one hr
  have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
  omega

/-- Every binary PSL₂ Sylow is commutative, independently of its field degree. -/
theorem not_binary_psl2_of_noncommutative_sylow
    (P : Sylow 2 G) (hnc : ¬ IsMulCommutative P) {f : ℕ} :
    ¬ ClassicalGroup.IsPSL G 2 (2 ^ f) := by
  rintro ⟨F, _, _, hF, ⟨j⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let eP : P ≃* Q := (P : Subgroup G).equivMapOfInjective j.toMonoidHom j.injective
  let S := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.standardSylow F
  let a : Multiplicative F ≃* S :=
    (MonoidHom.ofInjective
      (Matrix.ProjectiveSpecialLinearGroup.OddBorel.unipotentHom_injective F)).trans
      (MulEquiv.subgroupCongr
        (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.coe_standardSylow F).symm)
  let e : P ≃* Multiplicative F := (eP.trans (Q.equiv S)).trans a.symm
  apply hnc
  exact isMulCommutative_iff.mpr fun x y => e.injective (by
    simpa only [map_mul] using mul_comm (e x) (e y))

/-- The original central quotient cannot be odd PSL₂ when it uses the full
wreathed ambient two-part. The order equality is deliberately retained. -/
theorem not_odd_psl2_full_wreathed_central_quotient
    (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo) (K : Subgroup G)
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card P = 32)
    {q : ℕ} (hq : GorensteinWalter.IsOddPrimePower q) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q := by
  have hi := wreathedThirtyTwo_section_invariants T eT K
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _) P hP
  exact not_odd_psl2_of_large_sylow_exponent_eight P hP.ge hi.1 hq

/-- The same literal section excludes every binary rank-one entry. -/
theorem not_binary_psl2_full_wreathed_central_quotient
    (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo) (K : Subgroup G)
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card P = 32) {f : ℕ} :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ f) := by
  have hi := wreathedThirtyTwo_section_invariants T eT K
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _) P hP
  exact not_binary_psl2_of_noncommutative_sylow P hi.2

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
