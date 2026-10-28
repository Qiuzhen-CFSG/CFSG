module
public import Theory.GroupAction.FourAutomorphismOrbit
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# The image of a two-perfect action on a four-group

The automorphism group of an elementary four-group has order six. Its
Sylow three-subgroup has index two and is normal, so a two-perfect actor
has image in that subgroup. Thus every nontrivial such image has order
three. This supplies the residual-action comparison in Aschbacher--Smith,
15.1.29, printed p.1104, while retaining the original action homomorphism.
-/

public section
open Subgroup
namespace MulAut
variable {A W : Type*} [Group A] [Group W] [Finite W] [IsElementaryAbelian 2 W]
/-- A two-perfect action on an elementary four-group has image of order dividing three. -/
theorem card_range_dvd_three_of_twoPerfect
    (hA : IsPPerfect 2 A) (hW : Nat.card W = 4) (f : A →* MulAut W) :
    Nat.card f.range ∣ 3 := by
  let : Nontrivial W := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hW]; decide)
  let : IsKleinFour W := ⟨hW,IsElementaryAbelian.exponent_eq_prime⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 (MulAut W) := Classical.choice inferInstance
  have hc : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, IsKleinFour.card_mulAut]
    have hf6 : Nat.factorization 6 3 = 1 := by
      change Nat.factorization (2 * 3) 3 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    rw [hf6,pow_one]
  have hi : (P : Subgroup (MulAut W)).index = 2 := by
    have hh := (P : Subgroup (MulAut W)).index_mul_card
    rw [hc,IsKleinFour.card_mulAut] at hh
    omega
  let : (P : Subgroup (MulAut W)).Normal := normal_of_index_eq_two hi
  have hp : IsPGroup 2 (MulAut W ⧸ (P : Subgroup (MulAut W))) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one, Subgroup.index_eq_card] using hi)
  have hf := hA.hom_eq_one_of_isPGroup hp
    ((QuotientGroup.mk' (P : Subgroup (MulAut W))).comp f)
  have hle : f.range ≤ P := by
    rintro _ ⟨a,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hf a)
  exact hc ▸ card_dvd_of_le hle
end MulAut
