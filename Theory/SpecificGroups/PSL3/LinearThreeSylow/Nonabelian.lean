module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center

/-!
# Nonabelian Sylow two-subgroups of PSL₃ in characteristic two

A Sylow subgroup has order q³ and center of order q. For q > 1 these
orders differ, so the Sylow subgroup is nonabelian. This uses the actual
projective unipotent model and Sylow conjugacy.

Source: Aschbacher–Smith, E.6.11(3b), pp.249–250; used in the Cartan
centralizer obstruction in original 5.1.17, p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]
theorem sylow_not_isMulCommutative {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (S : Sylow 2 PSL(3,F)) : ¬IsMulCommutative S := by
  intro hc
  let := hc
  have hcenter := card_center_sylow F hn hF S
  have hcard : Nat.card S = (2^n)^3 := by
    rw [Nat.card_congr (S.equiv (unipotentSylow F hn hF)).toEquiv]
    exact (card_unipotent F).trans (congrArg (fun q : ℕ => q^3) hF)
  rw [show center S = ⊤ from center_eq_top,card_top,hcard] at hcenter
  have hp : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  nlinarith [sq_nonneg (2^n)]
end Matrix.PSL3.LinearThree
