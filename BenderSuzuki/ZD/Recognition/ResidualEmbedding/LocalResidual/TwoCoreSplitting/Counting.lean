module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.Algebra

/-!
# Assembly of the Section 17 counting witness

GLS, Volume 4, Chapter 2, Lemmas 17.1–17.5 give a rational centralizer
ratio a. In the linear case their identities are r − 1 = q((q + 1)a + 1)
and a(q + 1) = q − 1. These give r = q² + 1 without any assertion that
a is integral. Double transitivity then gives the internal index in M.
The odd inverter comes from the geometric data of Lemma 17.2(c,d).

This module assembles these inputs into `TwoCoreCountingData`. Constructing
`TwoCoreLocalData` and proving the linear model and rational counting identities
from the original residual hypotheses remain separate obligations; the theorem
below is conditional and does not assert their existence.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Conditional assembly with the actual local model, rational ratio, and
noncentral odd subgroup. The index and inverter are derived, not assumed. -/
public theorem twoCoreCountingData_of_local_linear_count
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (d : TwoCoreLocalData Z M) (n : ℕ) (hn : 0 < n) (a : ℚ)
    (hcount : (Nat.card (G ⧸ M) : ℚ) - 1 =
      (2 ^ n : ℚ) * (((2 ^ n : ℚ) + 1) * a + 1))
    (hratio : a * ((2 ^ n : ℚ) + 1) = (2 ^ n : ℚ) - 1)
    (hlinear : Nonempty ((Subgroup.closure
      ((Subgroup.centralizer ({((d.u : M) : G)} : Set G)).subtype ⁻¹' Z)) ≃*
        MatrixGroups.PSL2BinaryMatrixGroup n)) :
    Nonempty (TwoCoreCountingData Z M) := by
  have hdegree : Nat.card (G ⧸ M) = (2 ^ n) ^ 2 + 1 := by
    have hc : (Nat.card (G ⧸ M) : ℚ) = (2 ^ n : ℚ) ^ 2 + 1 := by
      rw [mul_comm ((2 ^ n : ℚ) + 1) a, hratio] at hcount
      nlinarith [hcount]
    exact_mod_cast hc
  obtain ⟨x, hxodd, hxne, hinv⟩ := d.exists_odd_inverted h
  exact ⟨{
    q := 2 ^ n
    one_lt := one_lt_pow₀ (by decide) (by omega)
    binary := ⟨n, rfl⟩
    t := d.t
    t_mem := d.t_mem
    t_not_mem := d.t_not_mem
    degree := hdegree
    pair_index := by
      rw [residualPairIn_index_eq_degree_sub_one ha d.t_not_mem, hdegree]
      omega
    u := d.u
    u_order := d.u_order
    commutes_t := d.commutes_t
    z := d.z
    z_mem := d.z_mem
    commutes_z := d.commutes_z
    linear_centralizer := ⟨n, rfl, hlinear⟩
    x := x
    x_odd := hxodd
    x_ne := hxne
    inverts := hinv }⟩

end BenderSuzuki.ZD
