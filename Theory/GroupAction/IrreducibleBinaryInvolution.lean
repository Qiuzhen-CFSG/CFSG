module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.OrderOfElement

/-!
# A commuting involution on an irreducible binary group

The fixed subgroup of an involution commuting with an irreducible action is
invariant, hence trivial or full. In characteristic two every displacement is
fixed; thus a trivial fixed subgroup also forces the action to be trivial.
This supplies the centralizing case of Aschbacher--Smith,
*The Classification of Quasithin Groups*, D.2.12(3), `refs/quasithin.pdf`,
printed pp.183–184.
-/

open scoped IsMulCommutative

/-- An actor with square one commuting with an irreducible action on an
elementary abelian two-group fixes the whole group. -/
public theorem fixes_of_sq_eq_one_of_commuting_irreducible_binary {A T W : Type*} [Group A] [Group T] [Group W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction A W] [MulDistribMulAction T W]
    (t : T) (ht : t ^ 2 = 1)
    (hcomm : ∀ a : A, ∀ w : W, a • (t • w) = t • (a • w))
    (hirred : ∀ D : Subgroup W, IsInvariant A W D → D = ⊥ ∨ D = ⊤) :
    ∀ w : W, t • w = w := by
  let D := FixedPoints.subgroup (Subgroup.zpowers t) W
  have hD (w : W) : w ∈ D ↔ t • w = w := by
    constructor
    · intro hw
      exact hw ⟨t, Subgroup.mem_zpowers t⟩
    · intro hw s
      exact smul_eq_self_of_mem_zpowers s.property hw
  have hinv : IsInvariant A W D := by
    constructor
    intro a w
    rw [hD, hD, ← hcomm]
    exact (smul_left_cancel_iff a).symm
  rcases hirred D hinv with hb | htop
  · intro w
    have hwInv (w : W) : w⁻¹ = w := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) w
    have hdelta : w⁻¹ * t • w ∈ D := by
      rw [hD]
      simp only [smul_mul', ← mul_smul,
        show t * t = 1 by simpa only [pow_two] using ht, one_smul, hwInv]
      exact mul_comm _ _
    exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hb ▸ hdelta))).symm
  · intro w
    exact (hD w).mp (htop ▸ Subgroup.mem_top w)

