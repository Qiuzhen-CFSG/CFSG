module

public import Theory.SpecificGroups.Suzuki.SubgroupOvoid

/-!
# The involution orbit of a Suzuki subgroup

The points fixed by involutions of a subgroup form an invariant subset of the
Suzuki ovoid. This subset is a single orbit whenever it is nonempty: each
Sylow 2-subgroup fixes a point because the ovoid has odd cardinality, an
involution makes that point unique, and Sylow conjugacy gives transitivity.

This is the orbit construction used in the subgroup analysis behind
Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), p. 194. It does not assert
that the orbit is doubly transitive; that requires the further subgroup
argument of Suzuki, *On a class of doubly transitive groups* (1962).
-/

namespace BenderSuzuki.MatrixGroups

/-- The ovoid points fixed by involutions in `H`. -/
@[expose] public def suzukiInvolutionSubaction {m : ℕ}
    (H : Subgroup (SuzukiMatrixGroup m)) : SubMulAction H (SuzukiOvoid m) where
  carrier := {a | ∃ t : H, orderOf t = 2 ∧ t • a = a}
  smul_mem' g := by
    rintro a ⟨t, ht, ha⟩
    refine ⟨MulAut.conj g t, (MulEquiv.orderOf_eq _ _).trans ht, ?_⟩
    change (g * t * g⁻¹) • (g • a) = g • a
    simp only [mul_smul, inv_smul_smul, ha]

/-- Membership records an actual subgroup involution and its fixed point. -/
public theorem mem_suzukiInvolutionSubaction {m : ℕ}
    (H : Subgroup (SuzukiMatrixGroup m)) (a : SuzukiOvoid m) :
    a ∈ suzukiInvolutionSubaction H ↔ ∃ t : H, orderOf t = 2 ∧ t • a = a :=
  Iff.rfl

/-- A subgroup involution gives a point of the involution subaction. -/
public theorem suzukiInvolutionSubaction_nonempty {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (t : H) (ht : orderOf t = 2) :
    Nonempty (suzukiInvolutionSubaction H) := by
  obtain ⟨a, ha, _⟩ := suzukiOvoid_involution_unique_fixed m hm t.val
    ((Subgroup.orderOf_coe t).trans ht)
  exact ⟨⟨a, t, ht, ha⟩⟩

/-- Every 2-subgroup of `H` fixes a point on the odd-cardinality ovoid. -/
public theorem suzukiSubgroup_twoGroup_fixed_point {m : ℕ}
    (H : Subgroup (SuzukiMatrixGroup m)) (P : Subgroup H) (hP : IsPGroup 2 P) :
    ∃ a : SuzukiOvoid m, ∀ t : P, (t : H) • a = a := by
  have hodd : ¬ 2 ∣ Nat.card (SuzukiOvoid m) := by
    rw [suzukiOvoid_card]
    have heven : Even (2 ^ (2 * m + 1)) :=
      even_two.pow_of_ne_zero (by omega)
    exact (heven.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)).add_one.not_two_dvd_nat
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (SuzukiOvoid m) hodd
  exact ⟨a, MulAction.mem_fixedPoints.mp ha⟩

/-- If an involution of a 2-subgroup fixes `a`, the whole 2-subgroup fixes `a`. -/
public theorem suzukiSubgroup_twoGroup_fixes_involution_point {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (P : Subgroup H) (hP : IsPGroup 2 P)
    (t : H) (htP : t ∈ P) (ht : orderOf t = 2)
    (a : SuzukiOvoid m) (ha : t • a = a) :
    ∀ u : P, (u : H) • a = a := by
  obtain ⟨b, hb⟩ := suzukiSubgroup_twoGroup_fixed_point H P hP
  obtain ⟨c, _, hc⟩ := suzukiOvoid_involution_unique_fixed m hm t.val
    ((Subgroup.orderOf_coe t).trans ht)
  have hab : a = b := (hc a ha).trans (hc b (hb ⟨t, htP⟩)).symm
  simpa only [hab] using hb

/-- Sylow conjugacy makes the involution subaction transitive. This holds
for arbitrary subgroups, including solvable ones, and says nothing about
transitivity of a point stabilizer. -/
public theorem suzukiInvolutionSubaction_isPretransitive {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) :
    MulAction.IsPretransitive H (suzukiInvolutionSubaction H) := by
  constructor
  rintro ⟨a, t, ht, hta⟩ ⟨b, u, hu, hub⟩
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, ht]
    exact dvd_refl 2
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, hu]
    exact dvd_refl 2
  obtain ⟨P, htP⟩ := ht2.exists_le_sylow
  obtain ⟨Q, huQ⟩ := hu2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  have htgQ : MulAut.conj g t ∈ Q := by
    rw [← hg]
    exact ⟨t, htP (Subgroup.mem_zpowers t), rfl⟩
  have hfix := suzukiSubgroup_twoGroup_fixes_involution_point hm H Q Q.isPGroup'
    u (huQ (Subgroup.mem_zpowers u)) hu b hub ⟨MulAut.conj g t, htgQ⟩
  have horder : orderOf ((MulAut.conj g t : H) : SuzukiMatrixGroup m) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨c, _, hc⟩ := suzukiOvoid_involution_unique_fixed m hm _ horder
  have htga : (MulAut.conj g t : H) • (g • a) = g • a := by
    change (g * t * g⁻¹) • (g • a) = g • a
    simp only [mul_smul, inv_smul_smul, hta]
  exact ⟨g, Subtype.ext ((hc _ htga).trans (hc _ hfix).symm)⟩

end BenderSuzuki.MatrixGroups
