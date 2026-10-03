module
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.Lemmas

/-!
# Fixed and commutator lines for an involution

An order-two group acting nontrivially on an elementary abelian group of
order four has a fixed subgroup of order two and an action commutator of
order two. For an arbitrary finite elementary two-group, the supporting
rank-nullity identity multiplies the fixed and commutator orders to the
module order, and the commutator lies in the fixed subgroup.

For the nonidentity actor x, the homomorphism v↦v⁻¹(x•v) has the fixed
subgroup as kernel and the action commutator as image. Its square is zero
in characteristic two, giving the containment. Cardinality then determines
both lines in the four-element case.

These ordinary finite-action facts were previously private inside the
local SL₂(2) coordinate proof of Stellmacher (1.6). They are shared with
the natural commutator-line argument in (4.6), Journal of Algebra 190
(1997), pp18--19 and26. The original coordinate theorem retains wrappers.
-/

open scoped IsMulCommutative
universe u

/-- Rank-nullity and quadraticity for an order-two action on an elementary two-group. -/
public theorem card_two_action_fixed_commutator_card_data
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [Nontrivial U] [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (x : Q) (hx : x ≠ 1 ∧ x ^ 2 = 1) (hcardQ : Nat.card Q = 2) :
    Nat.card U = Nat.card (FixedPoints.subgroup Q U) *
        Nat.card (commutatorAction Q U) ∧
      commutatorAction Q U ≤ FixedPoints.subgroup Q U := by
  classical
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  let d : U →* U :=
    { toFun := fun w => w⁻¹ * (x • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : d.ker = FixedPoints.subgroup Q U := by
    ext w
    constructor
    · intro hw
      rw [FixedPoints.mem_subgroup]
      intro r
      have hwx : x • w = w := by
        exact (eq_of_inv_mul_eq_one (MonoidHom.mem_ker.mp hw)).symm
      by_cases hr : r = 1
      · simp [hr]
      · obtain ⟨z, _hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : Q)).mp hcardQ
        have hre : r = x := (hzuniq r hr).trans (hzuniq x hx.1).symm
        simpa [hre] using hwx
    · intro hw
      rw [MonoidHom.mem_ker]
      have hwx := (FixedPoints.mem_subgroup (M := Q) (a := w)).1 hw x
      exact inv_mul_eq_one.mpr hwx.symm
  have hrange : d.range = commutatorAction Q U := by
    apply le_antisymm
    · intro z hz
      rcases hz with ⟨w, rfl⟩
      change w⁻¹ * (x • w) ∈ commutatorAction Q U
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨x, w, rfl⟩
    · rw [commutatorAction_eq_closure]
      refine (Subgroup.closure_le (K := d.range)).2 ?_
      intro z hz
      rcases hz with ⟨r, w, rfl⟩
      by_cases hr : r = 1
      · subst r
        exact ⟨1, by simp [d]⟩
      · obtain ⟨z, _hzne, hzuniq⟩ :=
          (Nat.card_eq_two_iff' (1 : Q)).mp hcardQ
        have hre : r = x := (hzuniq r hr).trans (hzuniq x hx.1).symm
        exact ⟨w, by simp [d, hre]⟩
  have hrange_le_ker : d.range ≤ d.ker := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two hxorder
    have hxx : x * x = 1 := by simpa [pow_two] using hx.2
    have hexp : Monoid.exponent U = 2 := IsElementaryAbelian.exponent_eq_prime
    have hpow2 (y : U) : y * y = 1 := by
      have h := Monoid.pow_exponent_eq_one y
      rw [hexp] at h
      simpa [pow_two] using h
    have hinvself (y : U) : y⁻¹ = y :=
      (eq_inv_of_mul_eq_one_left (hpow2 y)).symm
    change
      ((w⁻¹ * (x • w))⁻¹ *
        (x • (w⁻¹ * (x • w)))) = 1
    simp only [mul_inv_rev, smul_mul', smul_inv', ← mul_smul, hxx, one_smul]
    simp_rw [hinvself]
    calc
      (x • w) * w * ((x • w) * w) =
          (w * w) * ((x • w) * (x • w)) := by ac_rfl
      _ = 1 := by rw [hpow2, hpow2, one_mul]
  constructor
  · calc
      Nat.card U = Nat.card d.ker * d.ker.index := d.ker.card_mul_index.symm
      _ = Nat.card d.ker * Nat.card d.range := by rw [Subgroup.index_ker]
      _ = Nat.card (FixedPoints.subgroup Q U) *
          Nat.card (commutatorAction Q U) := by rw [hker, hrange]
  · simpa [hker, hrange] using hrange_le_ker

/-- A nontrivial involution action on four elements has a fixed line and a commutator line. -/
public theorem four_element_action_fixed_commutator_card_two
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (hQcard : Nat.card Q = 2) (hUcard : Nat.card U = 4)
    (hne : commutatorAction Q U ≠ ⊥) :
    Nat.card (FixedPoints.subgroup Q U) = 2 ∧
      Nat.card (commutatorAction Q U) = 2 := by
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hUcard]
    omega)
  obtain ⟨x, hxne, hxuniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQcard
  have hx : x ≠ 1 ∧ x ^ 2 = 1 := by
    refine ⟨hxne, ?_⟩
    have hxinv : x⁻¹ ≠ 1 := by simpa using hxne
    have heq : x⁻¹ = x := (hxuniq x⁻¹ hxinv).trans (hxuniq x hxne).symm
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := by rw [heq]
      _ = 1 := inv_mul_cancel x
  obtain ⟨hprod, hle⟩ :=
    card_two_action_fixed_commutator_card_data (Q := Q) (U := U) x hx hQcard
  have hcommGt : 1 < Nat.card (commutatorAction Q U) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hcommLe : Nat.card (commutatorAction Q U) ≤
      Nat.card (FixedPoints.subgroup Q U) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  rw [hUcard] at hprod
  have hcommDvd : Nat.card (commutatorAction Q U) ∣ 4 := by
    refine ⟨Nat.card (FixedPoints.subgroup Q U), ?_⟩
    simpa [Nat.mul_comm] using hprod
  have hcommLeFour : Nat.card (commutatorAction Q U) ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hcommDvd
  have hcommCard : Nat.card (commutatorAction Q U) = 2 := by
    interval_cases hc : Nat.card (commutatorAction Q U) <;> omega
  constructor
  · rw [hcommCard] at hprod
    omega
  · exact hcommCard

