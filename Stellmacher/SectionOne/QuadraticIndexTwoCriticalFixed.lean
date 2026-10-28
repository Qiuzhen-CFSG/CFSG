module

public import Stellmacher.SectionOne.FixedIndexTwoOffender
public import Stellmacher.SectionOne.LemmaOneSeven

/-!
# The critical subgroup fixes a quadratic index-two commutator

Under the faithful Section One action hypotheses, let `Y` lie in the Sylow
two-subgroup `U`. If its full fixed subgroup has index two and its action is
quadratic, then `J(V,U)` is nontrivial and fixes `[V,Y]` pointwise.

The index-two quadratic action makes `Y` a nontrivial offender, so it lies in
`J(V,U)`. The proved conclusion (1.7)(b) makes `J(V,U)` elementary abelian.
For each actor in `Y`, the displacement homomorphism on `V` has kernel
containing the full `Y`-fixed subgroup; hence its image has order dividing two.
Every element of `J(V,U)` commutes with that actor and therefore preserves its
displacement image. An action on a subgroup of order at most two fixes that
subgroup pointwise. The displacement images generate `[V,Y]`.

This is the intrinsic barred-action step used in Stellmacher (9.2), journal
p. 48, using (1.7), journal p. 19, in
`refs/latex/stellmacher-n-group.tex`. It uses precisely the supplied module
action; no fixedness under the whole Sylow subgroup is assumed.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem smul_displacement_eq_of_commute_fixed_index_two
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (Y : Subgroup K)
    (hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V))
    (j : K) (y : Y) (hcomm : j * (y : K) = (y : K) * j) (v : V) :
    j • (v⁻¹ * (y : K) • v) = v⁻¹ * (y : K) • v := by
  let d : V →* V :=
    { toFun := fun w => w⁻¹ * ((y : K) • w)
      map_one' := by simp
      map_mul' := by
        intro w z
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hker : FixedPoints.subgroup Y V ≤ d.ker := by
    intro w hw
    change w⁻¹ * ((y : K) • w) = 1
    have hwy : (y : K) • w = w := (FixedPoints.mem_subgroup _ _ _).mp hw y
    rw [hwy, inv_mul_cancel]
  have hidx : (FixedPoints.subgroup Y V).index = 2 := by
    have h := (FixedPoints.subgroup Y V).card_mul_index
    rw [hindex] at h
    have hp : 0 < Nat.card (FixedPoints.subgroup Y V) := Nat.card_pos
    nlinarith
  have hcard : Nat.card d.range ∣ 2 := by
    rw [← Subgroup.index_ker]
    exact hidx ▸ Subgroup.index_dvd_of_le hker
  have hdcomm (w : V) : d (j • w) = j • d w := by
    change (j • w)⁻¹ * ((y : K) • (j • w)) = j • (w⁻¹ * ((y : K) • w))
    rw [smul_mul', smul_inv', ← mul_smul, ← mul_smul, hcomm]
  change j • d v = d v
  by_cases hv : d v = 1
  · simp [hv]
  have hcardne : Nat.card d.range ≠ 1 := by
    intro h
    have hb : d.range = ⊥ := Subgroup.card_eq_one.mp h
    exact hv (Subgroup.mem_bot.mp (hb ▸ (show d v ∈ d.range from ⟨v, rfl⟩)))
  have hcardtwo : Nat.card d.range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h | h
    · exact (hcardne h).elim
    · exact h
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : d.range)).mp hcardtwo
  let a : d.range := ⟨d v, ⟨v, rfl⟩⟩
  let b : d.range := ⟨j • d v, ⟨j • v, hdcomm v⟩⟩
  have ha : a ≠ 1 := fun h => hv (congrArg Subtype.val h)
  have hb : b ≠ 1 := by
    intro h
    have hval : j • d v = j • (1 : V) := by simpa [b] using congrArg Subtype.val h
    exact hv ((MulAction.injective j) hval)
  exact congrArg Subtype.val ((hz b hb).trans (hz a ha).symm)

/-- A quadratic index-two actor lies in the nontrivial critical subgroup,
which fixes its full action commutator. -/
public theorem oneJ_fixed_commutator_of_quadratic_index_two
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (U : Sylow 2 K) (Y : Subgroup K)
    (hYU : Y ≤ (U : Subgroup K))
    (hindex : Nat.card V = 2 * Nat.card (FixedPoints.subgroup Y V))
    (hquad : commutatorAction Y V ≤ FixedPoints.subgroup Y V) :
    oneJ (V := V) (U : Subgroup K) ≠ ⊥ ∧
      commutatorAction Y V ≤ FixedPoints.subgroup
        (oneJ (V := V) (U : Subgroup K)) V := by
  obtain ⟨hY, hYne⟩ := oneA_of_quadratic_fixed_index_two h U Y hYU hindex hquad
  have hYJ : Y ≤ oneJ (V := V) (U : Subgroup K) := le_sSup hY
  have hJne : oneJ (V := V) (U : Subgroup K) ≠ ⊥ := by
    intro hJ
    exact hYne (le_bot_iff.mp (hJ ▸ hYJ))
  let : IsElementaryAbelian 2 (oneJ (V := V) (U : Subgroup K)) :=
    (lemma_one_seven h U hJne).part_b.2.2.1
  refine ⟨hJne, ?_⟩
  rw [commutatorAction_eq_closure]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨y, v, rfl⟩
  apply (FixedPoints.mem_subgroup _ _ _).mpr
  intro j
  have hc : (j : K) * (y : K) = (y : K) * (j : K) :=
    congrArg Subtype.val (mul_comm j (⟨y, hYJ y.property⟩ : oneJ (V := V) (U : Subgroup K)))
  exact smul_displacement_eq_of_commute_fixed_index_two Y hindex j y hc v

end Stellmacher.SectionOne
