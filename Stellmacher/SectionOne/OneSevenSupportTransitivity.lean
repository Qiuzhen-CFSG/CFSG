module

public import Stellmacher.SectionOne.OneSevenSylowFixedCoordinate

/-!
# Transitivity on a canonical factor support

The derived order-three subgroup of a one-seven factor is fixed-point-free
on its order-four support, by coprime action. The identity and the three
orbit elements exhaust the support, proving transitivity on its nonidentity
vectors for the original action. No ambient normality of the factor is needed.

This supplies the factor-action input in Stellmacher (9.3), printed p50.
-/

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

universe u

private theorem three_action_support_transitive
    {F V : Type u} [Group F] [Group V] [Finite F] [Finite V]
    [MulDistribMulAction F V] (support : Subgroup V)
    (hF : Nat.card F = 3) (hcard : Nat.card support = 4)
    (hcomm : commutatorAction F V ≤ support)
    (hdisj : Disjoint (FixedPoints.subgroup F V) support)
    (vector : V) (hvector : vector ∈ support) (hne : vector ≠ 1)
    (target : V) (htarget : target ∈ support) (htne : target ≠ 1) :
    ∃ actor : F, actor • vector = target := by
  classical
  have hnfix : ¬ vector ∈ FixedPoints.subgroup F V := by
    intro hfix
    exact hne (hdisj.le_bot ⟨hfix, hvector⟩)
  obtain ⟨actor, hactor⟩ : ∃ actor : F, actor • vector ≠ vector :=
    not_forall.mp hnfix
  have hcube : actor ^ 3 = 1 := by
    rw [← hF]
    exact pow_card_eq_one' (x := actor)
  have hsquare : actor ^ 2 • vector ≠ vector := by
    intro heq
    apply hactor
    calc
      actor • vector = actor • (actor ^ 2 • vector) := by rw [heq]
      _ = actor ^ 3 • vector := by rw [← mul_smul]; congr 1; group
      _ = vector := by rw [hcube, one_smul]
  have hdistinct : actor ^ 2 • vector ≠ actor • vector := by
    intro heq
    apply hactor
    have hcancel := congrArg (fun value : V => actor⁻¹ • value) heq
    simpa only [← mul_smul, pow_two, inv_mul_cancel_left,
      inv_mul_cancel, one_smul] using hcancel
  have hpreserves (other : F) : other • vector ∈ support := by
    have hdelta : vector⁻¹ * (other • vector) ∈ support := by
      apply hcomm
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨other, vector, rfl⟩
    simpa only [mul_inv_cancel_left] using support.mul_mem hvector hdelta
  have hsmulne (other : F) : other • vector ≠ 1 := by
    intro heq
    apply hne
    have hcancel := congrArg (fun value : V => other⁻¹ • value) heq
    simpa only [inv_smul_smul, smul_one] using hcancel
  have hactorne := hsmulne actor
  have hsquarene := hsmulne (actor ^ 2)
  let points : Fin 4 → support :=
    ![1, ⟨vector, hvector⟩, ⟨actor • vector, hpreserves actor⟩,
      ⟨actor ^ 2 • vector, hpreserves (actor ^ 2)⟩]
  have hinj : Function.Injective points := by
    intro index other heq
    have hvalues := congrArg Subtype.val heq
    clear heq
    fin_cases index <;> fin_cases other <;> simp [points] at hvalues ⊢ <;>
      first | contradiction | exact (hne hvalues.symm).elim |
        exact (hactorne hvalues.symm).elim | exact (hsquarene hvalues.symm).elim |
        exact (hactor hvalues.symm).elim | exact (hsquare hvalues.symm).elim |
        exact (hdistinct hvalues.symm).elim
  have hsurj : Function.Surjective points :=
    (hinj.bijective_of_nat_card_le (by simpa using hcard.le)).2
  obtain ⟨index, hindex⟩ := hsurj ⟨target, htarget⟩
  have hvalues := congrArg Subtype.val hindex
  fin_cases index
  · exact (htne (by simpa [points] using hvalues.symm)).elim
  · exact ⟨1, by simpa [points] using hvalues⟩
  · exact ⟨actor, by simpa [points] using hvalues⟩
  · exact ⟨actor ^ 2, by simpa [points] using hvalues⟩

public theorem oneSevenFactor_support_transitive
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (D : Subgroup G) (hD : IsOneSevenFactor (V := V) D)
    (vector : V) (hvector : vector ∈ commutatorAction D V) (hne : vector ≠ 1)
    (target : V) (htarget : target ∈ commutatorAction D V) (htne : target ≠ 1) :
    ∃ actor ∈ D, actor • vector = target := by
  let derived := (commutator D).map D.subtype
  have hcop : Nat.Coprime (Nat.card derived) (Nat.card V) := by
    obtain ⟨exponent, hpower⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [show Nat.card derived = 3 from hD.2.1.2.1, hpower]
    exact (show Nat.Coprime 3 2 by decide).pow_right exponent
  have hcompl : IsCompl (FixedPoints.subgroup derived V) (commutatorAction D V) := by
    rw [oneSevenFactor_full_commutator_eq_derived D hD]
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := derived)
      (Group.isSolvable_of_comm fun left right =>
        (IsMulCommutative.is_comm (M := V)).comm left right) hcop inferInstance
  obtain ⟨actor, hactor⟩ := three_action_support_transitive (F := derived)
    (commutatorAction D V) hD.2.1.2.1 hD.2.2.1
    (oneSevenFactor_full_commutator_eq_derived D hD).symm.le hcompl.disjoint
    vector hvector hne target htarget htne
  exact ⟨actor, (Subgroup.map_subtype_le _) actor.property, hactor⟩

end Stellmacher.SectionOne
