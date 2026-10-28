module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.ElementaryAbelian.Basic

/-!
# Odd-order norm displacement

For an odd finite actor on a finite elementary abelian two-group, the
relative norm separates fixed points from commutator displacements. In the
fixed-point-free case, the displacement homomorphism is surjective.
-/

open scoped IsMulCommutative

namespace OddNormDisplacement

variable (A V : Type*) [Group A] [Finite A] [Group V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]

@[expose] public noncomputable def norm : V →* V := by
  classical
  letI := Fintype.ofFinite A
  exact
    { toFun := fun v => ∏ a : A, a • v
      map_one' := by simp
      map_mul' := by
        intro v w
        simp only [smul_mul']
        exact Finset.prod_mul_distrib }

public theorem norm_mem_fixed (v : V) : norm A V v ∈ FixedPoints.subgroup A V := by
  classical
  let _ := Fintype.ofFinite A
  intro a
  change a • (∏ b : A, b • v) = ∏ b : A, b • v
  rw [Finset.smul_prod']
  simp only [smul_smul]
  exact Fintype.prod_bijective (fun b : A => a * b)
    (Group.mulLeft_bijective a) _ _ (fun _ => rfl)

public theorem norm_eq_one (hfixed : FixedPoints.subgroup A V = ⊥) (v : V) :
    norm A V v = 1 := by
  simpa only [hfixed, Subgroup.mem_bot] using norm_mem_fixed A V v

@[expose] public noncomputable def displacement : V →* V := by
  classical
  letI := Fintype.ofFinite A
  exact
    { toFun := fun v => ∏ a : A, v⁻¹ * (a • v)
      map_one' := by simp
      map_mul' := by
        intro v w
        simp only [mul_inv_rev, smul_mul']
        calc
          (∏ a : A, w⁻¹ * v⁻¹ * (a • v * a • w)) =
              ∏ a : A, (v⁻¹ * (a • v)) * (w⁻¹ * (a • w)) := by
                apply Finset.prod_congr rfl
                intro a _
                ac_rfl
          _ = _ := Finset.prod_mul_distrib }

public theorem displacement_mem_commutatorAction (v : V) :
    displacement A V v ∈ commutatorAction A V := by
  classical
  let _ := Fintype.ofFinite A
  change (∏ a : A, v⁻¹ * (a • v)) ∈ commutatorAction A V
  apply Subgroup.prod_mem
  intro a _
  rw [commutatorAction_eq_closure]
  exact Subgroup.subset_closure ⟨a, v, rfl⟩

public theorem displacement_eq_self (hodd : Odd (Nat.card A))
    (hfixed : FixedPoints.subgroup A V = ⊥) (v : V) :
    displacement A V v = v := by
  classical
  let _ := Fintype.ofFinite A
  have hnorm : norm A V v = 1 := norm_eq_one A V hfixed v
  have hsquare : v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hpow : v ^ Nat.card A = v := by
    obtain ⟨n, hn⟩ := hodd
    rw [hn, pow_add, pow_mul, hsquare, one_pow, pow_one, one_mul]
  have hinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using hsquare)
  change (∏ a : A, v⁻¹ * (a • v)) = v
  rw [Finset.prod_mul_distrib]
  change (∏ _a : A, v⁻¹) * norm A V v = v
  rw [hnorm, mul_one, hinv]
  simpa only [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card] using hpow

public theorem displacement_surjective (hodd : Odd (Nat.card A))
    (hfixed : FixedPoints.subgroup A V = ⊥) :
    Function.Surjective (displacement A V) :=
  fun v => ⟨v, displacement_eq_self A V hodd hfixed v⟩

public theorem commutatorAction_eq_top (hodd : Odd (Nat.card A))
    (hfixed : FixedPoints.subgroup A V = ⊥) : commutatorAction A V = ⊤ := by
  apply top_unique
  intro v _
  rw [← displacement_eq_self A V hodd hfixed v]
  exact displacement_mem_commutatorAction A V v

public theorem commutator_subtype_surjective (hodd : Odd (Nat.card A))
    (hfixed : FixedPoints.subgroup A V = ⊥) :
    Function.Surjective (commutatorAction A V).subtype :=
  fun v => ⟨⟨displacement A V v, displacement_mem_commutatorAction A V v⟩,
    displacement_eq_self A V hodd hfixed v⟩

end OddNormDisplacement
