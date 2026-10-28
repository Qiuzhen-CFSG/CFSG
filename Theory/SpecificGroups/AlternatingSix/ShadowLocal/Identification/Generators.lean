module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Holomorph

/-!
# Marked automorphisms in Aut(A₆)

The pentad automorphism, composed with conjugation by (01)(35), has
square equal to conjugation by (0123)(45). Together with conjugation
by (45) and (02)(45), it satisfies the holomorph relations. The pentad
calculations are checked on permutation generators and by the kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570. The pentad
construction is `GLS3.Chapter5.outerAltAut`.
-/

@[expose] public section
namespace AlternatingSix.ShadowLocal.Identification
open GLS3.Chapter5

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The inner twist used to choose an eighth root of the marked rotation. -/
def twist : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 3 5

def transpositionPerm : Equiv.Perm (Fin 6) := Equiv.swap 4 5

noncomputable def rotation : AutA6 := outerAltAut * permutationAction twist

def twistHom : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6) :=
  outerHom.comp (MulAut.conj twist).toMonoidHom

def transposition : AutA6 := permutationAction transpositionPerm

def reflection : AutA6 := permutationAction dihedralReflection.1

private theorem twistHom_sq : twistHom.comp twistHom =
    (MulAut.conj dihedralRotation.1).toMonoidHom := by
  apply MonoidHom.eq_of_eqOn_dense
    (Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide))
      (support_finRotate_of_le (by decide)) 0)
  rintro p (rfl | rfl)
  all_goals
    apply Equiv.ext
    intro i
    fin_cases i <;> decide +kernel

theorem rotation_sq : rotation ^ 2 = permutationAction dihedralRotation.1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  exact DFunLike.congr_fun twistHom_sq g.1

private theorem rotation_conjugates (p : Equiv.Perm (Fin 6)) :
    rotation * permutationAction p * rotation⁻¹ = permutationAction (twistHom p) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change outerHom (twist * (p * g.1 * p⁻¹) * twist⁻¹) =
    twistHom p * outerHom (twist * g.1 * twist⁻¹) * (twistHom p)⁻¹
  simp only [twistHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]
  group

private theorem rotation_transposition_permutation :
    twistHom transpositionPerm = transpositionPerm * dihedralRotation.1 ^ 2 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

private theorem rotation_reflection_permutation :
    twistHom dihedralReflection.1 = dihedralReflection.1 * (dihedralRotation.1)⁻¹ := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

theorem transposition_sq : transposition ^ 2 = 1 := by
  rw [transposition, ← map_pow]
  have h : transpositionPerm ^ 2 = 1 := by decide +kernel
  rw [h, map_one]

theorem reflection_sq : reflection ^ 2 = 1 := by
  rw [reflection, ← map_pow]
  have h : dihedralReflection.1 ^ 2 = 1 := by decide +kernel
  rw [h, map_one]

theorem transposition_reflection : Commute transposition reflection := by
  change permutationAction transpositionPerm * permutationAction dihedralReflection.1 =
    permutationAction dihedralReflection.1 * permutationAction transpositionPerm
  rw [← map_mul, ← map_mul]
  congr 1
  decide +kernel

theorem transposition_rotation : transposition * rotation * transposition⁻¹ = rotation ^ 5 := by
  have h : rotation * transposition * rotation⁻¹ = transposition * rotation ^ 4 := by
    rw [transposition, rotation_conjugates, rotation_transposition_permutation,
      map_mul, map_pow, ← rotation_sq, ← pow_mul]
  have hi : transposition⁻¹ = transposition :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using transposition_sq)
  calc
    transposition * rotation * transposition⁻¹ =
        transposition * (rotation * transposition * rotation⁻¹) * rotation := by rw [hi]; group
    _ = transposition * (transposition * rotation ^ 4) * rotation := by rw [h]
    _ = rotation ^ 5 := by
      rw [← mul_assoc transposition transposition, ← pow_two, transposition_sq, one_mul,
        ← pow_succ]

theorem reflection_rotation : reflection * rotation * reflection⁻¹ = rotation⁻¹ := by
  have h : rotation * reflection * rotation⁻¹ = reflection * (rotation ^ 2)⁻¹ := by
    rw [reflection, rotation_conjugates, rotation_reflection_permutation,
      map_mul, map_inv, ← rotation_sq]
  have hi : reflection⁻¹ = reflection :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using reflection_sq)
  calc
    reflection * rotation * reflection⁻¹ =
        reflection * (rotation * reflection * rotation⁻¹) * rotation := by rw [hi]; group
    _ = reflection * (reflection * (rotation ^ 2)⁻¹) * rotation := by rw [h]
    _ = rotation⁻¹ := by
      rw [← mul_assoc reflection reflection, ← pow_two, reflection_sq, one_mul]
      group

theorem rotation_order : orderOf rotation = 8 := by
  have h8 : rotation ^ 8 = 1 := by
    rw [show 8 = 2 * 4 from rfl, pow_mul, rotation_sq, ← map_pow]
    have h : dihedralRotation.1 ^ 4 = 1 := by decide +kernel
    rw [h, map_one]
  have h4 : rotation ^ 4 ≠ 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, rotation_sq, ← map_pow]
    intro h
    have hh : dihedralRotation.1 ^ 2 = 1 := permutationAction_injective (h.trans (map_one _).symm)
    have hn : dihedralRotation.1 ^ 2 ≠ 1 := by decide +kernel
    exact hn hh
  have hd : orderOf rotation ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hn : ¬ orderOf rotation ∣ 4 := fun h => h4 (orderOf_dvd_iff_pow_eq_one.mp h)
  rw [he] at hn ⊢
  interval_cases k <;> norm_num at hn
  norm_num

theorem rotation_not_mem_natural : rotation ∉ natural := by
  intro h
  have ht : permutationAction twist ∈ natural := ⟨twist, rfl⟩
  have he : outerAltAut = rotation * (permutationAction twist)⁻¹ := by
    dsimp [rotation]
    group
  have hout : outerAltAut ∈ natural := he ▸ natural.mul_mem h (natural.inv_mem ht)
  obtain ⟨p, hp⟩ := hout
  have htype := congrArg (fun a : AutA6 => (a baseThreeCycle).1.cycleType) hp
  change (p * threeCyclePerm * p⁻¹).cycleType = _ at htype
  rw [Equiv.Perm.cycleType_conj] at htype
  change baseThreeCycle.1.cycleType = (outerAltAut baseThreeCycle).1.cycleType at htype
  rw [baseThreeCycle_isThreeCycle, outerAltAut_base_cycleType] at htype
  have hh := congrArg Multiset.card htype
  norm_num at hh

end AlternatingSix.ShadowLocal.Identification
