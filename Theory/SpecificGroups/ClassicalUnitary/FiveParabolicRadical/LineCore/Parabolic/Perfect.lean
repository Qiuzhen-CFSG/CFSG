module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Split
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfectness of the unitary line radical and SU₃ Levi

Over the field of order sixteen with fourth-power conjugation, an element ζ of
order five gives the special-unitary matrix `diag(ζ, ζ, ζ³)`. Its three diagonal
entries have norm one, their product is one, and none equals one. Thus its
displacement on the middle three-space is surjective, by coordinate division.

A mixed Levi–radical commutator realizes every vector coordinate. The remaining
central correction is a radical commutator, using a trace-one scalar. Hence the
whole radical lies in the semidirect product's derived subgroup. If the actual
SU₃ Levi is perfect, its image lies there too and the semidirect product is
perfect. No full-parabolic decomposition is needed for this calculation.

Source: the classical unitary calculation used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
open scoped commutatorElement
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- A surjective displacement puts all radical coordinates in the derived group. -/
theorem inl_mem_commutator_of_displacement (c : F) (hc : c + J.conj c = 1)
    (A : (middleForm J).specialSubgroup)
    (hA : Function.Surjective (fun v : Fin 3 → F => A.val.val *ᵥ v + v))
    (x : Coord J) :
    SemidirectProduct.inl x ∈ commutator (RadicalLevi J) := by
  obtain ⟨v, hv⟩ := hA x.vector
  let u : Coord J := Coord.liftVector c hc v
  let k : Coord J := leviAction J A u * u⁻¹
  have hk : k.vector = x.vector := hv
  have hkcomm : SemidirectProduct.inl k ∈ commutator (RadicalLevi J) := by
    have he : (SemidirectProduct.inl k : RadicalLevi J) =
        ⁅(SemidirectProduct.inr A : RadicalLevi J), SemidirectProduct.inl u⁆ := by
      simp only [k, map_mul, SemidirectProduct.inl_aut, map_inv, commutatorElement_def]
    rw [he]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hz : (x * k⁻¹).vector = 0 := by
    ext i
    simp [hk, CharTwo.add_self_eq_zero]
  obtain ⟨a, b, hab⟩ := Coord.exists_commutator_of_vector_eq_zero c hc (x * k⁻¹) hz
  have hzcomm : SemidirectProduct.inl (x * k⁻¹) ∈ commutator (RadicalLevi J) := by
    rw [← hab, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have := (commutator (RadicalLevi J)).mul_mem hzcomm hkcomm
  simpa only [← map_mul, inv_mul_cancel_right] using this

/-- Once the radical lies in the derived group, a perfect Levi completes it. -/
theorem radicalLevi_isPerfect_of_displacement (c : F) (hc : c + J.conj c = 1)
    (A : (middleForm J).specialSubgroup)
    (hA : Function.Surjective (fun v : Fin 3 → F => A.val.val *ᵥ v + v))
    [Group.IsPerfect (middleForm J).specialSubgroup] : Group.IsPerfect (RadicalLevi J) := by
  constructor
  apply top_unique
  intro x _
  have hmap : (commutator (middleForm J).specialSubgroup).map
      (SemidirectProduct.inr : (middleForm J).specialSubgroup →* RadicalLevi J) ≤
      commutator (RadicalLevi J) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hr : SemidirectProduct.inr x.right ∈ commutator (RadicalLevi J) :=
    hmap ⟨x.right, Group.IsPerfect.mem_commutator, rfl⟩
  simpa only [SemidirectProduct.inl_left_mul_inr_right] using
    (commutator (RadicalLevi J)).mul_mem
      (inl_mem_commutator_of_displacement J c hc A hA x.left) hr

/-- Over sixteen elements the SU₃ Levi contains a diagonal with surjective displacement. -/
theorem exists_middle_surjective_displacement_of_card_sixteen [Finite F]
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) :
    ∃ A : (middleForm J).specialSubgroup,
      Function.Surjective (fun v : Fin 3 → F => A.val.val *ᵥ v + v) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 5 (by
    rw [Nat.card_units, hcard]; decide)
  have hu5 : u ^ 5 = 1 := hu ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    simp [h] at hu
  have hu3 : u ^ 3 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hu] at hd
    norm_num at hd
  let a : F := u.val
  have ha5 : a ^ 5 = 1 := congrArg Units.val hu5
  have ha1 : a ≠ 1 := fun h => hu1 (Units.ext h)
  have ha3 : a ^ 3 ≠ 1 := fun h => hu3 (Units.ext h)
  have hnorm : J.conj a * a = 1 := by rw [hconj, ← pow_succ, ha5]
  let d : Fin 3 → F := ![a, a, a ^ 3]
  have hdNorm (i : Fin 3) : J.conj (d i) * d i = 1 := by
    fin_cases i
    · exact hnorm
    · exact hnorm
    · change J.conj (a ^ 3) * a ^ 3 = 1
      rw [map_pow, ← mul_pow, hnorm, one_pow]
  have hdNe (i : Fin 3) : d i ≠ 1 := by
    fin_cases i
    · exact ha1
    · exact ha1
    · exact ha3
  have hdet : (diagonal d).det = 1 := by
    rw [det_diagonal]
    simpa [d, Fin.prod_univ_succ, pow_succ, mul_assoc] using ha5
  let D : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero (diagonal d)
    (by rw [hdet]; exact one_ne_zero)
  have hD : D ∈ (middleForm J).specialSubgroup := by
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change (middleForm J).conjTranspose (diagonal d) * 1 * diagonal d = 1
      rw [mul_one]
      ext i j
      by_cases h : j = i <;>
        simp [HermitianForm.conjTranspose, middleForm, Matrix.mul_apply,
          Matrix.diagonal_apply, Matrix.one_apply, h, Ne.symm, hdNorm]
    · apply Units.ext
      exact hdet
  refine ⟨⟨D, hD⟩, ?_⟩
  intro v
  refine ⟨fun i => v i / (d i + 1), ?_⟩
  change diagonal d *ᵥ _ + _ = v
  ext i
  rw [Pi.add_apply, mulVec_diagonal]
  have hn : d i + 1 ≠ 0 := by
    intro h
    apply hdNe i
    exact add_right_cancel (h.trans (CharTwo.add_self_eq_zero (1 : F)).symm)
  change d i * (v i / (d i + 1)) + v i / (d i + 1) = v i
  field_simp

/-- Perfectness of the actual radical–SU₃ product over the field of order sixteen. -/
theorem radicalLevi_isPerfect_of_card_sixteen [Finite F]
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (c : F) (hc : c + J.conj c = 1)
    [Group.IsPerfect (middleForm J).specialSubgroup] : Group.IsPerfect (RadicalLevi J) := by
  obtain ⟨A, hA⟩ := exists_middle_surjective_displacement_of_card_sixteen J hcard hconj
  exact radicalLevi_isPerfect_of_displacement J c hc A hA

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
