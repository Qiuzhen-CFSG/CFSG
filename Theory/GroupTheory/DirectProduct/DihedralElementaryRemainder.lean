module
public import Theory.GroupTheory.DirectProduct.SymmetricFourRemainder
public import Theory.ElementaryAbelian.Basic

/-!
# The elementary remainder after maximal dihedral splitting

Squares of central elements of D8 times B generate a characteristic
subgroup contained in B. The characteristic obstruction kills it, so
Z(B) has exponent two. The abelian factor in the maximal dihedral splitting
lies in Z(B), and is therefore elementary. The final theorem discharges the
obstruction using the original Sylow subgroup of the actual S4 times B model.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), last step
of (2.14), printed p.385.
-/

public section
open Subgroup
namespace Theory.GroupTheory.DihedralFactorExtraction
variable {B : Type*} [Group B]

private theorem center_dihedral_square : ∀ z : DihedralGroup 4,
    (∀ d : DihedralGroup 4, d * z = z * d) → z ^ 2 = 1 := by
  decide +kernel

private theorem center_square_of_characteristic_remainder_trivial
    (hchar : ∀ K : Subgroup (DihedralGroup 4 × B), K.Characteristic →
      K ≤ (⊥ : Subgroup (DihedralGroup 4)).prod ⊤ → K = ⊥)
    (b : B) (hb : b ∈ center B) : b ^ 2 = 1 := by
  let D := DihedralGroup 4 × B
  let K : Subgroup D := closure {z | ∃ x ∈ center D, x ^ 2 = z}
  have hK : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro e
    apply (closure_le _).mpr
    rintro z ⟨x, hx, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨e x, ?_, (map_pow e x 2).symm⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx w)
  have hKB : K ≤ (⊥ : Subgroup (DihedralGroup 4)).prod ⊤ := by
    apply (closure_le _).mpr
    rintro z ⟨x, hx, rfl⟩
    refine ⟨?_, mem_top _⟩
    change x.1 ^ 2 = 1
    apply center_dihedral_square
    intro d
    exact congrArg Prod.fst (mem_center_iff.mp hx (d, 1))
  have hk := hchar K hK hKB
  have hbD : ((1, b) : D) ∈ center D := by
    rw [mem_center_iff]
    intro x
    apply Prod.ext
    · simp
    · exact mem_center_iff.mp hb x.2
  have hz : ((1, b) : D) ^ 2 ∈ K := Subgroup.subset_closure ⟨(1, b), hbD, rfl⟩
  exact congrArg Prod.snd (show ((1, b) : D) ^ 2 = 1 from hk.le hz)

theorem exists_elementary_remainder (B : Type*) [Group B] [Finite B]
    (hchar : ∀ K : Subgroup (DihedralGroup 4 × B), K.Characteristic →
      K ≤ (⊥ : Subgroup (DihedralGroup 4)).prod ⊤ → K = ⊥) :
    ∃ n : ℕ, ∃ A : Subgroup B,
      Nonempty (B ≃* (Fin n → DihedralGroup 4) × A) ∧ IsElementaryAbelian 2 A := by
  obtain ⟨n, A, ⟨e⟩, hA⟩ := exists_abelian_remainder B hchar
  let := hA
  refine ⟨n, A, ⟨e⟩, { exponent_dvd_p := ?_ }⟩
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro a
  have hc : e.symm (1, a) ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    apply Prod.ext
    · simp
    · exact IsMulCommutative.is_comm.comm _ _
  have hs := center_square_of_characteristic_remainder_trivial hchar _ hc
  have hh := congrArg (fun b => (e b).2) hs
  simpa only [map_pow, map_one, e.apply_symm_apply, Prod.pow_snd, Prod.snd_one] using hh

theorem symmetricFour_exists_elementary_remainder (B : Type*) [Group B] [Finite B]
    (hB : IsPGroup 2 B) (P : Sylow 2 (Equiv.Perm (Fin 4) × B))
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup (Equiv.Perm (Fin 4) × B)).subtype).Normal) :
    ∃ n : ℕ, ∃ A : Subgroup B,
      Nonempty (B ≃* (Fin n → DihedralGroup 4) × A) ∧ IsElementaryAbelian 2 A :=
  exists_elementary_remainder B (symmetricFour_characteristic_remainder_eq_bot B hB P hP)

end Theory.GroupTheory.DihedralFactorExtraction

