module

public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.FieldAction

/-!
# A Suzuki field automorphism is detected on its split torus

A field automorphism preserves the concrete split torus. If all its
displacements there have two-power order, the odd order of the torus makes
every displacement trivial. The (1,1) matrix entry then recovers every
nonzero field parameter, proving that the field automorphism is identity.

This includes the order-three field action used in Aschbacher–Smith,
13.6.6, printed p.927. It requires no simplicity or automorphism-coverage
theorem, and uses the literal entrywise field action.
-/

@[expose] public section
noncomputable section
namespace BenderSuzuki.MatrixGroups
open Subgroup BenderSuzuki.PFAppendixIII

def splitTorusElement (m : ℕ) (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiTorusGL m u, subset_closure (Or.inr (Or.inl ⟨u, rfl⟩))⟩

theorem splitTorusElement_mem (m : ℕ) (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    splitTorusElement m u ∈ SuzukiSplitTorus m :=
  (mem_suzukiSplitTorus_iff m _).mpr ⟨u, rfl⟩

theorem field_splitTorusElement (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    suzukiFieldAut m σ (splitTorusElement m u) =
      splitTorusElement m (Units.map σ.toRingHom u) := by
  ext i j
  rw [suzukiFieldAut_apply_entry]
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusElement, SuzukiTorusGL, SuzukiTorusMatrix]

theorem splitTorus_card_odd (m : ℕ) (hm : 0 < m) :
    Odd (Nat.card (SuzukiSplitTorus m)) := by
  rw [suzukiSplitTorus_card m hm]
  exact Nat.Even.sub_odd (pow_pos (by decide : 0 < (2 : ℕ)) (2 * m + 1))
    (even_two.pow_of_ne_zero (by omega)) odd_one

/-- Two-power displacements on the standard torus force the actual field
automorphism to be trivial. -/
theorem field_eq_one_of_torus_two_power (m : ℕ) (hm : 0 < m)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (h : ∀ u : (BinaryGaloisField (2 * m + 1))ˣ, ∃ n : ℕ,
      (suzukiFieldAut m σ (splitTorusElement m u) * (splitTorusElement m u)⁻¹) ^
        (2 ^ n) = 1) : σ = 1 := by
  have hfix (u : (BinaryGaloisField (2 * m + 1))ˣ) :
      suzukiFieldAut m σ (splitTorusElement m u) = splitTorusElement m u := by
    let t := splitTorusElement m u
    have ht : suzukiFieldAut m σ t ∈ SuzukiSplitTorus m := by
      rw [show t = splitTorusElement m u from rfl, field_splitTorusElement]
      exact splitTorusElement_mem _ _
    let z : SuzukiSplitTorus m :=
      ⟨suzukiFieldAut m σ t * t⁻¹, mul_mem ht (inv_mem (splitTorusElement_mem m u))⟩
    obtain ⟨n, hn⟩ := h u
    have hz : z ^ (2 ^ n) = 1 := Subtype.ext hn
    have hc : Nat.Coprime (2 ^ n) (Nat.card (SuzukiSplitTorus m)) :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr (splitTorus_card_odd m hm).not_two_dvd_nat).pow_left n
    have he : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc
      (orderOf_dvd_of_pow_eq_one hz) (orderOf_dvd_natCard z))
    exact mul_inv_eq_one.mp (congrArg Subtype.val he)
  ext x
  change σ x = x
  by_cases hx : x = 0
  · simp [hx]
  · have he := congrArg (fun g : SuzukiMatrixGroup m => g.val (1 : Fin 4) (1 : Fin 4))
      (hfix (Units.mk0 x hx))
    rw [suzukiFieldAut_apply_entry] at he
    have hp : σ x ^ (2 ^ m) = x ^ (2 ^ m) := by
      simpa [splitTorusElement, SuzukiTorusGL, SuzukiTorusMatrix] using he
    exact (iterateFrobenius_inj _ 2 m) (by simpa only [iterateFrobenius_def] using hp)

end BenderSuzuki.MatrixGroups
