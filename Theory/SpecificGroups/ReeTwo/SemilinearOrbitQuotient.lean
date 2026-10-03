module

public import Theory.SpecificGroups.ReeTwo.SemilinearExtensionData
public import Theory.SpecificGroups.ReeTwo.OrbitFrameAlgebra
public import Theory.SpecificGroups.ReeTwo.SemilinearOrbitCommutators
public import Theory.SpecificGroups.ReeTwo.SemilinearOrbitTailCoordinates

/-!
# Quotient coordinates of the semilinear orbit words

The intrinsic data make the central quotient class two with elementary
commutators. The seed and the prescribed root become involutions there.
Consequently the six orbit-commutator identities suffice for all frame
coordinates, including the trivial quotient pairing.

The root displacements provide faithful binary coordinates on the derived
subgroup modulo the center. The normalized symmetry then determines the six
orbit commutators, completing the intrinsic quotient calculation.
Source: Thompson VI,
pp.629–630; Parrott (1972), pp.672–674; Shinoda (1975), pp.81–82.
-/

@[expose] public section
namespace ReeTwo
open Subgroup
variable {K A : Type*} [Group K] [Group A]
/-- The intrinsic data supply all structural quotient laws. Only the six
orbit commutators remain as an explicit premise in this assembly lemma. -/
theorem SemilinearExtensionData.orbitFrame_quotient_of_commutators
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ) (g : A)
    (htable : OrbitCommutatorCoordinates
      (fun i : Fin 4 => QuotientGroup.mk' (center K) (ρ (g ^ i.val) b))
      (QuotientGroup.mk' (center K) t)) :
    FrameCoordinates ((QuotientGroup.mk' (center K)) ∘ orbitFrame ρ b g t)
      (QuotientGroup.mk' (center K) t) (QuotientGroup.mk' (center K) z) := by
  let q := QuotientGroup.mk' (center K)
  let D := (commutator R).map R.subtype
  let _ : IsElementaryAbelian 2 D := h.derived_elementary
  obtain ⟨hc, he⟩ := centralQuotient_rightComm_laws D h.derived_eq.ge
    (by rw [h.derived_commutator, h.center_eq])
  have hqz : q z = 1 := (QuotientGroup.eq_one_iff z).mpr
    (h.center_eq.symm ▸ h.central_mem)
  have ht : q t * q t = 1 := by rw [← map_mul, ← pow_two, h.root_square, hqz]
  have hb : (b : K) ^ 2 = 1 := congrArg Subtype.val h.seed_square
  have hu (i : Fin 4) : q (ρ (g ^ i.val) b) * q (ρ (g ^ i.val) b) = 1 := by
    rw [← pow_two, ← map_pow, ← map_pow, hb, map_one, map_one]
  have hf := frameCoordinates_of_orbitCommutators hc he
    (fun i : Fin 4 => q (ρ (g ^ i.val) b)) (q t) hu ht htable
  change FrameCoordinates (q ∘ orbitFrame ρ b g t) (q t) (q z)
  rw [hqz]
  convert hf using 1
  funext i
  fin_cases i <;> simp [orbitFrame, Function.comp_apply, q]

/-- The explicit semilinear orbit words have the prescribed frame coordinates
modulo the center, intrinsically from the extension data. -/
theorem SemilinearExtensionData.orbitFrame_quotient [Finite K] [Finite A]
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ) (g : A) (hg : g ≠ 1) :
    FrameCoordinates ((QuotientGroup.mk' (center K)) ∘ orbitFrame ρ b g t)
      (QuotientGroup.mk' (center K) t) (QuotientGroup.mk' (center K) z) := by
  obtain ⟨hrel, hinj, hspan⟩ := h.orbitTailCoordinates g hg
  exact h.orbitFrame_quotient_of_commutators g
    (h.orbitCommutatorCoordinates_of_tailCoordinates g hg hrel hinj hspan)
end ReeTwo
