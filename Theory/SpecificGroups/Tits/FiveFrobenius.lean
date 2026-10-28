module

public import Theory.SpecificGroups.Tits.FiveFrobenius.Subgroups
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# A five-local Frobenius pair in Parrott's Tits group

The ATLAS word certificates construct an abelian subgroup of order 25 and
an order-24 subgroup normalizing it and acting freely on its nonidentity
elements. Pulling both subgroups back along the certified isomorphism
`parrottFiniteImageEquiv` gives the same configuration in the actual Parrott
presentation. No order-only identification or extra hypothesis is used.

Source: ATLAS maximal-subgroup program `TF42G1-max8W1`,
https://brauer.maths.qmul.ac.uk/Atlas/v3/exc/TF42/.
The explicit words and inverse-point-map convention are documented in
`FiveFrobenius.Tables`; their collection and action proofs are in `Subgroups`.
-/

namespace Tits

/-- The certified order-25 subgroup, on Parrott's actual carrier. -/
public noncomputable def fiveKernel : Subgroup ParrottGroup :=
  FiveFrobenius.kernel.comap parrottFiniteImageEquiv.toMonoidHom

/-- The certified order-24 subgroup acting on `fiveKernel`. -/
public noncomputable def fiveComplement : Subgroup ParrottGroup :=
  FiveFrobenius.complement.comap parrottFiniteImageEquiv.toMonoidHom

public instance fiveKernel_commutative : IsMulCommutative fiveKernel :=
  FiveFrobenius.kernel.comap_injective_isMulCommutative parrottFiniteImageEquiv.injective

public theorem fiveKernel_card : Nat.card fiveKernel = 25 := by
  rw [fiveKernel, Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective parrottFiniteImageEquiv.symm.injective]
  exact FiveFrobenius.kernel_card

public theorem fiveComplement_card : Nat.card fiveComplement = 24 := by
  rw [fiveComplement, Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective parrottFiniteImageEquiv.symm.injective]
  exact FiveFrobenius.complement_card

public theorem fiveComplement_normalizes :
    fiveComplement ≤ Subgroup.normalizer (fiveKernel : Set ParrottGroup) := by
  intro c hc
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  change parrottFiniteImageEquiv.toMonoidHom x ∈ FiveFrobenius.kernel ↔
    parrottFiniteImageEquiv.toMonoidHom (c * x * c⁻¹) ∈ FiveFrobenius.kernel
  simpa only [map_mul, map_inv] using
    (Subgroup.mem_normalizer_iff.mp (FiveFrobenius.complement_normalizes hc))
      (parrottFiniteImageEquiv.toMonoidHom x)

public theorem fiveComplement_free (c : fiveComplement) (hc : c ≠ 1) (k : fiveKernel)
    (h : (c : ParrottGroup) * k * (c : ParrottGroup)⁻¹ = k) : k = 1 := by
  let c' : FiveFrobenius.complement := ⟨parrottFiniteImageEquiv c, c.property⟩
  let k' : FiveFrobenius.kernel := ⟨parrottFiniteImageEquiv k, k.property⟩
  have hc' : c' ≠ 1 := by
    intro hh
    apply hc
    apply Subtype.ext
    apply parrottFiniteImageEquiv.injective
    simpa only [c', Subgroup.coe_mk, Subgroup.coe_one, map_one] using congrArg Subtype.val hh
  have hh : (c' : Atlas1600Group) * k' * (c' : Atlas1600Group)⁻¹ = k' := by
    simpa only [map_mul, map_inv] using congrArg parrottFiniteImageEquiv h
  have hk := FiveFrobenius.complement_free c' hc' k' hh
  apply Subtype.ext
  apply parrottFiniteImageEquiv.injective
  simpa only [k', Subgroup.coe_mk, Subgroup.coe_one, map_one] using congrArg Subtype.val hk

/-- An unconditional Frobenius pair in the actual Tits group: an abelian
five-kernel of order 25 and a free normalizing subgroup of order 24. -/
public theorem exists_five_frobenius_subgroups :
    ∃ K C : Subgroup ParrottGroup,
      IsMulCommutative K ∧ Nat.card K = 25 ∧ Nat.card C = 24 ∧
      C ≤ Subgroup.normalizer (K : Set ParrottGroup) ∧
      (∀ c : C, c ≠ 1 → ∀ k : K,
        (c : ParrottGroup) * k * (c : ParrottGroup)⁻¹ = k → k = 1) :=
  ⟨fiveKernel, fiveComplement, fiveKernel_commutative, fiveKernel_card,
    fiveComplement_card, fiveComplement_normalizes, fiveComplement_free⟩

end Tits
