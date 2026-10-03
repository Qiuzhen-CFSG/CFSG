module

public import Theory.GroupAction.FiveFourLargeFixedKernel
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# A large fixed layer detects a five-four quotient kernel

Let P act on U/Z by conjugation, with a faithful five-four quotient action
on elementary sixteen. If Z has order at most two, an involution fixing
a subgroup of U of order at least sixteen modulo Z belongs to the kernel
of the five-four quotient map. The commutator containment gives fixed
vectors in the literal quotient, so the large-fixed-subgroup criterion
applies without any assertion about fusion.

Source: Thompson VI, printed p.630, the fixed bound on the conjugate
derived quotient preceding transport into the outer core cosets.
-/

namespace Theory.GroupAction
open Subgroup
open scoped commutatorElement

/-- A subgroup of order at least sixteen with central displacement forces
an involution into the kernel of a faithful five-four quotient action. -/
public theorem mem_ker_of_five_four_quotient_commutator_layer
    {G : Type*} [Group G] [Finite G]
    (P U Z : Subgroup G) (hZU : Z ≤ U) [(Z.subgroupOf U).Normal]
    [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)]
    (hU : Nat.card (U ⧸ Z.subgroupOf U) = 16) (hZ : Nat.card Z ≤ 2)
    (hPU : P ≤ normalizer (U : Set G))
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (π : P →* SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut (U ⧸ Z.subgroupOf U)) (hf : Function.Injective f)
    (hformula : ∀ p : P, ∀ u : U,
      f (π p) (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(p : G) * (u : G) * (p : G)⁻¹,
            (mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩)
    (y : P) (hy : y ^ 2 = 1)
    (E : Subgroup G) (hEU : E ≤ U) (hE : 16 ≤ Nat.card E)
    (hcomm : ⁅E, zpowers (y : G)⁆ ≤ Z) :
    y ∈ π.ker := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  have hq : Nat.card q.ker ≤ 2 := by
    rw [QuotientGroup.ker_mk', Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv]
    exact hZ
  have hE' : 16 ≤ Nat.card (E.subgroupOf U) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv]
    exact hE
  apply mem_ker_of_five_four_fixed_layer hU φ hφ π f hf q hq
    (E.subgroupOf U) hE' y hy
  intro a
  change f (π y) (QuotientGroup.mk' (Z.subgroupOf U) (a : U)) =
    QuotientGroup.mk' (Z.subgroupOf U) (a : U)
  rw [hformula]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (y : G) * ((a : U) : G) * (y : G)⁻¹ / ((a : U) : G) ∈ Z
  have hc : ⁅(y : G), ((a : U) : G)⁆ ∈ Z := by
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator (mem_zpowers (y : G)) a.property)
  simpa only [commutatorElement_def, div_eq_mul_inv] using hc

/-- The same test applies to a supplied conjugation action whose kernel is
the kernel of a surjective five-four quotient map. -/
public theorem mem_ker_of_five_four_quotient_action_layer
    {G : Type*} [Group G] [Finite G]
    (P U Z : Subgroup G) (hZU : Z ≤ U) [(Z.subgroupOf U).Normal]
    [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)]
    (hU : Nat.card (U ⧸ Z.subgroupOf U) = 16) (hZ : Nat.card Z ≤ 2)
    (hPU : P ≤ normalizer (U : Set G))
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (π : P →* SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (hπ : Function.Surjective π)
    (action : P →* MulAut (U ⧸ Z.subgroupOf U))
    (hkernel : π.ker = action.ker)
    (hformula : ∀ p : P, ∀ u : U,
      action p (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(p : G) * (u : G) * (p : G)⁻¹,
            (mem_normalizer_iff.mp (hPU p.property) u).mp u.property⟩)
    (y : P) (hy : y ^ 2 = 1)
    (E : Subgroup G) (hEU : E ≤ U) (hE : 16 ≤ Nat.card E)
    (hcomm : ⁅E, zpowers (y : G)⁆ ≤ Z) :
    y ∈ π.ker := by
  classical
  let f := π.liftOfSurjective hπ ⟨action, hkernel.le⟩
  have hfactor (p : P) : f (π p) = action p :=
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨action, hkernel.le⟩ p
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro b hb
    obtain ⟨p, rfl⟩ := hπ b
    have hp : p ∈ action.ker := by
      change action p = 1
      exact (hfactor p).symm.trans hb
    rw [← hkernel] at hp
    exact hp
  apply mem_ker_of_five_four_quotient_commutator_layer P U Z hZU hU hZ hPU
    φ hφ π f hf (fun p u => ?_) y hy E hEU hE hcomm
  rw [hfactor]
  exact hformula p u

end Theory.GroupAction
