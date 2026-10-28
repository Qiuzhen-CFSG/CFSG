module
public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.Quotient
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner

/-!
# Even involutions lifted through a retained action kernel

Suppose a finite group maps onto S₆ and a binary representation has kernel
contained in the permutation kernel. An element projecting to an even
involution moves at least two dimensions. A conjugate partner gives an
order-five commutator in S₆; its lift in the faithful representation quotient
has an order-five power. The binary degree of five is four, and commutator
rank is at most twice the original displacement.

This argument permits a nontrivial odd permutation kernel. It generalizes
the orbit calculation in CubicOrbit.Bounds to arbitrary representations.
Source: MS93 (5.2)(i), printed p.914; the order-five displacement argument
uses the elementary prime-contribution theorem imported below.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace Representation.BinaryOffender.EvenLift
private def testInvolution : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def testPartner : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 3 4
private theorem testInvolution_order : orderOf testInvolution = 2 :=
  orderOf_eq_prime (by decide) (by decide)
private theorem testCommutator_order : orderOf ⁅testInvolution.val,testPartner⁆ = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime <;> decide +kernel

private theorem even_involution_commutator_five
    (a : Equiv.Perm (Fin 6)) (ha : a ∈ alternatingGroup (Fin 6)) (ho : orderOf a = 2) :
    ∃ b : Equiv.Perm (Fin 6), orderOf ⁅a,b⁆ = 5 := by
  let a' : alternatingGroup (Fin 6) := ⟨a,ha⟩
  have ho' : orderOf a' = 2 :=
    (orderOf_injective (alternatingGroup (Fin 6)).subtype Subtype.coe_injective a').symm.trans ho
  obtain ⟨c,hc⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj testInvolution a' testInvolution_order ho')
  let f := (MulAut.conj c.val).toMonoidHom
  have hfa : f testInvolution.val = a := congrArg Subtype.val hc
  refine ⟨f testPartner,?_⟩
  rw [←hfa,←map_commutatorElement,orderOf_injective f (MulAut.conj c.val).injective]
  exact testCommutator_order

private theorem fixedCodim_mono_local
    {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    {A B : Subgroup H} (hab : A ≤ B) : fixedCodim ρ A ≤ fixedCodim ρ B := by
  have hd := Submodule.finrank_mono (fixedSpace_antitone ρ hab)
  have ha := fixedCodim_add_finrank ρ A
  have hb := fixedCodim_add_finrank ρ B
  omega


variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- An even involution in the actual symmetric quotient costs at least two
binary dimensions when the representation kernel lies in that quotient kernel. -/
theorem fixedCodim_lower (π : H →* Equiv.Perm (Fin 6))
    (hπ : Function.Surjective π) (ρ : Representation (ZMod 2) H V)
    (hk : ρ.ker ≤ π.ker) (a : H)
    (ha : π a ∈ alternatingGroup (Fin 6)) (ho : orderOf (π a) = 2) :
    2 ≤ fixedCodim ρ (zpowers a) := by
  let q := QuotientGroup.mk' ρ.ker
  let σ := quotientOfLEKer ρ ρ.ker le_rfl
  have hσ : Function.Injective σ := by
    apply σ.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective ρ.ker x
    exact (QuotientGroup.eq_one_iff x).mpr hx
  let p := QuotientGroup.lift ρ.ker π hk
  obtain ⟨u,hu⟩ := even_involution_commutator_five (π a) ha ho
  obtain ⟨b,hb⟩ := hπ u
  let v := ⁅q a,q b⁆
  have hv : orderOf (p v) = 5 := by
    change orderOf (p ⁅q a,q b⁆) = 5
    rw [map_commutatorElement]
    change orderOf ⁅π a,π b⁆ = 5
    rwa [hb]
  have hdvd : 5 ∣ orderOf v := hv ▸ orderOf_map_dvd p v
  let y := v ^ (orderOf v / 5)
  have hy : orderOf y = 5 := orderOf_pow_orderOf_div (orderOf_pos v).ne' hdvd
  have hlo := prime_order_le_fixedCodim σ hσ
    (by decide : Nat.Prime 5) (by decide) y hy
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hlo
  have hmon := fixedCodim_mono_local σ (zpowers_le.mpr
    (show y ∈ zpowers v from pow_mem (mem_zpowers _) _))
  have hhi := fixedCodim_commutator_le_twice σ (q a) (q b)
  have he : fixedCodim σ (zpowers (q a)) = fixedCodim ρ (zpowers a) := by
    rw [←MonoidHom.map_zpowers q a]
    unfold fixedCodim
    rw [←fixedSpace_comp_map σ q (zpowers a)]
    rfl
  rw [he] at hhi
  change fixedCodim σ (zpowers v) ≤ _ at hhi
  omega

end Representation.BinaryOffender.EvenLift
