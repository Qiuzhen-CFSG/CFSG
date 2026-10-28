module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.Commutant
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.RelativeCocycles

/-!
# Quotient fixers and pointwise kernel fixation in the actual max1 subgroup

An automorphism inducing the identity on the actual quotient preserves the
kernel. Its restriction is an automorphism by injectivity and finiteness.
Since conjugation factors through the quotient, this restriction commutes
with both generator actions. The scalar commutant theorem forces it to be
the identity. Thus the relative cocycle theorem also applies directly to
quotient fixers, with no extra pointwise-fixation premise.

All groups and elements are the canonical literal ATLAS max1 carriers from
`Core`. Conjugation in the commutant argument is left conjugation; the
relative displacement remains `h⁻¹ * phi h`.

Source: literal ATLAS `J4G1-max1W1`, documented in `Cardinality.Subgroup`;
local structure motivation: GLS3, Table 5.3i.
-/

public section
namespace Janko4.Max1RelativeRigidity
open Cardinality
attribute [local irreducible] KernelCount.basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

/-- Identity on the actual quotient forces pointwise fixation of its kernel. -/
theorem fixes_kernel_of_quotient_fixed (phi : MulAut M)
    (hquot : ∀ g : M, QuotientGroup.mk' K (phi g) = QuotientGroup.mk' K g) :
    ∀ e : K, phi (e : M) = (e : M) := by
  have hmem (g : M) (hg : g ∈ K) : phi g ∈ K := by
    apply (QuotientGroup.eq_one_iff (phi g)).mp
    exact (hquot g).trans ((QuotientGroup.eq_one_iff g).mpr hg)
  let f : K →* K := {
    toFun := fun e => ⟨phi e, hmem e e.property⟩
    map_one' := Subtype.ext (map_one phi)
    map_mul' := fun a b => Subtype.ext (map_mul phi (a : M) (b : M)) }
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (phi.injective (congrArg Subtype.val h))
  let kappa : MulAut K := MulEquiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hact (g : M) :
      QuotientCount.action matrixA_mul_self matrixB_pow_four (phi g) =
        QuotientCount.action matrixA_mul_self matrixB_pow_four g := by
    have hd : phi g * g⁻¹ ∈ K := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' K (phi g * g⁻¹) = 1
      rw [map_mul, map_inv, hquot, mul_inv_cancel]
    change phi g * g⁻¹ ∈ localKernel matrixA_mul_self matrixB_pow_four at hd
    rw [← LocalStructure.action_ker_eq_localKernel matrixA_mul_self matrixB_pow_four] at hd
    change QuotientCount.action matrixA_mul_self matrixB_pow_four (phi g * g⁻¹) = 1 at hd
    simpa only [map_mul, map_inv, mul_inv_eq_one] using hd
  have hc (g : M) : Commute kappa (MulAut.conjNormal g : MulAut K) := by
    apply MulEquiv.ext
    intro e
    apply Subtype.ext
    change phi (g * (e : M) * g⁻¹) = g * phi e * g⁻¹
    rw [map_mul, map_mul, map_inv]
    exact congrArg (fun a : Equiv.Perm K => (a (kappa e) : M)) (hact g)
  have hk := commutant_automorphism kappa (hc x) (hc y)
  intro e
  exact congrArg (fun a : MulAut K => (a e : M)) hk

/-- A quotient fixer with the relative centralizer displacement bound is
conjugation by one or the actual kernel pair. -/
theorem relative_rigidity_of_quotient_fixed (phi : MulAut M)
    (hquot : ∀ g : M, QuotientGroup.mk' K (phi g) = QuotientGroup.mk' K g)
    (hrelative : ∀ h : M, Commute h v → h⁻¹ * phi h ∈ Subgroup.zpowers v) :
    ∃ epsilon : Fin 2, phi = MulAut.conj (v ^ epsilon.val) :=
  relative_cocycle_rigidity phi (fixes_kernel_of_quotient_fixed phi hquot) hrelative

end Janko4.Max1RelativeRigidity
