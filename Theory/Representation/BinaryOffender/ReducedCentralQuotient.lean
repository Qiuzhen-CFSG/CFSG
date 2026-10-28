module
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Faithfulness of a fully moved central quotient

In a faithful binary action with trivial two-core, a normal subgroup K acts
faithfully on V/C_V(K): the kernel lies in O₂(K), which is trivial. If V=[V,K],
faithfulness on K then forces faithfulness of the full acting group on this
central quotient. The equivariant-map version retains any specified quotient
coordinates and does not change the acting group.

Source application: Aschbacher–Smith D.3.4 and D.3.9, the faithful action on
the original full module modulo its normal-layer fixed space.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Reducedness and full movement preserve faithfulness on the central quotient. -/
theorem fixedQuotient_faithful_of_trivial_core (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hc : pCore 2 G = ⊥) (K : Subgroup G) [K.Normal]
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤) :
    Function.Injective (fixedQuotient ρ K) := by
  apply fixedQuotient_faithful ρ K hf _ hwhole
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro k hk
  have hh : k ∈ (fixedQuotientRepresentation ρ K).ker :=
    (mem_fixedQuotient_ker_iff ρ K k).mpr ((quotient_kernel_iff ρ K k).mp hk)
  have hcore := fixedQuotient_ker_le_pCore ρ hf K hh
  rw [pCore_eq_comap_of_normal,hc] at hcore
  exact Subtype.ext hcore

/-- Faithfulness in specified central-quotient coordinates. -/
theorem faithful_of_equivariant_reduced_central_quotient
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (hf : Function.Injective ρ) (hc : pCore 2 G = ⊥) (K : Subgroup G) [K.Normal]
    (f : V →ₗ[ZMod 2] W) (hk : f.ker = fixedSpace ρ K)
    (he : ∀ g v, f (ρ g v) = σ g (f v))
    (hwhole : subspaceCommutator ρ ⊤ K = ⊤) : Function.Injective σ := by
  have hfaith := fixedQuotient_faithful_of_trivial_core ρ hf hc K hwhole
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  change g = 1
  apply hfaith
  rw [map_one]
  apply (quotient_kernel_iff ρ K g).mpr
  intro v
  rw [←hk,LinearMap.mem_ker,map_sub,he,show σ g = 1 from hg,Module.End.one_apply,sub_self]
end Representation.BinaryOffender
