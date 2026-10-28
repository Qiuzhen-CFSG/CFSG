module

public import Theory.Representation.SchurDisplacement
public import Theory.Representation.BinaryOffender.InvolutionFixedKernel
public import Theory.PGroupCore

/-!
# Strict displacement for actors moving the Schur field

On a faithful binary module, the pointwise kernel on an involution's fixed
space is elementary abelian. Its intersection with any subgroup of the
involution centralizer is normal in that subgroup. A trivial two-core
therefore makes this restricted action faithful. A nonidentity element
from that subgroup strictly reduces the common fixed space.

Combined with Schur displacement, an actor containing both a scalar-moving
involution and such an element moves strictly more than half the module.
This supplies the common-fixed-space step in the induced case of
Guralnick--Malle, Classification of 2F-modules II, Proposition 4.1(3),
manuscript pp.20--22, without choosing scalar-extension constituents.
-/

public section
namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A subgroup with trivial two-core in the involution centralizer acts faithfully
on the involution fixed space. -/
theorem involution_fixedSpace_kernel_eq_bot
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (t : G) (ht : t ^ 2 = 1) (C : Subgroup G)
    (hC : C ≤ centralizer {t}) (hcore : pCore 2 C = ⊥) :
    subspaceKernel ρ (fixedSpace ρ (zpowers t)) C = ⊥ := by
  let W := fixedSpace ρ (zpowers t)
  let D := subspaceKernel ρ W C
  have hstab : C ≤ subspaceStabilizer ρ W := by
    apply le_subspaceStabilizer
    intro g hg v hv
    rw [mem_fixedSpace_zpowers_iff] at hv ⊢
    rw [← Module.End.mul_apply, ← map_mul,
      ← mem_centralizer_singleton_iff.mp (hC hg), map_mul, Module.End.mul_apply, hv]
  have hn : (D.subgroupOf C).Normal := subspaceKernel_normal ρ W C hstab
  let : IsElementaryAbelian 2 (involutionFixedKernel ρ t) :=
    involutionFixedKernel_elementary ρ hf t ht
  have hD : D ≤ involutionFixedKernel ρ t := fun g hg => ⟨hC hg.1, hg.2⟩
  have hp : IsPGroup 2 D :=
    (IsElementaryAbelian.isPGroup 2 (involutionFixedKernel ρ t)).of_injective
      (inclusion hD) (inclusion_injective hD)
  have hsub : IsPGroup 2 (D.subgroupOf C) := hp.of_injective
    (subgroupOfEquivOfLe (subspaceKernel_le ρ W C)).toMonoidHom
    (subgroupOfEquivOfLe (subspaceKernel_le ρ W C)).injective
  have hle : D.subgroupOf C ≤ pCore 2 C := le_sSup ⟨hn, hsub⟩
  have hz : D.subgroupOf C = ⊥ := bot_unique (hcore ▸ hle)
  rw [← map_subgroupOf_eq_of_le (subspaceKernel_le ρ W C), hz, Subgroup.map_bot]

variable [FiniteDimensional (ZMod 2) V]

/-- A nonidentity element in a subgroup with trivial two-core strictly reduces
the common fixed space of any actor containing it and the involution. -/
theorem fixedCodim_zpowers_lt_of_centralizer_twoCore_eq_bot
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (t : G) (ht : t ^ 2 = 1) (C : Subgroup G)
    (hC : C ≤ centralizer {t}) (hcore : pCore 2 C = ⊥)
    {A : Subgroup G} (htA : t ∈ A) {b : G} (hbA : b ∈ A)
    (hbC : b ∈ C) (hb : b ≠ 1) :
    fixedCodim ρ (zpowers t) < fixedCodim ρ A := by
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr htA) a.property⟩
  have hne : fixedSpace ρ A ≠ fixedSpace ρ (zpowers t) := by
    intro he
    have hm : b ∈ subspaceKernel ρ (fixedSpace ρ (zpowers t)) C := by
      refine ⟨hbC, ?_⟩
      intro v hv
      exact (he ▸ hv : v ∈ fixedSpace ρ A) ⟨b, hbA⟩
    rw [involution_fixedSpace_kernel_eq_bot ρ hf t ht C hC hcore, mem_bot] at hm
    exact hb hm
  have hd := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank ρ (zpowers t)
  omega

/-- The strict common-fixed-space bound for a Schur-moving involution. -/
theorem finrank_add_two_le_twice_fixedCodim_of_schurMoving
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [IsIrreducible (ρ.comp L.subtype)]
    (hf : Function.Injective ρ) (t : G) (ht : t ^ 2 = 1)
    (hn : t ∈ normalizer (L : Set G)) (hs : ¬ IsSchurLinear ρ L t)
    (C : Subgroup G) (hC : C ≤ centralizer {t}) (hcore : pCore 2 C = ⊥)
    {A : Subgroup G} (htA : t ∈ A) {b : G} (hbA : b ∈ A)
    (hbC : b ∈ C) (hb : b ≠ 1) :
    Module.finrank (ZMod 2) V + 2 ≤ 2 * fixedCodim ρ A := by
  have hd := finrank_le_twice_displacement_of_not_isSchurLinear ρ L t hn hs
  have hh : Module.finrank (ZMod 2) V ≤ 2 * fixedCodim ρ (zpowers t) := by
    simpa only [fixedCodim_zpowers_eq_displacement_rank, Module.End.one_eq_id] using hd
  have hx := fixedCodim_zpowers_lt_of_centralizer_twoCore_eq_bot
    ρ hf t ht C hC hcore htA hbA hbC hb
  omega

end Representation.BinaryOffender
