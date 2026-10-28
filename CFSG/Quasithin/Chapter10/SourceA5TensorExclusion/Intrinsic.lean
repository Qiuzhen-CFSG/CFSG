module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Model

/-!
# Intrinsic consequences of the chosen A₅ tensor marking

The statements here keep the original subgroup and its original full module.
In particular, the centralizer calculation is obtained from the literal
section coordinates and determinant action; no abstract replacement of the
source module is made.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

namespace SourceA5TensorModel
include m

theorem fullModule_elementary : IsElementaryAbelian 2 D.fullModule := by
  rw [← m.module_eq]
  exact D.module_elementary

theorem fullModule_le_sylow : D.fullModule ≤ (T : Subgroup G) := by
  rw [← m.module_eq]
  exact D.module_le_sylow

theorem centralizer_localOrbit_iff (h : localOrbit T L) :
    (h : G) ∈ centralizer (D.fullModule : Set G) ↔ h ∈ m.quotient.ker := by
  have hker : (sourceA5TensorAction m.quotient).ker = m.quotient.ker := by
    ext h
    change Binary.action (m.quotient h) = 1 ↔ m.quotient h = 1
    rw [← Binary.action.map_one, Binary.action_injective.eq_iff]
  rw [← hker, m.sectionData.action_mem_ker_iff]
  simp only [Subgroup.mem_bot, mem_centralizer_iff_commutator_eq_one']
  rfl

theorem centralizer_localOrbit_eq_pCore :
    (centralizer (D.fullModule : Set G)).comap (localOrbit T L).subtype =
      pCore 2 (localOrbit T L) := by
  ext h
  change ((h : G) ∈ centralizer (D.fullModule : Set G)) ↔ h ∈ pCore 2 (localOrbit T L)
  rw [centralizer_localOrbit_iff m h, m.kernel_eq]

theorem fullModule_fixed_eq_bot :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  apply (m.sectionData.coordinates_eq_one_iff ⟨a, ha.1⟩).mp
  apply Multiplicative.toAdd.injective
  apply Displacement.common_fixed_eq_zero
  intro g
  obtain ⟨h, rfl⟩ := m.onto g
  have he := m.sectionData.equivariant h ⟨a, ha.1⟩
  have hsub :
      (⟨(h : G) * a * (h : G)⁻¹,
        (mem_normalizer_iff.mp (m.sectionData.normalized h.property)
          a).mp ha.1⟩ : D.fullModule) = ⟨a,ha.1⟩ := by
    apply Subtype.ext
    change (h : G) * a * (h : G)⁻¹ = a
    rw [ha.2 h h.property, mul_inv_cancel_right]
  rw [hsub] at he
  exact he.symm

theorem fullCentralizer_eq_bot : D.fullCentralizer = ⊥ := by
  ext a
  change (a : G) ∈ centralizer (localOrbit T L : Set G) ↔ a = 1
  constructor
  · intro ha
    apply Subtype.ext
    exact m.fullModule_fixed_eq_bot.le ⟨a.property,ha⟩
  · rintro rfl
    exact (centralizer _).one_mem

end SourceA5TensorModel
end CFSG.Quasithin.Chapter10
