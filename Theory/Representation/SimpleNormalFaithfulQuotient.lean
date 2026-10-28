module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SimpleHeadQuotient
public import Theory.GroupTheory.FaithfulNormalRestriction
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Faithful proper quotients of a fully moved binary module

Let K be a simple normal subgroup with trivial centralizer. If [V,K]=V,
every nonzero quotient of V has nontrivial K-action. Simplicity makes
that restricted action faithful. Its full kernel centralizes K, hence
is trivial. In particular all maximal invariant quotients are faithful
irreducible modules, with the original quotient projection.

Source application: the opening maximal-quotient step of
Aschbacher–Smith 14.7.50, printed p.1064, using 14.7.48(2).
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A fully moving actor survives on every nonzero quotient. -/
theorem not_le_quotient_ker_of_full_movement
    (K : Subgroup G) (hm : subspaceCommutator ρ ⊤ K = ⊤)
    (N : Subrepresentation ρ) (hN : N ≠ ⊤) : ¬ K ≤ N.quotientRepresentation.ker := by
  intro hk
  apply hN
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [←hm]
  apply Submodule.span_le.mpr
  rintro _ ⟨k,hkK,v,_,rfl⟩
  apply (Submodule.Quotient.eq N.toSubmodule).mp
  exact LinearMap.congr_fun (hk hkK) (N.toSubmodule.mkQ v)

/-- If a self-centralizing simple normal subgroup fully moves a binary module,
every nonzero quotient of that module is faithful. -/
theorem quotient_faithful_of_simple_normal_full_movement
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (hc : centralizer (K : Set G) = ⊥)
    (hm : subspaceCommutator ρ ⊤ K = ⊤)
    (N : Subrepresentation ρ) (hN : N ≠ ⊤) :
    Function.Injective N.quotientRepresentation := by
  apply MonoidHom.injective_of_injective_normal_restriction N.quotientRepresentation K _ hc
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.quotientRepresentation.comp K.subtype).ker inferInstance with hb | ht
  · exact hb
  · exfalso
    apply not_le_quotient_ker_of_full_movement ρ K hm N hN
    intro k hk
    have hh : (⟨k,hk⟩ : K) ∈ (N.quotientRepresentation.comp K.subtype).ker := by
      rw [ht]
      trivial
    exact hh

/-- Maximal invariant quotients of the same original action are faithful and irreducible. -/
theorem coatom_quotient_faithful_irreducible_of_simple_normal_full_movement
    (K : Subgroup G) [K.Normal] [IsSimpleGroup K]
    (hc : centralizer (K : Set G) = ⊥)
    (hm : subspaceCommutator ρ ⊤ K = ⊤)
    (N : Subrepresentation ρ) (hN : IsCoatom N) :
    Function.Injective N.quotientRepresentation ∧ IsIrreducible N.quotientRepresentation :=
  ⟨quotient_faithful_of_simple_normal_full_movement ρ K hc hm N hN.ne_top,
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN⟩
end Representation
