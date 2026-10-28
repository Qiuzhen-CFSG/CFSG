module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.Generators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.CentralQuotients

/-!
# Properness of the folded E8 subgroup after the central quotient

The last E8 simple node is orthogonal to all six E6 nodes. Its parameter-one
positive root element therefore commutes with every folded generator, with
either sign. That element is noncentral in the cover. Since the ambient
center also centralizes it, the folded subgroup cannot surject onto the
central quotient. This argument works over every field, including GF(3).

This proves the properness part of the E8 inclusion used in
Aschbacher--Smith A.2.17, printed p.39. Identifying the generated subgroup
with the given E6 folded carrier remains a separate matrix-relation problem.
The subsystem commutation is GLS3 §2.6.2 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem

namespace TwistedE6.FoldedSubsystem.HigherRealizations

attribute [local instance] Classical.decEq
local instance : Fintype typeE8Roots := Fintype.ofFinite _

variable (F : Type*) [Field F]

/-- A root element in the orthogonal A1, on the last E8 node. -/
def e8ExtraRoot : ExceptionalSplit.e8Cover F := e8Simple F true 7 1

theorem e8ExtraRoot_noncentral :
    e8ExtraRoot F ∉ Subgroup.center (ExceptionalSplit.e8Cover F) :=
  ExceptionalSplit.elementaryRoot_simple_one_not_mem_center
    (typeE8RootPairing_baseEquiv 7)

theorem e8ExtraRoot_commute_simple (s : Bool) (i : Fin 6) (t : F) :
    Commute (e8ExtraRoot F) (e8Simple F s (i.castLE (by decide)) t) := by
  have hne : typeE8RootPairing_baseEquiv 7 ≠
      typeE8RootPairing_baseEquiv (i.castLE (by decide)) := by
    intro h
    have hv := congrArg Fin.val (typeE8RootPairing_baseEquiv.injective h)
    simp only [Fin.val_castLE] at hv
    omega
  cases s
  · exact signedSimple_opposite_commute F _ _ hne 1 t
  · apply signedSimple_commute F true _ _ hne
    rw [typeE8RootPairing_base_cartan_apply]
    fin_cases i <;> decide

theorem e8ExtraRoot_commute_folded (s : Bool) (i : Fin 4) (t : F) :
    Commute (e8ExtraRoot F) (e8FoldedSimple F s i t) := by
  fin_cases i
  · exact e8ExtraRoot_commute_simple F s 3 t
  · exact e8ExtraRoot_commute_simple F s 2 t
  · exact (e8ExtraRoot_commute_simple F s 1 t).mul_right
      (e8ExtraRoot_commute_simple F s 4 t)
  · exact (e8ExtraRoot_commute_simple F s 0 t).mul_right
      (e8ExtraRoot_commute_simple F s 5 t)

/-- The entire concrete generated subgroup centralizes the displayed root. -/
theorem e8FoldedSubgroup_le_centralizer :
    e8FoldedSubgroup F ≤ Subgroup.centralizer ({e8ExtraRoot F} : Set _) := by
  rw [e8FoldedSubgroup, Subgroup.closure_le]
  rintro _ ⟨⟨s, i, t⟩, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (e8ExtraRoot_commute_folded F s i t).eq.symm

/-- The literal central projection restricted to the concrete folded E8 subgroup. -/
def e8FoldedProjection : e8FoldedSubgroup F →* ExceptionalSplit.E8 F :=
  (ExceptionalSplit.projection typeE8RootPairing typeE8RootPairing_base F).comp
    (e8FoldedSubgroup F).subtype

theorem e8FoldedProjection_proper : (e8FoldedProjection F).range ≠ ⊤ := by
  apply centralProjection_range_ne_top (e8FoldedSubgroup F).subtype
    (e8ExtraRoot F) (e8ExtraRoot_noncentral F)
  intro h
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (e8FoldedSubgroup_le_centralizer F h.property)).symm

/-- Every homomorphism with the displayed generator formulas has proper
projected image. No injectivity or field-characteristic assumption is needed. -/
theorem e8_marked_projection_proper
    (f : splitSubgroup F →* ExceptionalSplit.e8Cover F)
    (hf : ∀ s i t, f (f4Simple F s i t) = e8FoldedSimple F s i t) :
    ((ExceptionalSplit.projection typeE8RootPairing typeE8RootPairing_base F).comp f).range
      ≠ ⊤ := by
  apply centralProjection_range_ne_top f (e8ExtraRoot F) (e8ExtraRoot_noncentral F)
  intro h
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (e8FoldedSubgroup_le_centralizer F (e8_range_le F f hf ⟨h, rfl⟩))).symm

/-- The E8 constructor consumed by `f4InE8OfFolding`, once the marked matrix
homomorphism is constructed and its injectivity established. -/
def e8ProperEmbeddingOfMarkedHom
    (f : splitSubgroup F →* ExceptionalSplit.e8Cover F)
    (hi : Function.Injective f)
    (hf : ∀ s i t, f (f4Simple F s i t) = e8FoldedSimple F s i t)
    (hc : Subgroup.center (splitSubgroup F) = ⊥) :
    ExceptionalSplit.ProperEmbedding (splitSubgroup F) (ExceptionalSplit.E8 F) where
  hom := (ExceptionalSplit.projection typeE8RootPairing typeE8RootPairing_base F).comp f
  injective := centralProjection_injective f hi hc
  proper := e8_marked_projection_proper F f hf

end TwistedE6.FoldedSubsystem.HigherRealizations
