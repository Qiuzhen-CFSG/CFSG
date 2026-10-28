module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Mathieu.M12.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod

/-!
# The exact local hypotheses and alternatives of I.4.6

For an involution `z`, the local group is its centralizer and its core is the
intrinsic generalized Fitting subgroup. The Sylow three-subgroup is taken
inside that centralizer. Weak closure fails in the image of the core in the
ambient group. Quaternion-subgroup normality always means normality inside
the involution centralizer, not inside the ambient group.

The alternatives use the actual binary projective special linear group,
alternating permutation groups, and automorphism group of the Witt design.
The existence and uniqueness of the two quaternion subgroups are separate
local results; no sign, quaternion factorization, simplicity, or recognition
conclusion is included in the hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.6,
combined manuscript of 1 March 2004, printed p.417; M. Aschbacher,
“A 2-local characterization of M12”, Illinois J. Math. 47 (2003), 31–47.
-/

@[expose] public section

namespace CFSG.Quasithin.Extraspecial32

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G]

/-- The source's `H = C_G(z)`. -/
abbrev Centralizer (z : G) : Subgroup G := centralizer ({z} : Set G)

/-- The distinguished element considered inside its centralizer. -/
def distinguished (z : G) : Centralizer z :=
  ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

/-- The source's `Q = F*(H)`, as a subgroup of `H`. -/
abbrev Core (z : G) : Subgroup (Centralizer z) := generalizedFitting (Centralizer z)

/-- The same core embedded in the ambient group. -/
def coreInG (z : G) : Subgroup G := (Core z).map (Centralizer z).subtype

/-- Precisely the hypotheses of source I.4.6, including the chosen Sylow subgroup. -/
structure Hypotheses (z : G) [Finite G] where
  involution : orderOf z = 2
  extraspecial : IsExtraspecial 2 (Core z)
  core_card : Nat.card (Core z) = 32
  quotient_model : Nonempty ((Centralizer z ⧸ Core z) ≃* Equiv.Perm (Fin 3))
  X : Sylow 3 (Centralizer z)
  fixed : Core z ⊓ centralizer (X : Set (Centralizer z)) = zpowers (distinguished z)
  fused : ∃ g : G, g * z * g⁻¹ ∈ coreInG z ∧ g * z * g⁻¹ ≠ z

/-- Every quaternion subgroup of `Q` is normal in `H`. -/
def QuaternionSubgroupsNormal (z : G) : Prop :=
  ∀ R : Subgroup (Core z), Nonempty (R ≃* QuaternionGroup 2) →
    (R.map (Core z).subtype).Normal

/-- Neither quaternion subgroup of `Q` is normal in `H`. -/
def QuaternionSubgroupsNonnormal (z : G) : Prop :=
  ∀ R : Subgroup (Core z), Nonempty (R ≃* QuaternionGroup 2) →
    ¬ (R.map (Core z).subtype).Normal

/-- Alternative (1), with a normal elementary eight and the actual `PSL₃(2)` quotient. -/
def ElementaryEightAlternative (G : Type*) [Group G] : Prop :=
  ∃ (V : Subgroup G) (_ : V.Normal), IsElementaryAbelian 2 V ∧ Nat.card V = 8 ∧
    Nonempty ((G ⧸ V) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))

/-- All three source alternatives, including both relative normality clauses. -/
def Conclusion (z : G) : Prop :=
  ElementaryEightAlternative G ∨
    ((Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
        Nonempty (G ≃* alternatingGroup (Fin 9))) ∧ QuaternionSubgroupsNonnormal z) ∨
    (Nonempty (G ≃* Sporadic.Mathieu.M12) ∧ QuaternionSubgroupsNormal z)

end CFSG.Quasithin.Extraspecial32

end
