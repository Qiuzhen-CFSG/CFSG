module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.Sylow

/-!
# The local hypotheses for J₁ recognition

Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.9, printed
p.418 (combined manuscript of 1 March 2004), defines a simple group to have
type J₁ when it contains a 2-central involution whose centralizer is
`PSL₂(4) × C₂`. Here 2-central means central in an ambient Sylow two-subgroup.
The local data below asserts exactly these hypotheses. The source conclusion
is an actual multiplicative equivalence to the independently constructed
`Janko1.Model`; it is not included in the local data.
-/

namespace CFSG.Quasithin

/-- The source centralizer model, using the field with four elements. -/
public abbrev Janko1CentralizerModel :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
    Multiplicative (ZMod 2)

/-- A 2-central involution and the centralizer isomorphism in I.4.9.
Simplicity is a separate ambient assumption, not part of this local data. -/
public structure Janko1CentralizerData (G : Type*) [Group G] [Finite G] where
  z : G
  involution : orderOf z = 2
  sylow : Sylow 2 G
  z_mem : z ∈ (sylow : Subgroup G)
  central : ∀ x : G, x ∈ (sylow : Subgroup G) → Commute z x
  centralizer_equiv : Nonempty (Subgroup.centralizer ({z} : Set G) ≃*
    Janko1CentralizerModel)

/-- The local definition of type J₁ on printed p.418. -/
@[expose] public def IsJanko1Type (G : Type*) [Group G] [Finite G] : Prop :=
  Nonempty (Janko1CentralizerData G)

/-- The local data is equivalent to the literal existential source hypotheses. -/
public theorem isJanko1Type_iff {G : Type*} [Group G] [Finite G] :
    IsJanko1Type G ↔ ∃ z : G, orderOf z = 2 ∧
      (∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧
        ∀ x : G, x ∈ (S : Subgroup G) → Commute z x) ∧
      Nonempty (Subgroup.centralizer ({z} : Set G) ≃* Janko1CentralizerModel) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.z, h.involution, ⟨h.sylow, h.z_mem, h.central⟩, h.centralizer_equiv⟩
  · rintro ⟨z, hz, ⟨S, hzS, hcentral⟩, hequiv⟩
    exact ⟨⟨z, hz, S, hzS, hcentral, hequiv⟩⟩

end CFSG.Quasithin
