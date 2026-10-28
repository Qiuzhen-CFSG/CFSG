module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.JointKernels

/-!
# The proved Cartan and centralizer clauses of Fong--Seitz (6H)

The common-field construction already gives the actual two-factor Cartan
equivalence on the marked quotient. Two additional elementary consequences
are separation by the two simple roots and centralization of each rank-one
root group by its panel kernel. These are only part of (6H); both are
proved here from the literal Cartan centralizer identities and the faithful
Borel core argument; no model torus or simplicity predicate is substituted.

Source: Fong--Seitz I (1973), proof of (6H)(a), pp.51--56.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

/- The two simple roots are the independent roots in the marked rank-two
   carrier.  Rewriting each Cartan centralizer by its actual panel kernel
   reduces the statement to the already proved faithful joint-kernel theorem. -/
theorem sixH_joint_simpleRoot_centralizer_eq_bot
    (s : ∀ i, RootReflection Q split i)
    (hcore : Q.tits.B.normalCore = ⊥) :
    ((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      centralizer (simpleRoot Q split 0 : Set (X ⧸ Q.D))) ⊓
      centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hx0 : x ∈ (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      embeddedPanelKernel Q 0 := by
    have h := hx.1
    rw [cartan_centralizer_simpleRoot Q split 0] at h
    exact h
  have hx1 : x ∈ (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      embeddedPanelKernel Q 1 := by
    have h : x ∈ (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
        centralizer (simpleRoot Q split 1 : Set (X ⧸ Q.D)) :=
      ⟨hx.1.1, hx.2⟩
    rw [cartan_centralizer_simpleRoot Q split 1] at h
    exact h
  exact (joint_cartan_kernel_eq_bot Q split s hcore).le ⟨hx0, hx1.2⟩

/- The panel kernel is the precise Cartan centralizer of the corresponding
   rank-one root group, so it centralizes that whole source rank-one carrier. -/
theorem sixH_panelKernel_centralizes_rankOne
    (i : Fin 2) :
    ((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      embeddedPanelKernel Q i) ≤
      centralizer (rankOneRootGroup Q split i : Set (X ⧸ Q.D)) := by
  rw [← cartan_centralizer_rankOneRootGroup Q split i]
  exact inf_le_right

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
