module
public import CFSG.Quasithin.ChapterG.Section12.Defs
public import Theory.GroupTheory.SolvableResidual
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup
public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# The actual perfect action models needed from G.12

This is a conclusion vocabulary, not a recognition theorem. The first two
rows identify the embedded solvable residual of the full symplectic or
orthogonal group on the specified space. The last row includes both a group
isomorphism and an equivariant linear isomorphism with the natural binary
SL₂(4)-module. In particular it does not identify an arbitrary action by a
group-family label.

G.12.1/G.12.12 recognition must establish these alternatives for the actual
perfect normal image. The separate model argument must then prove the
center and automorphism facts it uses. Source: Aschbacher--Smith, printed
pp.363,370,374--375.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The solvable residual embedded in the original linear group. -/
def embeddedResidual (D : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Subgroup (V ≃ₗ[ZMod 2] V) := (Subgroup.solvableResidual D).map D.subtype

/-- The precise natural action, including the module identification. -/
def NaturalSL2Four (K : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∃ e : K ≃* Representation.SL2FourNatural.SL,
    ∃ f : V ≃ₗ[ZMod 2] Representation.SL2FourNatural.V,
      ∀ k : K, ∀ v : V, f (k.val v) = Representation.SL2FourNatural.action (e k) (f v)

/-- The perfect action rows needed by the central-kernel G.10.15 consumer.
In degree four the symplectic residual row includes the actual A₆ action. -/
def ResidualModel (K : Subgroup (V ≃ₗ[ZMod 2] V))
    (B : LinearMap.BilinForm (ZMod 2) V) : Prop :=
  K = embeddedResidual (formStabilizer B) ∨
  (∃ q : QuadraticForm (ZMod 2) V,
    q.polarBilin = B ∧ K = embeddedResidual q.isometrySubgroup) ∨
  NaturalSL2Four K

end CFSG.Quasithin.ChapterG.Section12
