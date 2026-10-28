module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Geometry

/-!
# The two local inputs to the fixed-residual branch

The block specialization of C.1.34 supplies two identities on the original
subgroups. The separate B.4.8 calculation gives the order and fixed planes
of the actual action of R on V after its centralizer is V. Neither input
asserts a maximum elementary family, normalizer containment or fusion.

The Frattini argument and the B.2.21 consumer are kept separate so that the
block specialization and the local action calculation can be proved
independently. Their source assembly must discharge both inputs.

Source: Aschbacher–Smith, 12.4.5(3) and the first escaping-normalizer case
of 12.4.6, printed pp.813–814; C.1.34, p.136, and B.4.8(2), p.91.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The precise two products used from the source block calculation.
The first centralizer is C_T(V), and the second uses the literal residual
O²(C_L(E)) embedded in G. -/
structure FixedBlockIdentities (d : LocalGeometry D) : Prop where
  product : (T : Subgroup G) ⊓ centralizer (V : Set G) =
    V ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))
  residual_centralizer : d.R ⊓ centralizer (d.L₁ : Set G) =
    d.E ⊔ ((T : Subgroup G) ⊓ centralizer (L : Set G))

/-- Numerical and pointwise fixed-space facts for the original R-action.
The relative index is the order of the literal quotient by V once the
Frattini argument has proved C_T(V)=V. -/
structure FixedBlockAction (d : LocalGeometry D) : Prop where
  module_card : Nat.card V = 16
  actor_index : V.relIndex d.R = 4
  fixed_plane : ∀ a ∈ d.R, a ∉ V → V ⊓ centralizer ({a} : Set G) = d.E

/-- The outstanding C.1.34 specialization. Its producer must establish the
MS hypotheses and compare the alternatives on the original chosen module. -/
def FixedBlockCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ d : LocalGeometry D,
    ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G) → FixedBlockIdentities d

/-- The independent B.4.8 calculation, allowed to use the proved equality
C_T(V)=V but not a conclusion about maximum elementary subgroups. -/
def FixedBlockActionCalculation : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (T : Sylow 2 G) (L V : Subgroup G),
    Hypothesis1223 KnownSimple.IsKnownSimple T L → (D : ChosenModule T L V) →
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 → fixedSubgroup L V ≠ ⊥ →
    ∀ d : LocalGeometry D,
    ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G) →
    (T : Subgroup G) ⊓ centralizer (V : Set G) = V → FixedBlockAction d

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
