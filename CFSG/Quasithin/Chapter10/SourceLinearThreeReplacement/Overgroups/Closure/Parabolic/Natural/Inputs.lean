module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Coordinates
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Inputs

/-!
# Independent inputs for diagonal-parabolic recognition

The source calculation constructs the complete wreath image of the original
conjugation action, in the canonical coordinates of the two moved factors,
and proves that its kernel is a two-group. The separate finite-model
calculation identifies nonzero-coordinate point stabilizers as maximal
S₄-wreath subgroups. Neither obligation is asserted here; their combination
will recognize the literal source centralizer and its two-core quotient.

Source: Aschbacher--Smith 10.2.4 and 10.2.11, pp.747,753--754.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original conjugation action, restricted to L₀T. -/
def joinAction (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    localJoin T L →* MulAut D.fullModule :=
  D.fullModule.normalizerMonoidHom.comp (inclusion
    ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)).trans
      D.maximalLocal_normalizes_fullModule))

theorem joinAction_apply (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (g : localJoin T L) (v : D.fullModule) :
    (joinAction D g v : G) = (g : G) * v * (g : G)⁻¹ := rfl

theorem joinAction_ker (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (joinAction D).ker = (centralizer (D.fullModule : Set G)).subgroupOf (localJoin T L) := by
  ext g
  change D.fullModule.normalizerMonoidHom (inclusion _ g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

/-- A marking of the whole original action, before selecting any parabolic.
The coordinates are fixed by the survivor and its specified exchanger. -/
structure ActionData {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (s : SourceLinearThreeSurvivor T D)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) where
  hom : localJoin T L →* Actor
  onto : Function.Surjective hom
  kernel_two : IsPGroup 2 hom.ker
  equivariant (g : localJoin T L) (v : D.fullModule) :
    fullCoordinates s hz (joinAction D g v) = action (hom g) (fullCoordinates s hz v)

/-- The original source action calculation. It has no parabolic conclusion. -/
def NaturalActionAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s),
    Nonempty (ActionData s d.fixed_part)

/-- The finite-model calculation, independent of the ambient source group.
The output is the whole stabilizer, before passage to its two-core quotient. -/
def ModelGeometry : Prop :=
  ∀ v : Space, (∀ i, v i ≠ 1) → IsCoatom (pointStabilizer v) ∧
    Nonempty (pointStabilizer v ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) Bit)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
