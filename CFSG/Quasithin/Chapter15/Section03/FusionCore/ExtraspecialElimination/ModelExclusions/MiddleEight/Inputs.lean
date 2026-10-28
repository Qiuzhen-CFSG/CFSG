module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Preparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Transport

/-!
# The actual point and star conjugacy in the middle-node branch

The input retains the component commutator submodule, its central supplement,
the vector whose stabilizer is Y₀*T*, and the conjugacy from Vγ* to Vα*.
Best offending and placement in the point two-core are already retained by
`BorelInner.SourceSetup`. Strong offending is (n). No module coordinates or
geometric rank bound occur among these earlier source inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed pp.1143–1145, especially the paragraph before (k) and (n).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open ComponentReduction.ModelReduction

universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {H M Y V Y₀ L ZS Z A : Subgroup G} {T : Sylow 2 G}
  [IsElementaryAbelian 2 (localSpan ZS H)]

/-- The genuine earlier point and module identities, before classifying the
component module. The starred actor is always the literal H/O₂(H). -/
structure PointData
    (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T) (Vγ : Subgroup G) where
  space : Subrepresentation d.action.representation
  component_space : space.toSubmodule =
    Representation.Coinvariants.ker (d.action.representation.comp (starImage H L).subtype)
  supplement : space.toSubmodule ⊔ d.action.representation.invariants = ⊤
  point : space.toSubmodule
  stabilizer : starImage H Y₀ ⊔ starImage H (T : Subgroup G) =
    pointStabilizer space.toRepresentation point
  conjugator : H ⧸ pCore 2 H
  conjugacy : starImage H A = (starImage H Vγ).map (MulAut.conj conjugator).toMonoidHom
  strong : IsStrongOffender d.action.representation (starImage H Vγ)

variable (d : BorelInner.SourceSetup κ H M Y V Y₀ L ZS Z A T)
  {Vγ : Subgroup G} (p : PointData d Vγ)

include p in
/-- Clause (n) transfers to precisely the offender placed in the point core. -/
theorem PointData.strong_alpha :
    IsStrongOffender d.action.representation (starImage H A) :=
  ModelExclusions.strong_alpha d.action p.strong p.conjugator p.conjugacy

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight
