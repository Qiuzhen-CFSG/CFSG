module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Models
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Contracts

/-!
# Earlier source inputs for the three-centralizer recognition

`EarlierConclusions` contains only the order and selected geometry of 47.1
and the full marked five-local conclusions of 47.2 in Aschbacher,
*Sporadic Groups* (1994), printed pp.259–261. The two product models in
`SelectedGeometry` preserve the intrinsic component and core, the placement
of z, and the Sylow-three subgroup X of the component's centralizer.
`SourceConclusion` retains the actual five-components, their generation
and complements, both five-families, and the self-centralizing Sylow fives.

The source producers are `qt-i47-j2-source-involutions` for `card` and
`geometry`, and `qt-i47-j2-five-local-calculation` for `five` at that same
selected involution. Their constructions are not asserted here. In particular
this input contains no perfectness, A₆ quotient, three-Sylow structure,
inverting involution, or order-eight element from the desired 47.3 result.
-/

@[expose] public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal

variable {G : Type*} [Group G] [Finite G]

/-- The exact earlier conclusions used by the conditional 47.3 recognition. -/
structure EarlierConclusions (D : Seed G) where
  card : Nat.card G = 604800
  geometry : InvolutionGeometry.SelectedGeometry D
  five : FiveLocal.SourceConclusion D geometry.t

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
