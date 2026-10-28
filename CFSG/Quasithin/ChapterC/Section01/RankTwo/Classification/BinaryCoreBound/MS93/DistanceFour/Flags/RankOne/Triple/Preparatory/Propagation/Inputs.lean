module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.ModuleSection

/-!
# The two source branches in flag propagation

`SingleSection` expands the source notation c(V₀/Z_alpha) = 1 using the
existing split natural-section definition. The groups are pulled back
through embedM, so the acting quotient is the original source projection
and its kernel. No constituent count substitutes for this representation.

`TransportedGenerator` specifies the displayed identity in the other
branch. Its lambda is obtained by one actual amalgam element transporting
the ordered pair (middle, alpha) to (lambda, mu). The identity is an
output still to be proved; it is not inferred merely from non-single
naturality. The final propagation assembly must discharge both branches.

Source: Meierfrankenfeld--Stellmacher (1993), notation on p.881 and
(4.6.8), claim (2), printed p.906.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The full source meaning of c(V₀/Z_alpha) = 1, for the given marked quotient. -/
def SingleSection (p : FlagCriticalData source geometry i) : Prop :=
  Nonempty (Escape.SingleNaturalSection source.projection source.projection.ker
    (pResidual 2 M) ((midpointSpan p).comap (embedM R))
    ((Z R (alpha R)).comap (embedM R)))

/-- The actual transported vertex and displayed commutator generation on p.906. -/
structure TransportedGenerator (p : FlagCriticalData source geometry i) (t : Vertex R) where
  lam : Vertex R
  conjugator : FreeAmalgam R
  base_image : act R conjugator (alpha R) = t
  middle_image : act R conjugator p.middle = lam
  escapes : ¬ Z R lam ≤ Q R (alpha R)
  generation : Z R t =
    ⁅Z R lam, midpointSpan p ⊓ Q R t⁆ ⊔ (Z R t ⊓ Z R (alpha R))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
