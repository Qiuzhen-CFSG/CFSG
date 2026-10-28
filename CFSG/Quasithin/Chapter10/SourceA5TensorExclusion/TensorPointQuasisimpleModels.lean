module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleRankTwo
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleSporadic

/-!
# Remaining quasisimple quotients in the original tensor point argument

SQTK inheritance and source Theorem C give the entire literal simple-quotient
catalogue. The actual central involution, rank-six tensor action and rank-seven
center-two refinement exclude every nonsporadic family and all but two
sporadic groups. Thus the original component quotient is Held or J₄.
The separate local residual arguments must discharge these two alternatives;
this theorem does not use the unproved general A.3.14 embedding shortlist.

Source: Aschbacher--Smith 9.4.1, printed p.735, with A.2.4 and I.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Exhaustive source-C inspection on the original point component quotient. -/
theorem tensorPoint_containing_quasisimple_held_or_janko4 (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    Nonempty ((I ⧸ center I) ≃* Held.He) ∨
      Nonempty ((I ⧸ center I) ≃* Janko4.Model) := by
  have hm := m.tensorPoint_containing_quotient_theoremC v hv hIX
  cases hm with
  | alternating n hn hm =>
    exact (m.tensorPoint_containing_not_alternating_quotient v hv hLI hIN hn hm).elim
  | odd hm => exact (m.tensorPoint_containing_not_odd_quotient v hv hLI hIN hm).elim
  | bender hm => exact (m.tensorPoint_containing_not_bender_quotient v hv hLI hIX hIN hm).elim
  | rank_two n hm =>
    exact (m.tensorPoint_containing_not_rank_two_quotient v hv hLI hIX hIN n hm).elim
  | linear_binary n hn hm =>
    exact (m.tensorPoint_containing_not_linear_binary_quotient v hv hLI hIX hIN hn hm).elim
  | sporadic hm => exact m.tensorPoint_containing_sporadic_held_or_janko4 v hv hLI hIX hIN hm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
