module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleMoved
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleMovedInterval
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour

/-!
# Excluding the Janko4 quotient in the original tensor point argument

The actual residual image modulo the containing center is a full-Sylow
local A5 section. Its original moved hyperplane remains elementary of order
at least16, fully moved, and irreducible modulo its fixed subgroup; the local
two-core centralizes it. The native Janko4 placement and extraspecial-core
obstruction therefore exclude this exact image. Every tensor mark is
proved on the original subgroups and maps, so no multiplier-table or
additional local-classification premise remains.

Source: Aschbacher--Smith9.4.1, printed p.735, with the native local argument
of A.3.12(17) and10.2.9, printed pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original tensor moved hyperplane excludes the Janko4 central quotient. -/
theorem tensorPoint_containing_not_janko4 (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (a : I ⧸ center I ≃* Janko4.Model) : False := by
  obtain ⟨S,hl,hn,hc,⟨eB⟩,hSE⟩ :=
    m.tensorPoint_containing_quotient_moved_local v hv hLI hIX hIN
  obtain ⟨hE,hEB,hcore,hmove⟩ :=
    m.tensorPoint_containing_quotient_moved_marks v hv hLI
  exact ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFour.not_section a S _ _
    hl hn eB hc hSE hE hEB (m.tensorPoint_containing_quotient_moved_card_ge v hv hLI)
    hcore hmove (m.tensorPoint_containing_moved_irreducible_interval v hv hLI)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
