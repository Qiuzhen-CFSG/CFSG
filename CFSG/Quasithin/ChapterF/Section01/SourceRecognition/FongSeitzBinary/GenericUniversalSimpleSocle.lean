module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniversalSimpleSocle
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GenericSimpleSocle

/-!
# The selected-factor consumer on an independent marked quotient carrier

Use the original generic preparation and perfect selected factor. The finite
marked quotient may be a quotient of the infinite universal completion,
with the local isomorphism supplied by ApartmentExchange.geometricMarkedIso.
Transport through both squares proves simplicity of its actual two-residual,
without assuming that this quotient descends to the original generated J.

The Chapter12 theorem uses the literal chosen-module input, full KnownSimple
scope, original selected R, and both endpoint markings. Earlier apartment,
root, Cartan and splitness data retain their original producer; this is the
both-perfect simple-socle reduction only. The recognition owner still owes
the minimal-configuration and seven marked Lie comparisons, including the
nonperfect branches. The DGS and generic-global assembly owners retain all
final premise discharge and exceptional alternatives.

Source: DGS, Groups and Graphs, Part II, pp.80–81 and224;
Aschbacher–Smith 5.2.6, pp.650–651, and the Chapter12 use, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- Apply the source local reduction on the supplied carrier, which may
be the universal completion rather than the actual generated subgroup. -/
theorem prepared_marked_quotient_twoResidual_isSimple
    (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hR : Group.IsPerfect R)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) : IsSimpleGroup (pResidual 2 (X ⧸ Q.D)) := by
  apply MarkedLocal.twoResidual_isSimple Q e (d.hypothesisF11 h hTH) _ split
  intro i
  fin_cases i
  · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
  · exact hR

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The original Chapter12 consumer accepts the finite universal geometric
quotient and its actual two-square marking without any ambient descent. -/
theorem rankOne_global_marked_quotient_twoResidual_isSimple
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hR : Group.IsPerfect R) (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) : IsSimpleGroup (pResidual 2 (X ⧸ Q.D)) :=
  prepared_marked_quotient_twoResidual_isSimple d
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH hR Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
