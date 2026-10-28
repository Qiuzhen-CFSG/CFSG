module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.CommutingCubic.OddComplement
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.SymmetricSix.CommutingCubic

/-!
# Applying the odd-complement construction to the commuting cubic

The constructed odd core discharges the transfer input of the existing
four-group calculation in Aschbacher's Lemma 4.5 (p.40). The remaining
fusion of `uz` is deliberately explicit: it is supplied by the separate
outside-core orbit argument, and remains with the source assembly owner.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The commuting cubic after discharging the odd-complement input. -/
public theorem commutingCubicData_of_uz_fused (h : Hypotheses z)
    (a : SourceGeometry h) (huz : IsConj z (a.u * z)) :
    Nonempty (CommutingCubicData h a) := by
  obtain ⟨o⟩ := oddCentralizerData h a
  exact commutingCubicData_of_oddCentralizer o huz

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup
