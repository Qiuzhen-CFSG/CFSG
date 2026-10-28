module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Actors.CoreNorm
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition

/-!
# Applying the constructed normalizer actors to centralizer recognition

The 47.2 component now supplies the inverting actor in the index-two and
index-six arguments. Only the independent Sylow bounds remain explicit in
the latter reduction. The completed order-eight construction also supplies
the second actor field of `CentralizerCalculation`. Its independent
perfectness and actual A₆ quotient remain with the centralizer-recognition
assembly owners `qt-i47-j2-three-centralizer-core-recognition` and
`qt-i47-j2-three-centralizer-recognition`.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, p.262.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The source geometry discharges the actor premise in the literal index. -/
theorem EarlierConclusions.centralizer_index (E : EarlierConclusions D) :
    (CM D).index = 2 := by
  obtain ⟨m, _, hm⟩ := E.exists_inverter
  exact centralizer_index_of_inverting_element m hm

/-- The index-six reduction now requires only the independent Sylow bounds. -/
theorem EarlierConclusions.component_index_six_of_sylow_bounds (E : EarlierConclusions D)
    (hcard : Nat.card (C D) = 1080 ∨ Nat.card (C D) = 7560) :
    (InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X).relIndex (C D) = 6 := by
  obtain ⟨m, _, hm⟩ := E.exists_inverter
  exact component_index_six_of_local_bounds E m hm hcard

/-- The actor constructions discharge both normalizer-witness premises of
the extension recognition. Only the independent perfect-cover conclusions
remain as inputs, using the literal quotient C_G(X)/X. -/
theorem EarlierConclusions.centralizerCalculation_of_cover (E : EarlierConclusions D)
    (hperfect : Group.IsPerfect (C D))
    (hquotient : Nonempty ((C D ⧸ XC D) ≃* alternatingGroup (Fin 6))) :
    Nonempty (CentralizerCalculation D) := by
  obtain ⟨⟨m, hm, hinv⟩, hs⟩ := E.normalizer_actors
  exact ⟨{ perfect := hperfect
           alternatingQuotient := hquotient
           inverter := m
           inverter_order := hm
           inverts_X := hinv
           eight := hs }⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
