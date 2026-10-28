module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition.LocalHypotheses
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition.Geometry

/-!
# The dimension-three recognition in 12.2.27

The actual affine centralizer satisfies I.4.6, and its quaternion factors are
nonnormal there. The completed A₃ coset geometry gives A₈ or A₉ after the
normal elementary-eight alternative is excluded by the original simplicity
hypotheses. The genuine A₈/PSL₄(2) equivalence gives the printed alternatives.
The application to 12.2.13 retains the original block C.block.

The split linear configuration is the precise earlier-source input owned by
qt-d-12213-local-configuration. Its construction and the other dimensions
remain with the parent qt-d-1222-recognition. No additional premise is imposed
on this dimension-three endpoint.
Source: Aschbacher–Smith 12.2.27(2), p.807; I.4.6, p.417.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem source_recognition (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (hnone : NoEscape L V)
    (C : SplitLinearConfiguration L V 3) :
    ClassicalGroup.IsPSL G 4 2 ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) := by
  obtain ⟨v,_,hv,hn⟩ := local_hypotheses D hnone C
  exact source_recognition_of_local h ⟨v,hv,hn⟩

theorem recognizedGroup (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (hnone : NoEscape L V)
    (C : SplitLinearConfiguration L V 3) : RecognizedGroup G 3 := by
  rcases source_recognition h D hnone C with hp | ha
  · exact Or.inl hp
  · exact Or.inr (Or.inl ⟨rfl,ha⟩)

theorem alternatives (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (hnone : NoEscape L V)
    (C : SplitLinearConfiguration L V 3) : Alternatives12213 T L V := by
  rcases source_recognition h D hnone C with hp | ha
  · exact Or.inr (Or.inl ⟨3,Or.inl rfl,C.block,hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨C.block,ha⟩))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
