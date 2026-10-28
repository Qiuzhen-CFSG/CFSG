module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Replay.Inputs

/-! Kernel checked dependency slice of the local word rewriting certificate.
The source equations are explicit inputs; this module assumes no group order. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Replay
variable {G : Type*} [Group G]

theorem eq_0 (P : Inputs G) :
    readWord P.g [0, 0] = readWord P.g [] := by
  have h : readWord P.g [0, 0] = readWord P.g [] :=
    cancel P.g P.inverse 0
  have ha : readWord P.g [0, 0] = readWord P.g [0, 0] := rfl
  have hb : readWord P.g [] = readWord P.g [] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_1 (P : Inputs G) :
    readWord P.g [2, 1] = readWord P.g [] := by
  have h : readWord P.g [2, 1] = readWord P.g [] :=
    cancel P.g P.inverse 2
  have ha : readWord P.g [2, 1] = readWord P.g [2, 1] := rfl
  have hb : readWord P.g [] = readWord P.g [] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_2 (P : Inputs G) :
    readWord P.g [1, 2] = readWord P.g [] := by
  have h : readWord P.g [1, 2] = readWord P.g [] :=
    cancel P.g P.inverse 1
  have ha : readWord P.g [1, 2] = readWord P.g [1, 2] := rfl
  have hb : readWord P.g [] = readWord P.g [] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_5 (P : Inputs G) :
    readWord P.g [1, 1] = readWord P.g [2, 2] := by
  have h : readWord P.g [2, 2] = readWord P.g [1, 1] :=
    seed P.g P.inverse (sourceWord 1) [2, 2] [1, 1] true 1 (by decide) (P.relation 1)
  have ha : readWord P.g [2, 2] = readWord P.g [2, 2] := rfl
  have hb : readWord P.g [1, 1] = readWord P.g [1, 1] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_6 (P : Inputs G) :
    readWord P.g [0, 1, 0, 1, 0, 1] = readWord P.g [2, 0, 2, 0, 2, 0] := by
  have h : readWord P.g [0, 1, 0, 1, 0, 1] = readWord P.g [2, 0, 2, 0, 2, 0] :=
    seed P.g P.inverse (sourceWord 2) [0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0] true 1 (by decide) (P.relation 2)
  have ha : readWord P.g [0, 1, 0, 1, 0, 1] = readWord P.g [0, 1, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [2, 0, 2, 0, 2, 0] = readWord P.g [2, 0, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_7 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 1, 0] = readWord P.g [0, 2, 0, 2, 0, 2] := by
  have h : readWord P.g [1, 0, 1, 0, 1, 0] = readWord P.g [0, 2, 0, 2, 0, 2] :=
    seed P.g P.inverse (sourceWord 2) [1, 0, 1, 0, 1, 0] [0, 2, 0, 2, 0, 2] true 0 (by decide) (P.relation 2)
  have ha : readWord P.g [1, 0, 1, 0, 1, 0] = readWord P.g [1, 0, 1, 0, 1, 0] := rfl
  have hb : readWord P.g [0, 2, 0, 2, 0, 2] = readWord P.g [0, 2, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_8 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] := by
  have h : readWord P.g [0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1] = readWord P.g [2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2] :=
    seed P.g P.inverse (sourceWord 4) [0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1] [2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2] false 12 (by decide) (P.relation 4)
  have ha : readWord P.g [0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] := (context P.g [0, 2, 2, 0] [0, 2, 0, 1, 0, 1, 1, 0, 1] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] [0, 1] [1, 1] [2, 2] (eq_5 P))
  have hb : readWord P.g [2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] := (context P.g [2, 0, 1, 0] [0, 1, 1, 0, 2, 0, 1, 0, 2] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [2, 0, 1, 0, 2, 2, 0] [0, 2, 0, 1, 0, 2] [1, 1] [2, 2] (eq_5 P))
  exact (ha.symm.trans (h.trans hb))

theorem eq_9 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] := by
  have h : readWord P.g [2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1] = readWord P.g [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0] :=
    seed P.g P.inverse (sourceWord 4) [2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0] false 13 (by decide) (P.relation 4)
  have ha : readWord P.g [2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] := (context P.g [2, 2, 0] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0] [0, 1, 1] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [] [1, 1] [2, 2] (eq_5 P)))
  have hb : readWord P.g [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] := (context P.g [0, 2, 0, 1, 0] [0, 1, 1, 0, 2, 0, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 0, 1, 0] [1, 1] [2, 2] (eq_5 P))
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_11 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] :=
    seed P.g P.inverse (sourceWord 4) [2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1] [0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] false 9 (by decide) (P.relation 4)
  have ha : readWord P.g [2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] := context P.g [2, 0, 1, 0, 2, 2, 0] [0, 2, 0, 1, 0, 1] [1, 1] [2, 2] (eq_5 P)
  have hb : readWord P.g [0, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := (context P.g [0] [0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [0, 2, 2, 0] [0, 2, 0, 1, 0, 2, 2, 0, 2] [1, 1] [2, 2] (eq_5 P))
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_12 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0] = readWord P.g [0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] :=
    seed P.g P.inverse (sourceWord 4) [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0] [0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] false 6 (by decide) (P.relation 4)
  have ha : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := context P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 0] [1, 1] [2, 2] (eq_5 P)
  have hb : readWord P.g [0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] := context P.g [0] [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] [1, 1] [2, 2] (eq_5 P)
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_13 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1] = readWord P.g [1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] :=
    seed P.g P.inverse (sourceWord 4) [2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1] [1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] false 7 (by decide) (P.relation 4)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] := context P.g [2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 0, 1] [1, 1] [2, 2] (eq_5 P)
  have hb : readWord P.g [1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] := context P.g [1, 0] [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] [1, 1] [2, 2] (eq_5 P)
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_14 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] := by
  have h : readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] :=
    seed P.g P.inverse (sourceWord 4) [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0] [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] false 4 (by decide) (P.relation 4)
  have ha : readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] := context P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0] [1, 1] [2, 2] (eq_5 P)
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_21 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2] := by
  have h : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [0, 1, 1, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0] :=
    seed P.g P.inverse (sourceWord 3) [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1] [0, 1, 1, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0] false 15 (by decide) (P.relation 3)
  have ha : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [0, 1, 1, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0] = readWord P.g [2, 0, 1, 0, 2, 2] := (context P.g [0] [1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2] [1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [0] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [] [2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0] [0, 0] [] (eq_0 P)).trans ((context P.g [2, 0, 1, 0] [0, 1, 1, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 0, 1, 0, 2, 2, 0] [1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 0, 1, 0, 2, 2, 0, 2] [1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [2, 0, 1, 0, 2, 2, 0] [0] [2, 1] [] (eq_1 P)).trans (context P.g [2, 0, 1, 0, 2, 2] [] [0, 0] [] (eq_0 P)))))))))
  exact (ha.symm.trans (h.trans hb))

theorem eq_32 (P : Inputs G) :
    readWord P.g [0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := by
  have h : readWord P.g [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] :=
    seed P.g P.inverse (sourceWord 6) [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] true 47 (by decide) (P.relation 6)
  have ha : readWord P.g [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] = readWord P.g [0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] := (context P.g [0] [1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [0, 2] [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] [2, 1] [] (eq_1 P))
  have hb : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := context P.g [] [0, 2, 0, 1, 0, 2, 0, 1] [2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1] [2, 0, 1, 0, 2, 2] (eq_21 P)
  exact (ha.symm.trans (h.trans hb))

theorem eq_76 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0] := by
  have h : readWord P.g [1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0] :=
    seed P.g P.inverse (sourceWord 6) [1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0] false 34 (by decide) (P.relation 6)
  have ha : readWord P.g [1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2] := (context P.g [] [1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2] [0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] [2, 1] [] (eq_1 P)).trans ((context P.g [2, 0, 1, 0, 2, 0, 1, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [1, 0, 2, 2, 2, 0, 2, 2, 0, 2] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0, 2, 2, 2, 0, 2, 2, 0, 2] [2, 1] [] (eq_1 P)))))
  have hb : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0] := (context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] [0, 1, 1, 1, 1, 0, 2, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [1, 1, 0, 2, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] [1, 0, 2, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 0] [2, 1] [] (eq_1 P)).trans (context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] [2, 0] [0, 0] [] (eq_0 P)))))
  exact (ha.symm.trans (h.trans hb))

theorem eq_82 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] :=
    seed P.g P.inverse (sourceWord 6) [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2] [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] false 29 (by decide) (P.relation 6)
  have ha : readWord P.g [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2] := (context P.g [1, 0] [0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [1, 0, 2, 2, 0] [1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [1, 0, 2, 2, 0, 2] [0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2] [2, 1] [] (eq_1 P)).trans ((context P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] [0, 1, 1, 1, 0, 2, 2, 2] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [1, 0, 2, 2, 2] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0, 2, 2, 2] [2, 1] [] (eq_1 P))))))
  have hb : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0, 1, 0, 2, 2, 0] := (context P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] [0, 1, 1, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] [1, 0, 2, 0, 1, 0, 1, 1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 0, 1, 0, 1, 1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] [2, 0, 1, 0, 1, 1, 0] [0, 0] [] (eq_0 P)).trans (context P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0, 1, 0] [0] [1, 1] [2, 2] (eq_5 P))))))
  exact (ha.symm.trans (h.trans hb))

theorem eq_101 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] := by
  have h : readWord P.g [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0] = readWord P.g [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] :=
    seed P.g P.inverse (sourceWord 6) [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0] [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] false 9 (by decide) (P.relation 6)
  have ha : readWord P.g [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0] = readWord P.g [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] := context P.g [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] [0] [1, 1] [2, 2] (eq_5 P)
  have hb : readWord P.g [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] := (context P.g [0, 1, 0] [0, 1, 1, 1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 1, 0, 2, 2, 0] [1, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [0, 1, 0, 2, 2, 0, 2] [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] [2, 1] [] (eq_1 P)))
  exact (ha.symm.trans (h.trans hb))

theorem eq_106 (P : Inputs G) :
    readWord P.g [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] = readWord P.g [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] :=
    seed P.g P.inverse (sourceWord 5) [1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] true 15 (by decide) (P.relation 5)
  have ha : readWord P.g [1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := (context P.g [] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 2, 0, 2, 0, 1, 0] [0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0] [0, 1, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [1, 0] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0] [2, 1] [] (eq_1 P))))))))
  have hb : readWord P.g [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_107 (P : Inputs G) :
    readWord P.g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] = readWord P.g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] :=
    seed P.g P.inverse (sourceWord 5) [0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] true 14 (by decide) (P.relation 5)
  have ha : readWord P.g [0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := (context P.g [0] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0] [0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] [2, 1] [] (eq_1 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0] [0, 1, 1, 1] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [1] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [] [2, 1] [] (eq_1 P))))))))
  have hb : readWord P.g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_110 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] :=
    seed P.g P.inverse (sourceWord 5) [1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] true 11 (by decide) (P.relation 5)
  have ha : readWord P.g [1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := (context P.g [] [1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2] [0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [2, 0] [0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 0, 2, 2, 0, 2, 0, 1, 0] [0, 1, 1, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans ((context P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0] [2, 1] [] (eq_1 P)).trans ((context P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [0, 2, 0, 1, 0, 1, 1, 0] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0] [0] [1, 1] [2, 2] (eq_5 P))))))))
  have hb : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_119 (P : Inputs G) :
    readWord P.g [2, 2, 2] = readWord P.g [1] := by
  have h : readWord P.g [2, 2, 2] = readWord P.g [1] :=
    overlap P.g [1] [1] [2] [2, 2] [] (eq_5 P) (eq_2 P)
  have ha : readWord P.g [2, 2, 2] = readWord P.g [2, 2, 2] := rfl
  have hb : readWord P.g [1] = readWord P.g [1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_134 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := by
  have h : readWord P.g [0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] :=
    eq_32 P
  have ha : readWord P.g [0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] := (context P.g [0, 2, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0] [2, 2, 2] [1] (eq_119 P)).trans (context P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] [0, 2, 2, 0] [2, 2, 2] [1] (eq_119 P))
  have hb : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_137 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0] :=
    eq_76 P
  have ha : readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := context P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [0, 2, 2, 0, 2] [2, 2, 2] [1] (eq_119 P)
  have hb : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] [0] [2, 2, 2] [1] (eq_119 P)
  exact (ha.symm.trans (h.trans hb))

theorem eq_144 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0, 1, 0, 2, 2, 0] :=
    eq_82 P
  have ha : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := context P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [] [2, 2, 2] [1] (eq_119 P)
  have hb : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := (context P.g [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 2, 0] [2, 2, 2] [1] (eq_119 P)).trans ((context P.g [0, 1, 0, 2, 0, 1, 0, 2] [0, 2, 2, 0] [0, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 0] (eq_6 P)).trans ((context P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] [2, 2, 0] [0, 0] [] (eq_0 P)).trans (context P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [0] [2, 2, 2] [1] (eq_119 P))))
  exact (ha.symm.trans (h.trans hb))

theorem eq_155 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] :=
    eq_101 P
  have ha : readWord P.g [1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] := (context P.g [1, 0] [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [2, 2, 2] [1] (eq_119 P)).trans ((context P.g [1, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [1, 2] [] (eq_2 P)).trans ((context P.g [1] [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [0, 0] [] (eq_0 P)).trans (context P.g [] [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [1, 2] [] (eq_2 P))))
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := (context P.g [0, 1, 0, 2, 2, 0, 2, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 2] [2, 2, 2] [1] (eq_119 P)).trans (context P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] [] [2, 2, 2] [1] (eq_119 P))
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_161 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] :=
    eq_106 P
  have ha : readWord P.g [0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := (context P.g [0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [2, 2, 2] [1] (eq_119 P)).trans (context P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [2, 2, 2] [1] (eq_119 P))
  have hb : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_162 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] :=
    eq_107 P
  have ha : readWord P.g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := (context P.g [] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [2, 2, 2] [1] (eq_119 P)).trans (context P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [2, 2, 2] [1] (eq_119 P))
  have hb : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_168 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] :=
    eq_110 P
  have ha : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] := (context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2] [2, 2, 2] [1] (eq_119 P)).trans (context P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [] [2, 2, 2] [1] (eq_119 P))
  have hb : readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_175 (P : Inputs G) :
    readWord P.g [0, 2, 0, 2, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 1] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 1] :=
    overlap P.g [1, 0, 1, 0, 1] [0] [0] [0, 2, 0, 2, 0, 2] [] (eq_7 P) (eq_0 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 2, 0] = readWord P.g [0, 2, 0, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 1] = readWord P.g [1, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_176 (P : Inputs G) :
    readWord P.g [2, 0, 2, 0, 2, 0, 2] = readWord P.g [0, 1, 0, 1, 0] := by
  have h : readWord P.g [0, 1, 0, 1, 0] = readWord P.g [2, 0, 2, 0, 2, 0, 2] :=
    overlap P.g [2] [1] [0, 1, 0, 1, 0] [] [0, 2, 0, 2, 0, 2] (eq_1 P) (eq_7 P)
  have ha : readWord P.g [0, 1, 0, 1, 0] = readWord P.g [0, 1, 0, 1, 0] := rfl
  have hb : readWord P.g [2, 0, 2, 0, 2, 0, 2] = readWord P.g [2, 0, 2, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_177 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 2, 0, 2] = readWord P.g [2, 2, 0, 1, 0, 1, 0] := by
  have h : readWord P.g [1, 0, 2, 0, 2, 0, 2] = readWord P.g [2, 2, 0, 1, 0, 1, 0] :=
    overlap P.g [2, 2] [2] [0, 2, 0, 2, 0, 2] [1] [0, 1, 0, 1, 0] (eq_119 P) (eq_176 P)
  have ha : readWord P.g [1, 0, 2, 0, 2, 0, 2] = readWord P.g [1, 0, 2, 0, 2, 0, 2] := rfl
  have hb : readWord P.g [2, 2, 0, 1, 0, 1, 0] = readWord P.g [2, 2, 0, 1, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_178 (P : Inputs G) :
    readWord P.g [0, 1, 0, 1, 0, 2, 2] = readWord P.g [2, 0, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [0, 1, 0, 1, 0, 2, 2] = readWord P.g [2, 0, 2, 0, 2, 0, 1] :=
    overlap P.g [2, 0, 2, 0, 2, 0] [2] [2, 2] [0, 1, 0, 1, 0] [1] (eq_176 P) (eq_119 P)
  have ha : readWord P.g [0, 1, 0, 1, 0, 2, 2] = readWord P.g [0, 1, 0, 1, 0, 2, 2] := rfl
  have hb : readWord P.g [2, 0, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_179 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0] = readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0] :=
    overlap P.g [1, 0, 1, 0] [1, 0] [2, 0, 2, 0, 2] [0, 2, 0, 2, 0, 2] [2, 2, 0, 1, 0, 1, 0] (eq_7 P) (eq_177 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_180 (P : Inputs G) :
    readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1] :=
    overlap P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1] [0] [0] [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2] [] (eq_179 P) (eq_0 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_182 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] :=
    overlap P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [2] [1] [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] [] (eq_11 P) (eq_1 P)
  have ha : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := context P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] [] [1, 1] [2, 2] (eq_5 P)
  have hb : readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_184 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 1] := by
  have h : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 1] :=
    overlap P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] [2] [2, 2] [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] [1] (eq_12 P) (eq_119 P)
  have ha : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2] := rfl
  have hb : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 1] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_188 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] :=
    overlap P.g [2, 2] [2] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [1] [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] (eq_119 P) (eq_182 P)
  have ha : readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := rfl
  have hb : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_189 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] :=
    overlap P.g [2] [1] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] [] [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] (eq_1 P) (eq_144 P)
  have ha : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_190 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] :=
    overlap P.g [0] [0] [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] [] [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] (eq_0 P) (eq_189 P)
  have ha : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_191 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] :=
    overlap P.g [1] [2] [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] [] [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] (eq_2 P) (eq_190 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_192 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [1] [2] [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [] (eq_190 P) (eq_2 P)
  have ha : readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] := rfl
  have hb : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_193 (P : Inputs G) :
    readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] :=
    overlap P.g [2] [2, 2] [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] [1] [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] (eq_119 P) (eq_190 P)
  have ha : readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_194 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] :=
    overlap P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] [0] [0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] [] (eq_134 P) (eq_0 P)
  have ha : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_195 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] :=
    overlap P.g [0] [0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] [] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] (eq_0 P) (eq_194 P)
  have ha : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_196 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] := by
  have h : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] :=
    overlap P.g [1] [2] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] [] [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] (eq_2 P) (eq_195 P)
  have ha : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_197 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] := by
  have h : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] :=
    overlap P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] [2] [1] [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] [] (eq_195 P) (eq_1 P)
  have ha : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_198 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] :=
    overlap P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] [2, 2] [2] [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] [1] (eq_195 P) (eq_119 P)
  have ha : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] := rfl
  have hb : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_199 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := by
  have h : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] :=
    overlap P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] [0] [0] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2] [] (eq_196 P) (eq_0 P)
  have ha : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_200 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] :=
    overlap P.g [0] [0] [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [] [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] (eq_0 P) (eq_199 P)
  have ha : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_201 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] := by
  have h : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] :=
    overlap P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] [1] [2] [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [] (eq_200 P) (eq_2 P)
  have ha : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_202 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] :=
    overlap P.g [2] [1] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] [] [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] (eq_1 P) (eq_201 P)
  have ha : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  have hb : readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] = readWord P.g [2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_204 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := by
  have h : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] :=
    overlap P.g [0] [1, 0, 1, 0, 2, 2] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [2, 0, 2, 0, 2, 0, 1] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] (eq_178 P) (eq_188 P)
  have ha : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := rfl
  have hb : readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_205 (P : Inputs G) :
    readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := by
  have h : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] :=
    overlap P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [0] [0] [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [] (eq_204 P) (eq_0 P)
  have ha : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  have hb : readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_206 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] :=
    overlap P.g [1] [2] [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [] [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] (eq_2 P) (eq_205 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  have hb : readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_207 (P : Inputs G) :
    readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] :=
    overlap P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] [2] [1] [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [] (eq_206 P) (eq_1 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] := rfl
  have hb : readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_208 (P : Inputs G) :
    readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] :=
    overlap P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] [2, 2] [2] [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [1] (eq_206 P) (eq_119 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  have hb : readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_209 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] :=
    overlap P.g [0] [0] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] [] [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] (eq_0 P) (eq_207 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_210 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] :=
    overlap P.g [0] [0] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [] [1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] (eq_0 P) (eq_208 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_211 (P : Inputs G) :
    readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] :=
    overlap P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] [2] [1] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1] [] (eq_209 P) (eq_1 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] := context P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [] [1, 1] [2, 2] (eq_5 P)
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_212 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] := by
  have h : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] :=
    overlap P.g [1] [2] [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] [] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] (eq_2 P) (eq_211 P)
  have ha : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_214 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] :=
    overlap P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [2] [2, 2] [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [1] (eq_192 P) (eq_119 P)
  have ha : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_215 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [1, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] := by
  have h : readWord P.g [1, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] :=
    overlap P.g [2, 2] [2] [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] [1] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] (eq_119 P) (eq_202 P)
  have ha : readWord P.g [1, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] := rfl
  have hb : readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_216 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1] := by
  have h : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1] :=
    overlap P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [2] [2, 2] [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] [1] (eq_201 P) (eq_119 P)
  have ha : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2] := rfl
  have hb : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_217 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] := by
  have h : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] = readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] :=
    overlap P.g [0, 1, 0] [1, 0, 2, 2] [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] [2, 0, 2, 0, 2, 0, 1] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] (eq_178 P) (eq_13 P)
  have ha : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] = readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_218 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] :=
    overlap P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] [2, 0, 2] [0, 2, 0, 2] [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1] [0, 1, 0, 1, 0] (eq_11 P) (eq_176 P)
  have ha : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] := rfl
  have hb : readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_219 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 1, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] :=
    overlap P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] [0, 1, 0] [1, 0, 1] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] [2, 0, 2, 0, 2, 0] (eq_9 P) (eq_6 P)
  have ha : readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 1, 0, 1] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := context P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0, 1] [2, 1] [] (eq_1 P)
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_220 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] :=
    overlap P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] [0] [0] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] [] (eq_219 P) (eq_0 P)
  have ha : readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_221 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] [2] [1] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [] (eq_220 P) (eq_1 P)
  have ha : readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_222 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [1] [2] [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] [] [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] (eq_2 P) (eq_221 P)
  have ha : readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_223 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [2] [2, 2] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] [1] [0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] (eq_119 P) (eq_221 P)
  have ha : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_225 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [2] [1] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] [] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] (eq_1 P) (eq_223 P)
  have ha : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_226 (P : Inputs G) :
    readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2] :=
    overlap P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2] [0] [0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1] [] (eq_225 P) (eq_0 P)
  have ha : readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0] := rfl
  have hb : readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_227 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] :=
    overlap P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [1] [1] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0] [2, 2] (eq_223 P) (eq_5 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_229 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] := by
  have h : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] :=
    overlap P.g [1] [2] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [] [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] (eq_2 P) (eq_218 P)
  have ha : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] := rfl
  have hb : readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_230 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] :=
    overlap P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] [0] [0] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] [] (eq_229 P) (eq_0 P)
  have ha : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_231 (P : Inputs G) :
    readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] [1] [2] [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0] [] (eq_217 P) (eq_2 P)
  have ha : readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_232 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] :=
    overlap P.g [0] [0] [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [] [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] (eq_0 P) (eq_230 P)
  have ha : readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_233 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [1] [2] [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] [] [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] (eq_2 P) (eq_231 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_234 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := by
  have h : readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] :=
    overlap P.g [2] [1] [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] (eq_1 P) (eq_232 P)
  have ha : readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_235 (P : Inputs G) :
    readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] :=
    overlap P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] [0] [0] [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] [] (eq_233 P) (eq_0 P)
  have ha : readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_237 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] = readWord P.g [2, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [2, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] :=
    overlap P.g [1] [1] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] [2, 2] [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] (eq_5 P) (eq_212 P)
  have ha : readWord P.g [2, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_238 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := by
  have h : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] :=
    overlap P.g [1] [1] [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [2, 2] [0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] (eq_5 P) (eq_206 P)
  have ha : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_239 (P : Inputs G) :
    readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0] :=
    overlap P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] [0, 1, 0, 1] [0, 1] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] [2, 0, 2, 0, 2, 0] (eq_197 P) (eq_6 P)
  have ha : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_241 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] :=
    overlap P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] [1] [2] [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0] [] (eq_155 P) (eq_2 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_242 (P : Inputs G) :
    readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] := by
  have h : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] :=
    overlap P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] [0] [0] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1] [] (eq_239 P) (eq_0 P)
  have ha : readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_245 (P : Inputs G) :
    readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] :=
    overlap P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] [0] [0] [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2] [] (eq_241 P) (eq_0 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_246 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] :=
    overlap P.g [1] [2] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] [] [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] (eq_2 P) (eq_242 P)
  have ha : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_247 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] [2] [1] [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0] [] (eq_246 P) (eq_1 P)
  have ha : readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_248 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := by
  have h : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] :=
    overlap P.g [0] [0] [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] [] [1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] (eq_0 P) (eq_247 P)
  have ha : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_249 (P : Inputs G) :
    readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := by
  have h : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] :=
    overlap P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [0] [0] [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] [] (eq_248 P) (eq_0 P)
  have ha : readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_257 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := by
  have h : readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] :=
    overlap P.g [2, 2] [2] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] [1] [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] (eq_119 P) (eq_234 P)
  have ha : readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] := rfl
  have hb : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_259 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := by
  have h : readWord P.g [2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] :=
    overlap P.g [1] [1] [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] [2, 2] [0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] (eq_5 P) (eq_233 P)
  have ha : readWord P.g [2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] = readWord P.g [2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] = readWord P.g [1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_261 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := by
  have h : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] :=
    overlap P.g [1] [1] [0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] [2, 2] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] (eq_5 P) (eq_229 P)
  have ha : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_262 (P : Inputs G) :
    readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] :=
    overlap P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2] [0, 1, 0, 1] [0, 1] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [2, 0, 2, 0, 2, 0] (eq_210 P) (eq_6 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_263 (P : Inputs G) :
    readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] := by
  have h : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] :=
    overlap P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] [0] [0] [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1] [] (eq_262 P) (eq_0 P)
  have ha : readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_264 (P : Inputs G) :
    readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] :=
    overlap P.g [1] [2] [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] [] [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] (eq_2 P) (eq_263 P)
  have ha : readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] = readWord P.g [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_270 (P : Inputs G) :
    readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := by
  have h : readWord P.g [1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] :=
    overlap P.g [0, 2, 0, 2] [0, 2, 0] [1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 1] [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] (eq_175 P) (eq_197 P)
  have ha : readWord P.g [1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] := (context P.g [1, 0, 1, 0] [0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] [1, 1] [2, 2] (eq_5 P)).trans (context P.g [] [] [1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] (eq_257 P))
  have hb : readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] = readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_274 (P : Inputs G) :
    readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] = readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := by
  have h : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] = readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] :=
    overlap P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] [2] [1] [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0] [] (eq_270 P) (eq_1 P)
  have ha : readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] = readWord P.g [2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb))

theorem eq_277 (P : Inputs G) :
    readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] :=
    overlap P.g [1] [2] [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [] [0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] (eq_2 P) (eq_274 P)
  have ha : readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] = readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] := rfl
  exact (ha.symm.trans (h.trans hb)).symm

theorem eq_286 (P : Inputs G) :
    readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := by
  have h : readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] = readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] :=
    overlap P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] [0] [0] [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1] [] (eq_277 P) (eq_0 P)
  have ha : readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] = readWord P.g [2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0] := rfl
  have hb : readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] = readWord P.g [1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1] := rfl
  exact (ha.symm.trans (h.trans hb))

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Replay
