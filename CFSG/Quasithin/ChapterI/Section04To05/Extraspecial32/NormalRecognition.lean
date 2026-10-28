module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.NormalEight
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.Assembly
public import Theory.Mathieu.M12.Recognition

/-!
# The normal-quaternion branch of I.4.6

Relative normality of the quaternion subgroups supplies the canonical
self-centralizing elementary fusion eight. If it is normal in the ambient
group, conjugation identifies the actual quotient with PSL₃(2). Otherwise,
the source geometry and eleven-point subgroup construction give a faithful
sharply five-transitive action on twelve points. Witt-design recognition then
identifies the ambient group with `Sporadic.Mathieu.M12`.

The final theorem discharges all intermediate fusion, geometry, subgroup and
action premises. It retains the elementary-eight alternative, including the
nonsplit extension in Proposition 4.12, and assumes no ambient simplicity.

Source: Aschbacher–Smith, I.4.6, printed p.417; M. Aschbacher,
“A 2-local characterization of M12”, Illinois J. Math. 47 (2003), 31–47,
Sections 2 and 4, especially Proposition 4.12.
-/

namespace CFSG.Quasithin.Extraspecial32

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The normal-quaternion branch of I.4.6. Quaternion normality is relative
to the involution centralizer; the fusion eight may or may not be normal in
the ambient group. The latter case is recognized as the actual Witt-design
automorphism group. -/
public theorem Hypotheses.recognition_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) :
    ElementaryEightAlternative G ∨ Nonempty (G ≃* Sporadic.Mathieu.M12) := by
  classical
  have d := h.fusionEightData_of_quaternion_normal hn
  by_cases hnormal : (fusionCore z).Normal
  · exact Or.inl (h.elementaryEightAlternative_of_normal_fusion d hnormal)
  · obtain ⟨a⟩ := DegreeTwelve.nonempty_action_of_nonnormal_fusion h hn d hnormal
    let := a.action
    let := a.faithful
    exact Or.inr (Sporadic.Mathieu.nonempty_mulEquiv_M12_of_sharplyMultiplyPretransitive
      a.sharp)

end CFSG.Quasithin.Extraspecial32
