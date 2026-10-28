module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.GridCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.GridOrbits
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.Lifting

/-!
# The six-candidate local orbit under quaternion normality

Relative quaternion normality preserves the two quaternion factors of Q.
Their nonidentity central quotient points give equivariant coordinates on
the nine singular cosets. The actual H/Q ≃ S₃ action has orbits of lengths
three and six on this grid, lifting to H-orbits of lengths six and twelve
on the noncentral involutions of Q.

Since |H| = 192, orbit--stabilizer identifies the literal `countCandidates`
set with the six-element orbit: its common centralizers have order 32,
whereas those on the other orbit have order 16. Both its cardinality and
its transitivity follow from the original hypotheses and relative normality,
discharging the two local premises of the separate ambient fusion count.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.2–2.3, especially 2.3(2)(b).
-/

namespace CFSG.Quasithin.Extraspecial32.Hypotheses

open FusionCount.LocalOrbit

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Relative quaternion normality gives the three- and six-point orbit profile
for the literal action on the nonzero singular central cosets of Q. -/
public theorem localOrbit_cosetProfile_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) : CosetProfile z := by
  obtain ⟨m⟩ := h.localOrbit_gridModel_of_quaternion_normal hn
  exact cosetProfile_of_gridModel h m

/-- Exactly six noncentral core involutions have common centralizer with z
of order at least 32. -/
public theorem countCandidates_card_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) : (FusionCount.countCandidates z).ncard = 6 :=
  countCandidates_card_of_cosetProfile h (h.localOrbit_cosetProfile_of_quaternion_normal hn)

/-- The six candidates form one orbit under conjugation by C_G(z). -/
public theorem countCandidates_transitive_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) :
    ∀ x ∈ FusionCount.countCandidates z, ∀ y ∈ FusionCount.countCandidates z,
      ∃ a ∈ Centralizer z, a * x * a⁻¹ = y :=
  countCandidates_transitive_of_cosetProfile h
    (h.localOrbit_cosetProfile_of_quaternion_normal hn)

end CFSG.Quasithin.Extraspecial32.Hypotheses
