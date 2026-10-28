module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import Theory.SpecificGroups.Janko4.Representations.CentralCoverDegree

/-!
# Excluding J₄ in the cubic degree window

Restrict the original faithful binary action to the actual quasisimple
component F*(G). For any of its central covers with quotient the concrete
J₄ model, the eleven-local extraspecial subgroup and the central-prime
argument force degree at least 110. This contradicts the supplied window
of at most 66, while preserving the full source hypotheses and ambient action.

This is the J₄ exclusion used in Aschbacher–Smith K.4, printed p.457
(PDF p.468), where the source cites GM02 Theorem 6.6 and Table 6.7.
`DegreeWindows.sourceExclusion_j4_of_bounded` combines this result with
the independent model geometry to discharge the full source exclusion.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory
universe u v

/-- J₄ admits no source module in the cubic degree window, including arbitrary
source central covers and ambient extensions. -/
theorem boundedSourceExclusion_j4 : BoundedSourceExclusion.{u,v} .j4 66 := by
  intro G V _ _ _ _ _ ρ h he hd
  obtain ⟨e⟩ := he
  let := h.quasisimple
  let := h.irreducible
  have hlow := Janko4.BinaryDegree.faithful_irreducible_central_cover_degree
    (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp (generalizedFitting G).subtype_injective) e
  omega

end CFSG.Quasithin.ChapterK.SporadicCatalogue
