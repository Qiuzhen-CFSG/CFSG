module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.M11
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.M12
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuOne.M24

/-!
# The Mathieu rank-one upper bounds in E.1.14(4)

For M₁₁, M₁₂ and M₂₄, actual solvable subgroups through a Sylow two-subgroup
generate the model. E.1.13 gives each local rank-one bound, and the corrected
E-member inheritance theorem supplies ambient E-generation. The full M₁₂
outer extension has its own proved solvable generating pair. M₁₁ and M₂₄
have no outer automorphisms, and self-centralization of F*(G) excludes further
ambient extensions. Every model comparison is an actual multiplicative equivalence.

The conclusion holds for every finite group with one of these generalized
Fitting subgroups; the source SQTK, simplicity and G = LT hypotheses are
therefore sufficient without further premises. Positivity and the equality
of the generation parameter with one remain with ValuesSporadic's assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
E.1.14(4), printed p.214, citing Asc82a Lemma 4.9.
-/

public section
open Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The M₁₁, M₁₂ and M₂₄ upper-generation cases of E.1.14(4), including
all possible ambient extensions and with no undischarged local premises. -/
theorem isEGenerated_one_of_mathieu_socle
    (h : Nonempty (generalizedFitting G ≃* M11) ∨
      Nonempty (generalizedFitting G ≃* M12) ∨
      Nonempty (generalizedFitting G ≃* M24)) : IsEGenerated 1 G := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    exact MathieuOne.isEGenerated_of_m11_socle e
  · obtain ⟨e⟩ := h
    exact MathieuOne.isEGenerated_of_m12_socle e
  · obtain ⟨e⟩ := h
    exact MathieuOne.isEGenerated_of_m24_socle e
end CFSG.Quasithin.ChapterE
