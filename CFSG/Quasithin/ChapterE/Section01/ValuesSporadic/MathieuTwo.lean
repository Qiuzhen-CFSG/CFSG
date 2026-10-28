module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuTwo.M23
public import CFSG.Quasithin.Defs

/-!
# E.1.14(5): the M22 and M23 upper bounds

These are the two Mathieu clauses under the exact source hypotheses:
G is finite SQTK, its generalized Fitting subgroup L is simple, G = LT,
and L is actually isomorphic to M22 or M23. The local generation proofs
include the M22 outer extension; the M23 automorphism theorem eliminates
proper faithful extensions. No local generation or rank premise remains.

Source: Aschbacher--Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, E.1.14(5), printed p.214, citing
Aschbacher, GF(2)-representations of finite groups (1982), Lemma 4.9.
-/

public section
namespace CFSG.Quasithin.ChapterE
open Subgroup Theory.GroupTheory Sporadic.Mathieu

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full M22 upper-generation clause, including the outer two-extension. -/
theorem isEGenerated_two_of_sqtk_mathieu22 {K : GroupClass.{u}}
    (_hG : IsSQTK K G) (L : Subgroup G) (hL : L = generalizedFitting G)
    [IsSimpleGroup L] (T : Sylow 2 G) (_hLT : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* M22) : IsEGenerated 2 G :=
  MathieuTwo.m22_generalizedFitting_isEGenerated L hL e T

/-- The full M23 upper-generation clause, including the ambient extension argument. -/
theorem isEGenerated_two_of_sqtk_mathieu23 {K : GroupClass.{u}}
    (_hG : IsSQTK K G) (L : Subgroup G) (hL : L = generalizedFitting G)
    [IsSimpleGroup L] (T : Sylow 2 G) (_hLT : L ⊔ (T : Subgroup G) = ⊤)
    (e : L ≃* M23) : IsEGenerated 2 G :=
  MathieuTwo.m23_generalizedFitting_isEGenerated L hL e

/-- The numerical conclusion of E.1.14(5) for either Mathieu model. -/
theorem generationParameter_le_two_of_sqtk_mathieu {K : GroupClass.{u}}
    (hG : IsSQTK K G) (L : Subgroup G) (hL : L = generalizedFitting G)
    [IsSimpleGroup L] (T : Sylow 2 G) (hLT : L ⊔ (T : Subgroup G) = ⊤)
    (he : Nonempty (L ≃* M22) ∨ Nonempty (L ≃* M23)) : generationParameter G ≤ 2 := by
  apply generationParameter_le (by decide)
  rcases he with he | he
  · obtain ⟨e⟩ := he
    exact isEGenerated_two_of_sqtk_mathieu22 hG L hL T hLT e
  · obtain ⟨e⟩ := he
    exact isEGenerated_two_of_sqtk_mathieu23 hG L hL T hLT e

end CFSG.Quasithin.ChapterE
