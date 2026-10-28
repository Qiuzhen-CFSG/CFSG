module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import Theory.GroupTheory.PCoreQuotientJoinAction

/-!
# Generation from the actual chief-factor action

For a two-group U normalizing L, the literal conjugation action of LU on
L/O₂(L) has kernel O₂(LU) when the section is centerless. Its proved
quotient isomorphism transfers generation from the action image to LU.
This supplies the local-normalizer application in E.1.11 without an
unrelated abstract automorphism group or an assumed faithful action.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.7 and E.1.11--13, pp.210--214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The literal action on `L/O₂(L)` supplies generation for `LU`. The action
kernel is proved to be `O₂(LU)`, not assumed to vanish. This is the local
normalizer application needed for a nonabelian chief factor in E.1.11. -/
theorem isEGenerated_join_of_pCoreJoinAction {i : ℕ} (L U : Subgroup G)
    (hUL : U ≤ normalizer (L : Set G)) (hU : IsPGroup 2 U)
    (hc : center (L ⧸ pCore 2 L) = ⊥)
    (hgen : IsEGenerated i (pCoreJoinAction 2 hUL).range) :
    IsEGenerated i (L ⊔ U : Subgroup G) := by
  have hquot := hgen.map_equiv (pCoreJoinQuotientEquivRange 2 hUL hU hc).symm
  exact IsEGenerated.of_normal_two_subgroup (pCore 2 (L ⊔ U : Subgroup G))
    pCore_isPGroup hquot


end CFSG.Quasithin.ChapterE
