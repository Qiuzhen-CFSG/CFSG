module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels.Reduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels.MathieuEleven

/-!
# The L₃(3) and M₁₁ exclusions in the contrary Sylow configuration

The reduction compares the actual Sylow-induced complement automizer in
L/O₂(L) with Aut_T(P), transports its order through model isomorphisms, and
retains both SL₃ and PSL₃ until their proved comparison. The concrete model
calculations give either a reducible pair or an induced automizer of order
divisible by sixteen. The first contradicts the intrinsic irreducibility;
the second contradicts the original D₈ automizer, whose order is eight.

The two exclusions below discharge both fixed-carrier restrictions. They
apply to the normal component supplied by the embedding theorem using only
its containment in H, relative normality, and X ≤ L; no further SQTK or
quasisimplicity premise is needed for this step. Final embedding and residual
assembly remains in the parent module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.509–511 and p.1164.
-/

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels

open Chapter1 Chapter1.XiEmbedding

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual D₈ complement automizer excludes both source covers of L₃(3).
The PSL₃(3) Sylow-pair restriction is proved by the concrete model calculation. -/
public theorem not_linearThreeModel
    {U X P H L : Subgroup G} (h : LocalInput 3 U X P H)
    (hU : IsSylowIn 2 U H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hXL : X ≤ L) (hD : Nonempty (automizer U P ≃* DihedralGroup 4)) :
    ¬ LinearThreeModel 3 (XiQuotient L) :=
  not_linearThreeModel_of_restriction linearThree_restriction h hU hLH hLn hXL hD

/-- The actual D₈ complement automizer excludes the concrete M₁₁ model.
Its permutable Sylow pairs induce automizers of order sixteen. -/
public theorem not_mathieuEleven
    {U X P H L : Subgroup G} (h : LocalInput 3 U X P H)
    (hU : IsSylowIn 2 U H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hXL : X ≤ L) (hD : Nonempty (automizer U P ≃* DihedralGroup 4)) :
    ¬ Nonempty (XiQuotient L ≃* Sporadic.Mathieu.M11) :=
  not_mathieuEleven_of_restriction mathieuEleven_restriction h hU hLH hLn hXL hD

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.SmallModels
