module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.Alternatives
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
/-!
# The source persistence alternative on the original chosen setup

The original non-Bender component either persists in N_G(E), or is contained
in an actual ordinary M₁₁ component. This is the precise earlier-source
alternative needed to attach the independent small-component exclusion in
2.5.18. It assumes neither that exclusion nor persistence itself.
Source: Aschbacher–Smith 2.5.6 and 2.5.18, printed pp.554,559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
    {H K M E : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.component_or_mathieu_in_normalizer
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬ClassificationModels.IsBenderModel K)
    (hE : E≠⊥) (hEC : E≤((S:Subgroup H).map H.subtype)⊓centralizer (K:Set G))
    (hSE : (S:Subgroup H).map H.subtype≤normalizer (E:Set G)) :
    IsComponentIn K (normalizer (E:Set G)) ∨
      ∃ C : Subgroup G, IsComponentIn C (normalizer (E:Set G)) ∧ K≤C ∧
        Nonempty (C≃*Sporadic.Mathieu.M11) :=
  NonEnlargement.component_or_mathieu_containing hG c.T c.maximal c.sylow_le c.unique
    hempty (MathieuSourceSetup.sourceTuple c) ⟨c.component_le,c.component⟩ hgen hb hE hEC hSE
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
