module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import Theory.GroupTheory.OddPrimeSectionCentralizers

/-!
# The cyclic-centralizer restriction in G.9.4

Apply the proved A.1.31(1) to the actual SQTK covering map. Its source has
three-rank at most two, although the image need not. When the image has
generalized Fitting subgroup equal to its three-core, every nontrivial
two-subgroup has cyclic centralizer in that core. The final equivalence
identifies this centralizer with the literal ambient intersection.

The degree-six normalizer proof must establish the generalized-Fitting
identity for its groups before using this restriction against the explicit
noncyclic centralizers. Source: Aschbacher--Smith, G.9.4, printed p.355,
using A.1.31(1), printed pp.27--28.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

universe u v

/-- The source-centralizer theorem applies through the literal covering
map. No rank bound on the quotient or Sylow-rank convention is substituted. -/
theorem cyclic_threeCore_centralizer
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
    {A : Subgroup G} {m : ℕ} (h : FittingHypothesis K ρ A m)
    (hF : Theory.GroupTheory.generalizedFitting G = pCore 3 G)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    IsCyclic (pCore 3 G ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := by
  obtain ⟨c⟩ := h.quotient
  let : IsCyclic ((Subgroup.centralizer (T : Set G)).subgroupOf (pCore 3 G)) :=
    Theory.GroupTheory.cyclic_primeCore_centralizer_of_surjective_rank_le_two
      (by decide : Odd 3) (c.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
      c.projection c.surjective hF T hT hne
  exact isCyclic_of_surjective
    (Theory.GroupTheory.primeCoreCentralizerEquivInf 3 T).toMonoidHom
    (Theory.GroupTheory.primeCoreCentralizerEquivInf 3 T).surjective

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
