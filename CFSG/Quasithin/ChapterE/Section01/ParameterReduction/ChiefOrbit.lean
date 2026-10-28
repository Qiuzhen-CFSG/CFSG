module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalGeneration

/-!
# Assembly of the nonabelian chief-factor reduction

For a chief two-residual, local generation of each component normalizer reduces
generation of G to two containments: the local E-family subgroup and the local
weak-closure normalizer. Components generate the chief subgroup, and the Sylow
two-subgroup supplements the two-residual. This gives the conditional assembly
below. Its two explicit branch premises still require the orbit-diagonal and
hyperplane-diagonal proofs; this module does not yet prove the chief case of
E.1.11 from only the local action hypotheses.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed pp.212--214.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- Assembly of the two component branches of E.1.11. The two branch premises
are explicit proof obligations, not consequences of chief minimality alone.
The source theorem also assumes a positive rank and trivial ambient two-core;
those hypotheses are consumed by the separate branch proofs. -/
theorem isEGenerated_of_component_branches {n : ℕ} (T : Sylow 2 G)
    (hX : ChiefFactor.IsChief (pResidual 2 G) ⊥)
    (hna : ¬ IsMulCommutative (pResidual 2 G))
    (hgen : ∀ J : Subgroup G, IsComponentIn J (pResidual 2 G) →
      IsEGenerated n (pCoreJoinAction 2
        (show stabilizer T J ≤ normalizer J from inf_le_right)).range)
    (hmembers : ∀ (Ω : Set (Subgroup G)), IsElementaryFamily Ω →
      ∀ J : Subgroup G, IsComponentIn J (pResidual 2 G) →
        localNormalizer T J Ω ≤ generationTarget n T Ω →
        localEFamily n T J Ω ≤ generationTarget n T Ω)
    (hnormalizers : ∀ (Ω : Set (Subgroup G)), IsElementaryFamily Ω →
      ∀ J : Subgroup G, IsComponentIn J (pResidual 2 G) →
        localNormalizer T J Ω ≤ generationTarget n T Ω) :
    IsEGenerated n G := by
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  have hTM : (T : Subgroup G) ≤ generationTarget n T Ω :=
    (sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right
  have hXM : pResidual 2 G ≤ generationTarget n T Ω :=
    hX.le_of_components_le hna _ (fun J hJ =>
      component_le_of_local_branches T hX hna hJ hΩ (hgen J hJ) hTM
        (hmembers Ω hΩ J hJ (hnormalizers Ω hΩ J hJ)) (hnormalizers Ω hΩ J hJ))
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top T]
  exact sup_le hXM hTM

end CFSG.Quasithin.ChapterE.ChiefOrbit
