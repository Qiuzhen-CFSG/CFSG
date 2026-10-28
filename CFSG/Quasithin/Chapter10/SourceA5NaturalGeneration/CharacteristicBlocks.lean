module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.FixedCenter
/-!
# One block from the same characteristic pair in two overgroups

After the natural fixed centers have vanished, neither local group can
centralize the nontrivial first member of C.1.26's characteristic pair.
If neither original component is a block, both local groups normalize the
nontrivial second member. Original maximal two-local uniqueness contradicts
H* escaping M. Thus at least one block alternative holds, with block status
retained in each component's actual local ambient group.

The local C.1.26 applications remain explicit inputs; this theorem discharges
the center and uniqueness alternatives, independently of torus-axis alignment.
Source: Aschbacher–Smith10.2.3(4), printed p.746.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- C.1.26's alternatives on the same characteristic pair force an actual
block in one of the two original overgroups. -/
theorem source_hstar_characteristic_alternatives_force_block {H K : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZL : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hZH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥)
    (C₁ C₂ : Subgroup G) (hC₁ : C₁ ≠ ⊥) (hC₂ : C₂ ≠ ⊥)
    (hC₁Z : C₁ ≤ omegaOneCenterAmbient (T : Subgroup G))
    (hp : IsPGroup 2 C₂) (hT : (T : Subgroup G) ≤ normalizer (C₂ : Set G))
    (hL : ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨ C₁ ≤ centralizer (localOrbit T L : Set G) ∨
      localOrbit T L ≤ normalizer (C₂ : Set G))
    (hK : ChapterC.IsBlock (K.subgroupOf H) ∨ C₁ ≤ centralizer (H : Set G) ∨
      H ≤ normalizer (C₂ : Set G)) : ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨ ChapterC.IsBlock (K.subgroupOf H) := by
  rcases hL with hb | hc | hnL
  · exact Or.inl hb
  · exact (hC₁ (bot_unique ((le_inf hC₁Z hc).trans hZL.le))).elim
  rcases hK with hb | hc | hnH
  · exact Or.inr hb
  · exact (hC₁ (bot_unique ((le_inf hC₁Z hc).trans hZH.le))).elim
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact (hH.1.2 (hnH.trans (normalizer_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness hu).2.2 hp hC₂ (sup_le hnL hT)))).elim
end CFSG.Quasithin.Chapter10
