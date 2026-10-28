module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.AlphaSource
public import CFSG.Quasithin.Chapter3.Section01.E23Input
/-!
# Exact alpha geometry on the original qrc omega orbit

The original qrc hypotheses construct the intrinsic minimal parabolic and
reduced orbit U=⟨Ω₁Z(T)^H⟩. Apply the complete source classification and
alpha theorem to this very subgroup and the prescribed intrinsic Sylow.
Both the moved-alpha and residual orbit identities are obtained with no
coordinate, earlier-classification or geometric hypothesis.
Source: Aschbacher–Smith E.2.3 and3.1.7, pp.216–217 and575–576.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.sylowOmega_alpha_and_orbit_span
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let S := T.subtype h.right_mem.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    ChapterB.thompsonAlpha (S : Subgroup H) =
      ((⁅U,pResidual 2 H⁆ : Subgroup H) ⊓
        centralizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)) ⊔
      (ChapterB.thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) ∧
    conjugateSpanBy (ChapterB.thompsonAlpha (S : Subgroup H)) (pResidual 2 H) =
      (⁅U,pResidual 2 H⁆ : Subgroup H) ⊔
        (ChapterB.thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)) := by
  obtain ⟨hsq,_,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  exact ChapterE.ThompsonAction.source_alpha_and_orbit_span hsq _ hp _ hU hj
end CFSG.Quasithin.Chapter3
