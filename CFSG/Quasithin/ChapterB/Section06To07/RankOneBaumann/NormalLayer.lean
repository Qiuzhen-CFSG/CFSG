module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section06To07.OffenderGeneration
public import Theory.GroupTheory.ReducedNormal.Defs
/-!
# The residual lies in the actual normal Thompson layer

Reducedness makes the centralizer quotient core-free, and minimal-parabolic
structure descends to it. A normal subgroup containing the nontrivial
Thompson image cannot lie in its odd maximal-overgroup core. The normal
subgroup dichotomy therefore puts the original residual image in that layer.
This applies to the paired natural layer including two S₃ factors; no
perfectness or nonsolvability assumption is needed.
Source: Aschbacher–Smith B.6.8–10 and E.2.3, pp.113–117 and216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem residual_image_le_normal_thompson_layer
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal]
    (hJL : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ L) :
    (pResidual 2 G).map q ≤ L := by
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hne : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≠ ⊥ := by
    intro hh
    exact hJ ((Subgroup.map_eq_bot_iff _).mp hh |>.trans_eq hker)
  have hkerne : q.ker ≠ ⊤ := by
    intro hh
    exact hne ((Subgroup.map_eq_bot_iff _).mpr (hh ▸ le_top))
  have hbar := (minimalParabolic_reduced_image T hP q hq hcore hkerne).2
  have htwo : IsPGroup 2 ((elementaryAbelianMaxJ (T : Subgroup G)).map q) :=
    (T.isPGroup'.to_le (sSup_le fun _ hA => hA.1)).map q
  rw [map_pResidual_of_surjective 2 q hq]
  exact (minimalParabolic_normal_contains_two_supplements (T.mapSurjective hq) hbar
    hcore L ((elementaryAbelianMaxJ (T : Subgroup G)).map q) htwo hne hJL).1
end CFSG.Quasithin.ChapterB.RankOneBaumann
