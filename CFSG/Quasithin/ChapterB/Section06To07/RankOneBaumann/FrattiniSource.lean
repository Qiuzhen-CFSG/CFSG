module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Frattini
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.TwoConjugates
public import Theory.GroupTheory.FrattiniOddIndexTwo

/-!
# The actual minimal-parabolic Frattini condition

B.6.8 identifies the odd image of the minimal-parabolic core in H/O₂(H)
with its Frattini subgroup. Odd-order elements lie in the two-residual.
The coprime-index Frattini theorem therefore restricts this image into the
Frattini subgroup of the actual residual image. Removing only the O₂
kernel yields B.2.18(b) on the original group, uniformly in both the
solvable and nonsolvable cases. Reducedness and movement then put the
literal action centralizer inside that same core.
Source: Aschbacher–Smith B.6.8(5),(7) and B.6.10, printed pp.114–117.
-/

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G : Type*} [Group G] [Finite G]

private theorem odd_frattini_le_residual {X : Type*} [Group X] [Finite X]
    (ho : Odd (Nat.card (frattini X))) : frattini X ≤ pResidual 2 X := by
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  have hd := orderOf_dvd_natCard (⟨x,hx⟩ : frattini X)
  have hc : Nat.Coprime 2 (orderOf (⟨x,hx⟩ : frattini X)) :=
    (Nat.coprime_two_left.mpr ho).of_dvd_right hd
  rwa [← Subgroup.orderOf_coe] at hc

public theorem residual_core_le_coreFrattini
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) :
    pResidual 2 G ⊓ minimalParabolicCore T hP ≤
      BaumannArgument.coreFrattini (pResidual 2 G) := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let X := G ⧸ pCore 2 G
  let L := pResidual 2 X
  have ho : Odd (Nat.card (frattini X)) := by
    rw [← coreImage_frattini T hP]
    exact minimalParabolic_coreImage_odd T hP
  have hsub := FrattiniCoprime.frattini_subgroupOf_le_of_odd_two_quotient L
    (odd_frattini_le_residual ho) ho (isPGroup_quotient_pResidual 2)
  apply residual_intersection_le_coreFrattini_of_image
  rw [coreImage_frattini T hP,
    map_pResidual_of_surjective 2 π (QuotientGroup.mk'_surjective _)]
  intro x hx
  exact mem_map.mpr ⟨⟨x,odd_frattini_le_residual ho hx⟩,hsub hx,rfl⟩

public theorem reduced_centralizer_le_core
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    centralizer (U : Set G) ≤ minimalParabolicCore T hP := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hk : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [QuotientGroup.ker_mk'] at he
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ C
    rw [he]
    exact le_top
  have hh := (minimalParabolic_reduced_image T hP q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hk).1
  simpa only [q,QuotientGroup.ker_mk'] using hh

public theorem residual_centralizer_le_coreFrattini
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    pResidual 2 G ⊓ centralizer (U : Set G) ≤
      BaumannArgument.coreFrattini (pResidual 2 G) :=
  (inf_le_inf_left _ (reduced_centralizer_le_core T hP U hU hJ)).trans
    (residual_core_le_coreFrattini T hP)
end CFSG.Quasithin.ChapterB.RankOneBaumann
