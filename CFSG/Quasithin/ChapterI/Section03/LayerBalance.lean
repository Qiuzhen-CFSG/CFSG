module

public import Theory.GroupAction.FixedPointHom
public import Theory.GroupTheory.CComponent.TwoComponent.LayerMaps
public import Theory.GroupTheory.SylowPointwiseSection
public import Theory.GroupTheory.PStar.Defs
public import Theory.GroupTheory.PStar.FixedPoints
public import Theory.GroupTheory.PResidual.PrimeSetSubgroupMaps
public import CFSG.Quasithin.ChapterI.Section03.LayerBalance.PStarIdentification
public import FeitThompson.FinalTheorem

/-!
# Two-layer transport in fixed subgroups

Under the explicit S₂ hypothesis on actual simple sections, the two-layer
is the embedded odd residual of the two-star core. Residual functoriality
therefore turns two-star-core balance into two-layer balance, and carries
the fixed-subgroup quotient bounds to the two-layers. For a central kernel,
the proved equality of the images of the two-star cores gives equality of
their residuals; the full fixed-subgroup map need not be surjective.

For an odd invariant normal kernel, each fiber over a fixed quotient point
has odd size. The two-group actor therefore fixes a representative. The
restricted quotient map has odd kernel, whose solvability follows from the
odd order theorem, so the two-component correspondence gives equality of
the two-layers. Both intrinsic and ambient equalities use the original
quotient map and its induced action.

Source: GLS II, Theorem 5.17 and the two-layer clauses of Proposition 5.19
(`refs/KGroup/GLS2/ChapterB.tex`), with S₂ as in Definition A.2.2.
The internal specialization retains exactly the centralizer subtype needed
by the ordinary-component balance consumer.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.LayerBalance
variable {A G H : Type*} [Group A] [Group G] [Group H] [Finite G]
    [MulDistribMulAction A G] [MulDistribMulAction A H]

/-- An equivariant odd-kernel surjection carries fixed-subgroup two-layers onto
one another. No solvability assumption on the ambient group is used. -/
theorem map_fixed_twoLayer_of_surjective_odd_kernel
    (hA : IsPGroup 2 A) (f : G →* H) (hf : Function.Surjective f)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x)
    (hk : Odd (Nat.card f.ker)) :
    (twoComponentLayer (fixedPointSubgroup A G)).map (FixedPoints.mapHom f he) =
      twoComponentLayer (fixedPointSubgroup A H) := by
  have hk' : Odd (Nat.card (FixedPoints.mapHom f he).ker) :=
    Nat.coprime_two_left.mp (hk.coprime_two_left.of_dvd_right
      (FixedPoints.mapHom_ker_card_dvd f he))
  let : Group.IsSolvable (FixedPoints.mapHom f he).ker := odd_order_theorem _ hk'
  exact map_twoComponentLayer_of_surjective_odd_kernel _
    (FixedPoints.mapHom_surjective_of_coprime_kernel hA f hf he hk.not_two_dvd_nat) hk'

/-- GLS II 5.19(iii), odd-kernel two-layer clause, on the literal fixed subgroups. -/
theorem map_twoLayer_fixedPoints_odd_quotient
    (hA : IsPGroup 2 A) (N : Subgroup G) [N.Normal]
    (hN : IsInvariant A G N) (hodd : Odd (Nat.card N)) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    (twoComponentLayer (fixedPointSubgroup A G)).map (FixedPoints.quotientMap N hN) =
      twoComponentLayer (fixedPointSubgroup A (G ⧸ N)) := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  exact map_fixed_twoLayer_of_surjective_odd_kernel hA (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (fun _ _ => rfl)
    (by simpa only [QuotientGroup.ker_mk'] using hodd)

/-- The same equality inside X/N, with both subtype embeddings retained. -/
theorem map_embedded_twoLayer_fixedPoints_odd_quotient
    (hA : IsPGroup 2 A) (N : Subgroup G) [N.Normal]
    (hN : IsInvariant A G N) (hodd : Odd (Nat.card N)) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    ((twoComponentLayer (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype).map (QuotientGroup.mk' N) =
        (twoComponentLayer (fixedPointSubgroup A (G ⧸ N))).map
          (fixedPointSubgroup A (G ⧸ N)).subtype := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  rw [← map_twoLayer_fixedPoints_odd_quotient hA N hN hodd, map_map, map_map]
  rfl

end CFSG.Quasithin.ChapterI.LayerBalance

namespace CFSG.Quasithin.ChapterI.LayerBalance
variable {A G : Type*} [Group A] [Group G] [Finite G] [MulDistribMulAction A G]

/-- GLS II 5.17: the two-layer of the fixed subgroup lies in the ambient
two-layer, under the genuine S₂ hypothesis on simple sections. -/
theorem map_twoLayer_fixedPoints_le [Finite A]
    (hS : HasTwoSchreier G) (hA : IsPGroup 2 A) :
    (twoComponentLayer (fixedPointSubgroup A G)).map (fixedPointSubgroup A G).subtype ≤
      twoComponentLayer G := by
  rw [← oddResidual_twoStarCore_eq_twoLayer (hS.subgroup (fixedPointSubgroup A G)),
    ← oddResidual_twoStarCore_eq_twoLayer hS]
  exact map_embedded_piResidual_le _ _ _ _
    (PStarAction.map_twoStarCore_fixedPoint_le hA)

/-- The literal internal-centralizer bound of GLS II 5.17, for an arbitrary
two-subgroup P. This is the bound used by ordinary-component balance. -/
theorem map_twoLayer_centralizer_le
    (hS : HasTwoSchreier G) (P : Subgroup G) (hP : IsPGroup 2 P) :
    (twoComponentLayer (centralizer (P : Set G))).map (centralizer (P : Set G)).subtype ≤
      twoComponentLayer G := by
  rw [← oddResidual_twoStarCore_eq_twoLayer (hS.subgroup (centralizer (P : Set G))),
    ← oddResidual_twoStarCore_eq_twoLayer hS]
  exact map_embedded_piResidual_le _ _ _ _ (map_twoStarCore_centralizer_le P hP)

/-- GLS II 5.19(ii), the two-layer clause for an arbitrary invariant normal
kernel, with the original quotient map restricted to fixed subgroups. -/
theorem map_twoLayer_fixedPoints_quotient_le [Finite A]
    (hS : HasTwoSchreier G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    (twoComponentLayer (fixedPointSubgroup A G)).map (FixedPoints.quotientMap N hN) ≤
      twoComponentLayer (fixedPointSubgroup A (G ⧸ N)) := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  have hQ := hS.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  rw [← oddResidual_twoStarCore_eq_twoLayer (hS.subgroup (fixedPointSubgroup A G)),
    ← oddResidual_twoStarCore_eq_twoLayer (hQ.subgroup (fixedPointSubgroup A (G ⧸ N)))]
  exact map_embedded_piResidual_le _ _ _ _ (FixedPoints.map_twoStarCore_quotient_le hA N hN)

/-- The arbitrary-kernel containment inside X/N, retaining both subtype maps. -/
theorem map_embedded_twoLayer_fixedPoints_quotient_le [Finite A]
    (hS : HasTwoSchreier G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    ((twoComponentLayer (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype).map (QuotientGroup.mk' N) ≤
        (twoComponentLayer (fixedPointSubgroup A (G ⧸ N))).map
          (fixedPointSubgroup A (G ⧸ N)).subtype := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  calc
    _ = ((twoComponentLayer (fixedPointSubgroup A G)).map
        (FixedPoints.quotientMap N hN)).map (fixedPointSubgroup A (G ⧸ N)).subtype := by
      rw [map_map, map_map]
      rfl
    _ ≤ _ := map_mono (map_twoLayer_fixedPoints_quotient_le hS hA N hN)

/-- GLS II 5.19(iii), central-kernel two-layer equality. Only the two-star
cores need to map onto one another, not the full fixed subgroups. -/
theorem map_twoLayer_fixedPoints_central_quotient
    (hS : HasTwoSchreier G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N) (hc : N ≤ center G) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    (twoComponentLayer (fixedPointSubgroup A G)).map (FixedPoints.quotientMap N hN) =
      twoComponentLayer (fixedPointSubgroup A (G ⧸ N)) := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  have hQ := hS.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  rw [← oddResidual_twoStarCore_eq_twoLayer (hS.subgroup (fixedPointSubgroup A G)),
    map_embedded_piResidual, FixedPoints.map_twoStarCore_quotient_of_central hA N hN hc,
    oddResidual_twoStarCore_eq_twoLayer (hQ.subgroup (fixedPointSubgroup A (G ⧸ N)))]

/-- The central-kernel equality inside X/N, with the original quotient map. -/
theorem map_embedded_twoLayer_fixedPoints_central_quotient
    (hS : HasTwoSchreier G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N) (hc : N ≤ center G) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    ((twoComponentLayer (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype).map (QuotientGroup.mk' N) =
        (twoComponentLayer (fixedPointSubgroup A (G ⧸ N))).map
          (fixedPointSubgroup A (G ⧸ N)).subtype := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  rw [← map_twoLayer_fixedPoints_central_quotient hS hA N hN hc, map_map, map_map]
  rfl

end CFSG.Quasithin.ChapterI.LayerBalance
