module
public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.Source
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Source
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality.Envelope
public import Theory.AlgebraicGroup.Unipotent.SolvableTorusDecomposition
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.Source
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.FixedDimension
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.ToralKernel
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.RankOneComparison
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.Assembly
/-!
# Semisimple centers lie in every maximal torus

For the intersection I(T) of Borels containing a maximal torus, its unipotent
radical is normal in the ambient connected group. The proof uses generation
by those Borels, the actual semisimple rank-one quotients of singular
subtorus centralizers, their one-dimensional Borel radicals and common-torus
intersections, and the original separating-Borel theorem. These source
results prove the dimension and envelope bounds needed for ambient normality.

The proved Cartan and Borel restriction theorems then make I(T) a torus in
the semisimple case. Central elements lie in I(T), hence in the original
maximal torus. No torality, rank-one model, or radical-normality premise is
assumed. This is the common source input to triality and Ree universality.
Source: Borel, Linear Algebraic Groups, IV, §§13.15–13.17.
-/
public section
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
/-- The actual envelope fixed subgroups suffice for the normalizer argument;
no larger Borel-intersection containment is needed. -/
private theorem borel_fixed_radical_normalizes_of_envelope_bounds
    (hG : Variety.IsConnected G) {B V T U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hV : IsUnipotentRadicalOf B V)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (S : CodimensionOneSubtorus T)
    (hdim : Variety.dimension (V.pointwiseCentralizer S.1).carrierVariety ≤
      Variety.dimension ((V.pointwiseCentralizer S.1).inter U).carrierVariety + 1)
    (hother : ∀ Q : CodimensionOneSubtorus T, Q.1 ≠ S.1 →
      ¬ Group.IsSolvable (Variety.Point Q.1.centralizer.carrierVariety) →
      (unipotentEnvelope (B.pointwiseCentralizer S.1) V).pointwiseCentralizer Q.1 ≤ U) :
    V.pointwiseCentralizer S.1 ≤ U.normalizer := by
  let H := unipotentEnvelope (B.pointwiseCentralizer S.1) V
  obtain ⟨hHc,hHu,hTH,hUH,hHS,hHT⟩ :=
    unipotentEnvelope_source_geometry hG hB hV hT hTB S.2.1 S.2.2.1 hU
  have hdimH : Variety.dimension H.carrierVariety ≤ Variety.dimension U.carrierVariety + 1 := by
    apply externalTorusFixed_dimension_le H U T S.1 hT.1 hTH hHT
    · intro Q hQS
      by_cases hsolv : Group.IsSolvable (Variety.Point Q.1.centralizer.carrierVariety)
      · exact unipotent_fixed_le_intersection_radical_of_solvable hG Q.2.1 hT.1
          Q.2.2.1 hU hHu hsolv
      · exact hother Q hQS hsolv
    · rw [hHS]
      exact hdim
  have hHN := hHu.le_normalizer_of_le_of_dimension_le_add_one H U hHc hUH hdimH
  exact fun _ hx => hHN (borel_fixed_radical_le_envelope hB hV S.2.1
    (fun _ hs => hTB (S.2.2.1 hs)) hx)

/-- Once the two rank-one source clauses hold, each original torus-containing
Borel normalizes `I(T)_u`. All solvable-centralizer cases are discharged. -/
private theorem borel_le_intersection_radical_normalizer_of_envelope_bounds
    (hG : Variety.IsConnected G) {B V T U : ClosedSubgroup G}
    (hB : IsBorelSubgroup B) (hV : IsUnipotentRadicalOf B V)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hdim : ∀ S : CodimensionOneSubtorus T,
      ¬ Group.IsSolvable (Variety.Point S.1.centralizer.carrierVariety) →
      Variety.dimension (V.pointwiseCentralizer S.1).carrierVariety ≤
        Variety.dimension ((V.pointwiseCentralizer S.1).inter U).carrierVariety + 1)
    (hother : ∀ S Q : CodimensionOneSubtorus T, Q.1 ≠ S.1 →
      ¬ Group.IsSolvable (Variety.Point S.1.centralizer.carrierVariety) →
      ¬ Group.IsSolvable (Variety.Point Q.1.centralizer.carrierVariety) →
      (unipotentEnvelope (B.pointwiseCentralizer S.1) V).pointwiseCentralizer Q.1 ≤ U) : B ≤ U.normalizer := by
  have hVN : V ≤ U.normalizer := by
    obtain ⟨V',hV',hc⟩ := exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
    have hVc : _root_.IsConnected (V : Set (Variety.Point G)) :=
      (unipotent_radical_unique hV' hV) ▸ hc
    have hg := externalTorusFixed_generation V T hVc hT.1
      (fun _ ht => BorelFixedRadicalRoots.radical_normalizer hV (hTB ht))
    change V.toSubgroup ≤ U.normalizer.toSubgroup
    rw [← hg]
    apply (Subgroup.closure_le U.normalizer.toSubgroup).mpr
    intro x hx
    rcases hx with ht | hq
    · exact U.toSubgroup.le_normalizer
        (unipotent_fixed_le_intersection_radical_of_solvable hG hT.1 hT.1
          (fun _ ht => ht) hU hV.2.1
          (CartanGeometry.maximalTorus_centralizer_connected_solvable hG hT).2 ht)
    · obtain ⟨Q,hxQ⟩ := Set.mem_iUnion.mp hq
      by_cases hs : Group.IsSolvable (Variety.Point Q.1.centralizer.carrierVariety)
      · exact U.toSubgroup.le_normalizer
          (unipotent_fixed_le_intersection_radical_of_solvable hG Q.2.1 hT.1
            Q.2.2.1 hU hV.2.1 hs hxQ)
      · exact borel_fixed_radical_normalizes_of_envelope_bounds hG hB hV hT hTB hU Q
          (hdim Q hs) (fun R hRQ hns => hother Q R hRQ hs hns) hxQ
  have hTN := torus_le_intersection_radical_normalizer T U hT.1 hU
  have hdecomp := maximalTorus_unipotentRadical_decomposition_of_connected_solvable
    hB.connected hB.solvable hV hT hTB
  intro b hb
  obtain ⟨t,v,ht,hv,rfl⟩ := hdecomp.1 b hb
  exact U.normalizer.toSubgroup.mul_mem (hTN ht) (hVN hv)

/-- Bor1 13.16 reduces to the exact 13.7 generation theorem and the two
13.15 bounds. This is the final assembly for the actual ambient normality,
without any assumed relative normality or quotient by the candidate radical. -/
private theorem intersection_radical_normal_of_torusBorel_generation_of_envelope_bounds
    (hG : Variety.IsConnected G) {T U : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
    (hgen : Subgroup.closure
      (⋃ B : BorelContainingIndex T, (B.1 : Set (Variety.Point G))) = ⊤)
    (hdim : ∀ B V : ClosedSubgroup G, IsBorelSubgroup B → T ≤ B →
      IsUnipotentRadicalOf B V → ∀ S : CodimensionOneSubtorus T,
      ¬ Group.IsSolvable (Variety.Point S.1.centralizer.carrierVariety) →
      Variety.dimension (V.pointwiseCentralizer S.1).carrierVariety ≤
        Variety.dimension ((V.pointwiseCentralizer S.1).inter U).carrierVariety + 1)
    (hother : ∀ B V : ClosedSubgroup G, IsBorelSubgroup B → T ≤ B →
      IsUnipotentRadicalOf B V → ∀ S Q : CodimensionOneSubtorus T, Q.1 ≠ S.1 →
      ¬ Group.IsSolvable (Variety.Point S.1.centralizer.carrierVariety) →
      ¬ Group.IsSolvable (Variety.Point Q.1.centralizer.carrierVariety) →
      (unipotentEnvelope (B.pointwiseCentralizer S.1) V).pointwiseCentralizer Q.1 ≤ U) : U.toSubgroup.Normal := by
  have hN : (⊤ : Subgroup (Variety.Point G)) ≤ U.normalizer.toSubgroup := by
    rw [← hgen]
    apply (Subgroup.closure_le U.normalizer.toSubgroup).mpr
    intro x hx
    obtain ⟨B,hxB⟩ := Set.mem_iUnion.mp hx
    obtain ⟨V,hV,_⟩ := exists_unipotentRadical_of_connected_solvable B.1 B.2.1.connected B.2.1.solvable
    exact borel_le_intersection_radical_normalizer_of_envelope_bounds
      hG B.2.1 hV hT B.2.2 hU
      (hdim B.1 V B.2.1 B.2.2 hV) (hother B.1 V B.2.1 B.2.2 hV) hxB
  constructor
  intro x hx g
  exact (Subgroup.mem_normalizer_iff.mp (hN (by trivial)) x).mp hx



/-- Full source normality after the two independent rank-one results and
source separating-Borel theorem. The torus-generation premise is discharged
by Bor1 13.7 along the original ambient group. -/
theorem intersection_radical_normal
    (hG : Variety.IsConnected G) {T U : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hU : IsUnipotentRadicalOf (torusBorelIntersection T) U)
 :
    U.toSubgroup.Normal := by
  apply intersection_radical_normal_of_torusBorel_generation_of_envelope_bounds hG hT hU
    (Bor1.TorusBorelGeneration.closure_borels_containing_maximalTorus_eq_top hG T hT)
  · intro B V hB hTB hV S hns
    obtain ⟨c⟩ := Bor1.SingularTorusQuotient.centralizer_rankOne_quotient_of_not_solvable
      hG S.2.1 hT S.2.2.1 S.2.2.2 hns
    let _ : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
    have hk : c.quotientMap.kernel = c.radical.toSubgroup := by
      change c.quotientMap.kernelClosedSubgroup.toSubgroup = c.radical.toSubgroup
      rw [c.kernel_eq_radical]
    exact Bor1.SingularTorusQuotient.fixed_radical_dimension_le_of_quotient_borel_radicals
      hG S.2.1 hT.1 S.2.2.1 hU hB (fun _ hx => hTB (S.2.2.1 hx)) hV
      c.radical c.radical_isRadical c.quotientMap c.surjective hk
      (Bor1.SingularTorusQuotient.rankOne_quotient_borel_radical_dimension_le c
        (fun D A N hD hdim hA hDA hN => le_of_eq
          (Bor1.RankOneGeometry.unipotentRadical_dimension_eq_one
            c.quotient_isSemisimple D A N hD hdim hA hDA hN)))
  · intro B V hB hTB hV S P hPS hnsS hnsP
    obtain ⟨B',hB',hTB',hsep,hne'⟩ :=
      Bor1.SeparatingBorel.exists_separating_borel hG T S.1 P.1 B hT
        S.2.1 P.2.1 S.2.2.1 P.2.2.1 S.2.2.2 P.2.2.2 hPS.symm hnsS hnsP hB hTB
    have hne := hne'.symm
    obtain ⟨c⟩ := Bor1.SingularTorusQuotient.centralizer_rankOne_quotient_of_not_solvable
      hG P.2.1 hT P.2.2.1 P.2.2.2 hnsP
    let _ : AlgebraicGroup c.quotient := c.quotientAlgebraicGroup
    have hk : c.quotientMap.kernel = c.radical.toSubgroup := by
      change c.quotientMap.kernelClosedSubgroup.toSubgroup = c.radical.toSubgroup
      rw [c.kernel_eq_radical]
    exact Bor1.SingularTorusQuotient.envelope_fixed_le_radical_of_rankOne_intersections
      hG P.2.1 hT P.2.2.1 hTB hTB' hU hB hB' hV hsep hne
      c.radical c.radical_isRadical c.quotientMap c.surjective hk
      (Bor1.SingularTorusQuotient.rankOne_quotient_borel_intersection_isSubtorus c
        (fun D A A' hD hdim hA hA' hDA hDA' hne =>
          Bor1.RankOneGeometry.common_torus_borel_intersection_isSubtorus
            c.quotient_isSemisimple D A A' hD hdim hA hA' hDA hDA' hne))

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.IntersectionNormality

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
open RadicalGeometry.IntersectionNormality

/-- The center of a connected semisimple algebraic group lies in every
actual maximal torus. All Borel, quotient, and rank-one geometry is proved. -/
theorem center_le_maximalTorus_of_semisimple
    (hG : IsSemisimpleAlgebraicGroup G) {T : ClosedSubgroup G} (hT : IsMaximalTorus T) :
    Subgroup.center (Variety.Point G) ≤ T.toSubgroup := by
  apply center_le_maximalTorus_of_semisimple_of_borel_geometry hG hT
  · intro B hB hTB
    exact RadicalGeometry.BorelRestriction.isBorel_centralizer_restriction hG.1 T B hT.1 hB hTB
  · intro D hD U hU
    exact intersection_radical_normal hG.1 hD hU

end Theory.AlgebraicGroup.SemisimpleCenterContainment
