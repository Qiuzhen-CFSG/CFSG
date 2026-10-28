module
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.CartanGeometry.Source
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry

/-!
# Semisimple center containment after the Cartan step

The Cartan source layer discharges connectedness and solvability of maximal
centralizers.  This assembly keeps only the genuine remaining source input:
the Borel restriction and unipotent-radical normality statements used by
Bor1, IV, 13.16--13.17.  Once those are supplied, the center is contained in
the specified maximal torus.
-/

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem center_le_maximalTorus_of_semisimple_of_borel_geometry
    {K : Variety k} [AlgebraicGroup K]
    (hK : IsSemisimpleAlgebraicGroup K)
    {S : ClosedSubgroup K} (hS : IsMaximalTorus S)
    (hfixed : ∀ B : ClosedSubgroup K, IsBorelSubgroup B → S ≤ B →
      IsBorelSubgroup (S.centralizer.inclusion.closedSubgroupPreimage B))
    (hnormal : ∀ T : ClosedSubgroup K, IsMaximalTorus T →
      ∀ V : ClosedSubgroup K,
        IsUnipotentRadicalOf
          (torusBorelIntersection
            (T : ClosedSubgroup K)) V → V.toSubgroup.Normal) :
    Subgroup.center (Variety.Point K) ≤ S.toSubgroup := by
  have hred : IsReductiveAlgebraicGroup K :=
    isReductive_of_isSemisimple hK
  have hconn : Variety.IsConnected S.centralizer.carrierVariety :=
    CartanGeometry.subtorus_centralizer_isConnected hK.1 hS.1
  have hsolv : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety) :=
    CartanGeometry.maximalTorus_centralizer_connected_solvable hK.1 hS |>.2
  have hrad : ∀ R : ClosedSubgroup S.centralizer.carrierVariety,
      IsRadicalSubgroup R → IsSubtorus R := by
    intro R hR
    exact RadicalGeometry.centralizer_radical_isSubtorus_of_borel_geometry
      hred S hS.1 hconn hfixed hnormal R hR
  exact center_le_maximalTorus_of_connected_solvable_of_toral_radicals
    hS hconn hsolv hrad

end Theory.AlgebraicGroup.SemisimpleCenterContainment
