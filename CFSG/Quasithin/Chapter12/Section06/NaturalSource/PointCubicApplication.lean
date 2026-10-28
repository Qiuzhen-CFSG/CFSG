module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedFiltration
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointCubicMarking

/-!
# Applying the canonical point marking

The exchanged-filtration contradiction is already proved for a marked
nonidentity cubic.  This adapter supplies its point-coordinate premise from
the original singular-point theorem, while keeping the selected cubic in the
actual component `K` and preserving the original quotient map.

Source: Aschbacher--Smith, 12.6.33, printed pp.837--838.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes)
  (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include S D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The marked-cubic exchanged-filtration contradiction with the point marking
constructed from the original source point. -/
theorem SourceHypothesis.original_abelian_exchanged_impossible_of_original_point
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    (hout : ¬ K ≤ M L)
    (x : K) (hxL : (x : G) ∈ L) (hx3 : x ^ 3 = 1) (hxn : x ≠ 1) : False := by
  obtain ⟨r, hr⟩ := SourceHypothesis.original_point_cubic_marking S D hZ z hz hTz
  apply S.original_abelian_exchanged_impossible_of_marked_cubic D hZ z hz hTV hTz
    hbound hTI hns hH hKH hK hgen hn hm hout r
    ((D.fullCoordinates_apply hZ z).symm.trans hr) x hxL hx3 hxn

end CFSG.Quasithin.Chapter12.Section06
