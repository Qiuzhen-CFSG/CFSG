module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourQuotient
public import Theory.SpecificGroups.SL3.FourOuterQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
/-!
# The original SL₃(4) outer four-group

The full normal component is the generalized Fitting subgroup of H-star,
so it contains its relative centralizer. Perfect central descent embeds the
literal quotient H-star/K-star in Out(PSL₃(4)). Its established noncyclic
two-group structure and the outer order bound make it E₄. The full component,
its scalar center and the original quotient maps are retained.

Source: Aschbacher–Smith 12.6.31(1), printed pp.836–837. The module exclusion
and original universal natural reduction remain further source obligations.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)


include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The original quotient by the full special-linear component is a four-group. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_kleinFour
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    letI : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective _)
    IsKleinFour ((H ⧸ pCore 2 H) ⧸ actorImage H K) := by
  let B := actorImage H K
  let : B.Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨h2,hnc,hfit⟩ := S.original_abelian_normal_specialLinearFour_quotient
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  have hq : IsQuasisimple B :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  let _ := hq
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let e : B ≃* SL(3,F) := (componentStarEquiv H K hKH hK).symm.trans eK
  have hc : centralizer (B : Set (H ⧸ pCore 2 H)) ≤ B := by
    change centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) ≤ actorImage H K
    rw [←hfit]
    exact centralizer_generalizedFitting_le (H ⧸ pCore 2 H)
  exact Matrix.SpecialLinearGroup.isKleinFour_quotient_of_card_four B e hcard hc h2 hnc

end CFSG.Quasithin.Chapter12.Section06
