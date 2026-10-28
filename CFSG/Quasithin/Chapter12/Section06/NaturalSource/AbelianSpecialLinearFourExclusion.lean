module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourCoordinates
public import CFSG.Quasithin.Chapter12.Section06.LocalAlternatives.SpecialLinearFourCritical
/-!
# Excluding the original full SL₃(4) component

The original faithful U_H/V₁ action has natural-plus-dual coordinates.
Apply the F.9 common-line obstruction to the actual reduced H. The proved
abelian span, intersecting-conjugate commutation and perpendicular-centralizer
equality supply its geometry. Every critical denominator case is covered,
so no equality of H with the full point centralizer is used.

This gives the SL₃(4) exclusion needed in 12.6.32, preserving the intrinsic
K/O₂(K), original H/O₂(H), the scalar center and all earlier geometry inputs.
It replaces the source's nonsingular-parabolic final step by the applicable
F.9 matrix obstruction; the earlier nonsingular-centralizer premise remains
explicit and is still used to establish the abelian geometry.
Source: Aschbacher–Smith 12.6.30–32, printed pp.835–837, and F.9.13–16,
pp.322–324, with the natural-plus-dual obstruction of 13.8.20, p.955.
-/
public noncomputable section
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

variable (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original full special-linear component is excluded on its literal
U_H/V₁, using F.9 on the actual reduced H. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_excluded
    (hn : (K.subgroupOf H).Normal) :
    ¬ Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4 := by
  intro hm
  let E := D.fullSetup hZ T z
  obtain ⟨hU,a,_⟩ := S.original_abelian_quadratic_actor
    D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  obtain ⟨e,q,hq⟩ := S.original_abelian_normal_specialLinearFour_coordinates
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a hgen
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let : IsMulCommutative (conjugateSpanBy V H) :=
    (S.original_abelian_point_geometry D hZ z hz hTV hTz hbound hH hTI hns).1
  let : IsElementaryAbelian 2 (E.f9 H).VH :=
    conjugateSpanBy_elementary_of_commutative V H
  let : IsElementaryAbelian 2 (E.f9 H).UH := hU
  let s := ModuleBound.OriginalF916.conjugationSection a h.H_centralizes
  refine @LocalAlternatives.specialLinearFour_impossible_of_f9 G _ _ _ _ _ _
    (E.f9 H) h _ _ a.representation s
    (actorImage H K) (hn.map _ (QuotientGroup.mk'_surjective _)) e q hq
    (S.original_intersecting_conjugates_commute D hZ z hz hTV hTz hbound hTI hns) ?_
  intro x hx
  have hc := S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound
  have hxV : x ∈ centralizer (V : Set G) := hc ▸ hx
  exact Or.inl (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (zpowers_le.mpr hxV)))

end CFSG.Quasithin.Chapter12.Section06
