module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.IntersectingConjugates
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalF918

/-!
# The quadratic actor on the original abelian point section

The proved abelianness of V_H, intersecting-conjugate commutation and
C_G(V₅)=C_G(V) discharge the hypotheses of F.9.16. The resulting action
is faithful on the literal U_H/V₁, with actor H/O₂(H). Its quadratic
witness lies in the actual edge core, and that placement makes the same
actor faithful on the residual image. No component selection or catalogue
is assumed here.

Source: Aschbacher--Smith,12.6.30(1--2), printed p.835, and F.9.16.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.ModuleBound
open Chapter15.Section03.AbelianAmalgam.GenerationOne
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
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)

include hz hTV hTz hbound hTI hns hH in
/-- The actual source section has q≤2, witnessed inside the literal edge
core by one nontrivial quadratic actor, faithful on the residual image. -/
theorem SourceHypothesis.original_abelian_quadratic_actor :
    ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H),
      let _ := hU
      ∃ a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁,
        quadraticRatio a.representation ≤ 2 ∧
        ∃ B : Subgroup H,
          B ≤ (((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
          IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
            2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
            centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have h91 : SourceF91 T L V E.V₅ E.V₁ H := SourceF91.ofF91 h
  let : IsMulCommutative (conjugateSpanBy V H) :=
    (S.original_abelian_point_geometry D hZ z hz hTV hTz hbound hH hTI hns).1
  have h62 := S.original_intersecting_conjugates_commute D hZ z hz hTV hTz hbound hTI hns
  have h47 : ∀ x ∈ centralizer (E.V₅ : Set G),
      ⁅V,zpowers x⁆ = ⊥ ∨ NormalizingConjugatesCentralize V x := by
    intro x hx
    have hc := S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound
    have hxV : x ∈ centralizer (V : Set G) := hc ▸ hx
    exact Or.inl (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (zpowers_le.mpr hxV)))
  obtain ⟨hU,ha⟩ := OriginalF916.original_bounded_action h91 h62 h47
  let _ := hU
  obtain ⟨a,hq⟩ := ha
  obtain ⟨B,hB,he,hquad,hcodim⟩ := OriginalF916.original_witness h91 h62 h47 a
  exact ⟨hU,a,hq,B,hB,he,hquad,hcodim,
    source_internal_actor_faithful_on_residual T h91.toF91.T_le_H B hB⟩

end CFSG.Quasithin.Chapter12.Section06
