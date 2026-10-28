module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointSpanAbelian
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FixedFreeFusion
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints

/-!
# Intersecting conjugates of the original six-space commute

The full point-centralizer span is abelian. If that centralizer lies in M,
TI and its fixed nonidentity point make it normalize V; otherwise it is an
actual member of Hz and the completed12.6.26 applies. The proved fixed-free
fusion theorem and singular-point orbit then give12.6.27 for the original V.

The actual F.9 consumer now has odd critical length at least three and a
critical endpoint, with no assumed parity or intersection-commutativity
premise. The earlier fixed-space, point-invariance, TI, intersection bound
and nonsingular-centralizer inputs remain explicit.

Source: Aschbacher--Smith12.6.26--27, printed pp.831--833, and F.9.10--11.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
include hz hTV hTz hbound hTI hns in
/-- The full original point-centralizer span is abelian, including the case
where the point centralizer lies in the original maximal subgroup. -/
theorem SourceHypothesis.original_full_point_span_abelian :
    IsMulCommutative ((D.fullSetup hZ T z).VH (D.fullSetup hZ T z).Gz) := by
  let E := D.fullSetup hZ T z
  by_cases hout : E.Gz ≤ M L
  · have hn : E.Gz ≤ normalizer (V : Set G) := by
      intro c hc
      apply mem_normalizer_iff_map_conj_eq.mpr
      rcases hTI c (hout hc) with hi | he
      · have hz' : (z : G) ∈ V ⊓ V.map (MulAut.conj c).toMonoidHom := by
          refine ⟨z.property,z,z.property,?_⟩
          change c * (z : G) * c⁻¹ = (z : G)
          rw [←hc z (mem_zpowers _),mul_inv_cancel_right]
        exact (hz (Subtype.ext (mem_bot.mp (hi ▸ hz')))).elim
      · exact he
    have he : E.VH E.Gz = V :=
      le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
    rw [he]
    infer_instance
  · exact S.original_point_span_abelian D hZ z hz hTV hTz hbound
      (E.Gz_mem_Hz hz hTz hout) hTI hns

include hz hTV hTz hbound hTI hns in
/-- Source 12.6.27 on the original module. Element fusion and the singular
intersection orbit are constructed, retaining the earlier geometric inputs. -/
theorem SourceHypothesis.original_intersecting_conjugates_commute
    (g : G) (hi : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let E := D.fullSetup hZ T z
  have hf := S.fixed_free_controls_element_fusion D hTV hTI hZ
  apply E.lemma_12_6_27_of_abelian
    (S.original_full_point_span_abelian D hZ z hz hTV hTz hbound hTI hns) _ _ g hi
  · intro a ha
    obtain ⟨l,hl,he⟩ := hf z z.property a ha
    exact ⟨l,S.chosen.normalizes hl,he⟩
  · intro a ha x hx hxn
    have hs : ¬ D.Nonsingular (⟨x,hx.1⟩ : V) := by
      intro hs
      exact ha (mem_normalizer_iff_map_conj_eq.mpr
        (CentralLine.unique_conjugate_of_centralizer_le S.chosen.normalizes hf hTI
          hx.1 hxn (hns ⟨x,hx.1⟩ hs) hx.2))
    obtain ⟨l,hl⟩ := S.original_singular_point_orbit D hZ
      (⟨x,hx.1⟩ : V) (fun he => hxn (congrArg Subtype.val he)) hs z hz
      (S.original_point_singular D hZ z hz hTz)
    exact ⟨l,S.chosen.normalizes l.property,congrArg Subtype.val hl⟩

include hz hTV hTz hbound hTI hns in
/-- The actual abelian F.9 critical track has odd length at least three,
and supplies an original critical endpoint. -/
theorem SourceHypothesis.original_abelian_critical_geometry
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
    3 ≤ h.b ∧ Odd h.b ∧ Nonempty h.CriticalEndpoint := by
  let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hc := S.original_intersecting_conjugates_commute D hZ z hz hTV hTz hbound hTI hns
  have hv := (S.original_abelian_point_geometry D hZ z hz hTV hTz hbound hH hTI hns).2.2.1
  have hb := h.b_bounds_of_intersecting_conjugates_commute hv hc
  exact ⟨hb.1,hb.2,h.criticalEndpoint_nonempty hv hc⟩
end CFSG.Quasithin.Chapter12.Section06
