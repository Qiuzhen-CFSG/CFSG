module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.Geometry
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreOvergroup

/-!
# The actual conjugate span in the moving residual branch

The escaping normalizer preserves E, and C_G(E) lies in N_G(L). Consequently
O²(C_L(E)) is normal in C_G(E), as is each of its N_G(R)-conjugates. Their
span is normal in C_G(E), invariant under N_G(R), and contained in N_G(L).
The actual overgroup XLT has characteristic two by Sylow-overgroup inheritance.
These are source construction steps; no quotient order or residual count is
assumed here.

Source: Aschbacher–Smith, proof of 12.4.6, printed p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

namespace LocalGeometry
variable (d : LocalGeometry D)

/-- A canonical invariant span of the actual residual, with no change of theta
or of the unrestricted cubic family. -/
def movingSpan : Subgroup G := componentOrbit d.L₁ (normalizer (d.R : Set G))

omit [Finite G] in
theorem lineResidual_le : d.L₁ ≤ L ⊓ centralizer (d.E : Set G) :=
  map_subtype_le _

omit [Finite G] in
theorem centralizer_normalizes_lineResidual :
    normalizer (L : Set G) ⊓ centralizer (d.E : Set G) ≤ normalizer (d.L₁ : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ centralizer (d.E : Set G)) (pResidual 2 _))
  exact (le_inf inf_le_left (inf_le_right.trans (centralizer (d.E : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

/-- The source residual is intrinsically two-perfect. -/
theorem lineResidual_twoPerfect : IsPPerfect 2 d.L₁ :=
  isPPerfect_embedded_pResidual 2 _

omit [Finite G] in
theorem lineResidual_le_movingSpan : d.L₁ ≤ d.movingSpan := le_componentOrbit _ _

omit [Finite G] in
theorem normalizer_normalizes_movingSpan :
    normalizer (d.R : Set G) ≤ normalizer (d.movingSpan : Set G) :=
  le_normalizer_componentOrbit _ _

omit [Finite G] in
theorem movingSpan_le_centralizer
    (hNE : normalizer (d.R : Set G) ≤ normalizer (d.E : Set G)) :
    d.movingSpan ≤ centralizer (d.E : Set G) :=
  iSup_conjugates_le_of_le_normalizer _ _ _ (d.lineResidual_le.trans inf_le_right)
    (hNE.trans (normalizer_le_normalizer_centralizer d.E))

/-- Escape forces the entire plane centralizer into the original M. -/
theorem plane_centralizer_le_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    centralizer (d.E : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hZ, _, _, _, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  obtain ⟨_, z, _, hgen, hM, _, _, _⟩ := exists_slThree_fixed_involution_setup
    h D structural marked uniquenessEarlier_knownSimple hmodel hne
  have hFE : fixedSubgroup L V ≤ d.E := by
    rw [← d.fixed_plane]
    rw [← hZ]
    exact le_inf (hZ ▸ (show fixedSubgroup L V ≤ V from inf_le_left))
      (fun x hx => centralizer_le (show d.R ≤ T from inf_le_left)
        ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
  rw [hM]
  exact centralizer_le (Set.singleton_subset_iff.mpr (hFE (hgen ▸ mem_zpowers z)))

omit [Finite G] in
/-- This is relative normality in the literal C_G(E), not normality in G. -/
theorem lineResidual_normal_in_centralizer
    (hCM : centralizer (d.E : Set G) ≤ normalizer (L : Set G)) :
    (d.L₁.subgroupOf (centralizer (d.E : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((le_inf hCM le_rfl).trans d.centralizer_normalizes_lineResidual)

omit [Finite G] in
/-- All moved residuals remain normal in the same plane centralizer. -/
theorem conjugate_normal_in_centralizer
    (hCM : centralizer (d.E : Set G) ≤ normalizer (L : Set G))
    (hNE : normalizer (d.R : Set G) ≤ normalizer (d.E : Set G))
    (g : G) (hg : g ∈ normalizer (d.R : Set G)) :
    ((d.L₁.map (MulAut.conj g).toMonoidHom).subgroupOf
      (centralizer (d.E : Set G))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  have hC : (centralizer (d.E : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer (d.E : Set G) := mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_centralizer d.E (hNE hg))
  have hn := map_mono (f := (MulAut.conj g).toMonoidHom)
    ((le_inf hCM le_rfl).trans d.centralizer_normalizes_lineResidual)
  rw [hC, map_equiv_normalizer_eq] at hn
  exact hn

omit [Finite G] in
theorem movingSpan_normal_in_centralizer
    (hCM : centralizer (d.E : Set G) ≤ normalizer (L : Set G))
    (hNE : normalizer (d.R : Set G) ≤ normalizer (d.E : Set G)) :
    (d.movingSpan.subgroupOf (centralizer (d.E : Set G))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  apply le_trans _ (iInf_normalizer_le_normalizer_iSup _)
  apply le_iInf
  intro g
  have hc := (map_mono (f := (MulAut.conj (g : G)).toMonoidHom)
    (d.lineResidual_le.trans inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_centralizer d.E (hNE g.property)))
  let := d.conjugate_normal_in_centralizer hCM hNE g g.property
  exact le_normalizer_of_normal_subgroupOf hc

/-- The exact ambient even-characteristic hypothesis supplies characteristic two
for XLT, for any X already placed in M. -/
theorem moving_overgroup_characteristicTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (X : Subgroup G) (hXM : X ≤ normalizer (L : Set G)) :
    HasCharacteristicTwo (X ⊔ (L ⊔ (T : Subgroup G)) : Subgroup G) := by
  let M := normalizer (L : Set G)
  let J := X ⊔ (L ⊔ (T : Subgroup G))
  have hTM := (structural G T L h).1
  have he : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit _ _)
    exact iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTM
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal M := by simpa only [he] using hu.normalizer_maximal
  have hc := h.simpleQTKE.evenCharacteristic T M hm hTM
  have hJM : J ≤ M := sup_le hXM (sup_le L.le_normalizer hTM)
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_right
  have hrel := centralizer_pCore_le_of_sylow_le (T.subtype hTM) (J.subgroupOf M)
    (fun t ht => hTJ ht) hc
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hJM)).mp hrel

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
