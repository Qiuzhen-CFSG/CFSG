module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.QuotientActions

/-!
# Literal quotient maps for the fixed-characteristic argument

The restriction of H → S₅ to J = K C_T(u) has kernel O₂(J), and its image
contains the prescribed A₅. This identifies the exact input to the remaining
five-point minimal-parabolic argument, without replacing the original quotient.

For the actual C-component Lᵤ in Gᵤ, its intrinsic two-core quotient is
isomorphic to its image in Gᵤ/O₂(Gᵤ). The displayed equation checks the original
quotient maps on every element. The full universal A.3.6 implication therefore
supplies its structural alternatives and genuine omega actions, including in
the non-quasisimple branch. It supplies no exclusion of that branch.

The critical subgroup and its star image are elementary, and their placements
are proved using the actual R₁ and Sylow maps. The earlier 14.7.38 escape of
Uγ from O₂(H) survives the H-rechoice and implies Uα* ≠ 1. That escape remains
an earlier-source premise owned by qt-14-07-components; it is not inferred
from EarlierImages. The A.3.6 producer is qt-a-03 (and its structural branch).
No center–Frattini equality or bound on homocyclic exponents is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.38, p.1060; Notation 14.7.1, p.1043; 14.7.66–68, pp.1070–1072;
A.3.6, pp.43–45, and 1.2.1(4), p.504.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

def fixedJoinMap (u : F.U) : d.fixedJoin u →* ChapterJ.S5 :=
  d.qH.comp (inclusion (d.fixedJoin_le_H u))

theorem fixedJoin_core_eq_inter (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) :
    (d.fixedJoin u).pCoreIn 2 = F.H.pCoreIn 2 ⊓ d.fixedJoin u := by
  apply le_antisymm
  · exact le_inf (pCoreIn_mono_of_normalizes (d.fixedJoin_le_H u)
      ((normal_subgroupOf_iff_le_normalizer (d.fixedJoin_le_H u)).mp
        (d.fixedJoin_normal u hu hfix))) (pCoreIn_le 2 _)
  · rw [inf_comm]
    exact inf_pCoreIn_le_of_le 2 (d.fixedJoin_le_H u)

theorem fixedJoinMap_ker (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) : (d.fixedJoinMap u).ker = pCore 2 (d.fixedJoin u) := by
  ext x
  change (d.qH (inclusion (d.fixedJoin_le_H u) x) = 1) ↔ _
  rw [← MonoidHom.mem_ker, d.qH_ker]
  change (x : G) ∈ F.H.pCoreIn 2 ↔ x ∈ pCore 2 (d.fixedJoin u)
  rw [← mem_map_iff_mem (d.fixedJoin u).subtype_injective]
  change (x : G) ∈ F.H.pCoreIn 2 ↔ (x : G) ∈ (d.fixedJoin u).pCoreIn 2
  rw [d.fixedJoin_core_eq_inter u hu hfix, mem_inf]
  exact (and_iff_left x.property).symm

theorem alternating_le_fixedJoinMap_range (u : F.U) :
    alternatingGroup (Fin 5) ≤ (d.fixedJoinMap u).range := by
  intro a ha
  rw [← d.K_image] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact ⟨⟨k, mem_sup_left hk⟩, rfl⟩

def fixedComponentImage (u : F.U) (Lu : Subgroup G) :
    Subgroup ((d.fixedCentralizer u) ⧸ pCore 2 (d.fixedCentralizer u)) :=
  (Lu.subgroupOf (d.fixedCentralizer u)).map (QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u)))

noncomputable def fixedComponentQuotientEquiv (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent) :
    (Lu ⧸ pCore 2 Lu) ≃* d.fixedComponentImage u Lu :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLu).symm
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLu).symm)).trans
      (cComponentTwoCoreQuotientEquiv hc)

theorem fixedComponentQuotientEquiv_apply (u : F.U) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent) (x : Lu) :
    (d.fixedComponentQuotientEquiv u hLu hc (QuotientGroup.mk' (pCore 2 Lu) x) :
      (d.fixedCentralizer u) ⧸ pCore 2 (d.fixedCentralizer u)) =
      QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u)) ⟨x, hLu x.property⟩ := rfl

theorem fixedComponent_earlier_structure
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
        B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (u : F.U) (hne : (u : G) ≠ 1) {Lu : Subgroup G}
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent) :
    Chapter1.Section02.A36Conclusion (d.fixedComponentImage u Lu) ∧
      (¬ IsQuasisimple (d.fixedComponentImage u Lu) →
        Chapter1.Section02.CenterFrattiniSource.OmegaActionData (d.fixedComponentImage u Lu)) :=
  Chapter1.Section02.proposition_1_2_1_four_earlier_with_actions
    hA36 (d.fixedCentralizer_quotient_sqtk u hne) hc

theorem fixedComponent_omega_of_not_quasisimple
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
        B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (u : F.U) (hne : (u : G) ≠ 1) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hnq : ¬ IsQuasisimple (Lu ⧸ pCore 2 Lu)) :
    Chapter1.Section02.CenterFrattiniSource.OmegaActionData (d.fixedComponentImage u Lu) := by
  apply (d.fixedComponent_earlier_structure hA36 u hne hc).2
  intro hi
  let := hi
  exact hnq (IsQuasisimple.of_mulEquiv (d.fixedComponentQuotientEquiv u hLu hc).symm)

end Data

namespace CriticalPath
variable (d : Data T L V F W) (c : CriticalPath (L := L) F)

include d in
theorem Uα_elementary : IsElementaryAbelian 2 c.Uα := by
  let := d.U_elementary
  exact IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom

include d in
theorem star_Uα_elementary (earlier : c.EarlierImages) : IsElementaryAbelian 2 (star F c.Uα) := by
  let := c.Uα_elementary d
  let := IsElementaryAbelian.subgroupOf (p := 2) (c.Uα_le_H earlier)
  exact IsElementaryAbelian.map (starMap F)

omit [Finite G] in
theorem star_Uα_le_K (earlier : c.EarlierImages) : star F c.Uα ≤ star F (K F) :=
  (c.lemma_14_7_66 earlier).1.trans (Chapter1.isSylowIn_iff.mp (c.lemma_14_7_66 earlier).2).2.1

omit [Finite G] in
theorem Uα_le_sylow (earlier : c.EarlierImages) : c.Uα ≤ (T : Subgroup G) := by
  exact earlier.placement.trans
    ((pCoreIn_le_sylow (F.Li L 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))

omit [Finite G] in
theorem star_Uα_ne_bot_of_gamma_escape (earlier : c.EarlierImages)
    (hgamma : ¬ conjugate F.U (c.gammaConjugator : G) ≤ F.H.pCoreIn 2) :
    star F c.Uα ≠ ⊥ := by
  intro hzero
  have hA : c.Uα ≤ F.H.pCoreIn 2 := by
    have hk : (c.Uα.subgroupOf F.H) ≤ pCore 2 F.H := by
      simpa only [star, Subgroup.map_eq_bot_iff, starMap, QuotientGroup.ker_mk'] using hzero
    intro x hx
    exact mem_map.mpr ⟨⟨x, c.Uα_le_H earlier hx⟩, hk hx, rfl⟩
  apply hgamma
  intro x hx
  have hy : (c.rechoice : G)⁻¹ * x * (c.rechoice : G) ∈ c.Uα := by
    obtain ⟨a, ha, rfl⟩ := hx
    refine mem_map.mpr ⟨a, ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conjugator]
    group
  have hn : (c.rechoice : G) ∈ normalizer (F.H.pCoreIn 2 : Set G) :=
    (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))) c.rechoice.property
  have hh := (mem_normalizer_iff.mp (inv_mem hn) x).mpr
    (hA (by simpa only [inv_inv] using hy))
  exact hh

end CriticalPath
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
