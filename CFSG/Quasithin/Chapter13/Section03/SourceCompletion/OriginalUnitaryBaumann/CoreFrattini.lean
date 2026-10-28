module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.ConjugateEscape
public import Theory.Frattini.ConjugateCentralFactors

/-!
# The unitary fixed factor has trivial Frattini subgroup

The direct product and the conjugate factorization identify the embedded
Frattini subgroups of the two cores with Φ(C_B(L)). Thus the escaping
Baumann-normalizer element preserves Φ(C_B(L)). This subgroup is normal
in LT; maximal-local uniqueness would put its normalizer inside N_G(L)
if it were nontrivial. That contradicts the chosen escape. Consequently
the whole product core is elementary abelian.

Source: Aschbacher--Smith 13.3.10(2), printed p.888. The original flag
consumer supplies the core product and factorization without extra premises.
The exceptional MS reconstruction and the final normalizer argument remain
with qt-d-13316-noncentrality.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]

theorem unitary_baumann_core_elementary_of_conjugate_product
    {T : Sylow 2 G} {L V : Subgroup G}
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hshort : ChapterC.IsShort L)
    (hcore : (L ⊔ ChapterB.baumann R).pCoreIn 2 =
      ChapterB.baumann R ⊓ centralizer (V : Set G))
    (hprod : (L ⊔ ChapterB.baumann R).pCoreIn 2 =
      V ⊔ (ChapterB.baumann R ⊓ centralizer (L : Set G)))
    (x : G) (hx : x ∈ normalizer (ChapterB.baumann R : Set G))
    (hext : ¬ V.map (MulAut.conj x⁻¹).toMonoidHom ≤ (L ⊔ ChapterB.baumann R).pCoreIn 2)
    (hc : ChapterB.baumann R ⊓ centralizer (L : Set G) ≤
      centralizer (V.map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    (hspan : ChapterB.baumann R = V.map (MulAut.conj x⁻¹).toMonoidHom ⊔
      (L ⊔ ChapterB.baumann R).pCoreIn 2) :
    frattini (ChapterB.baumann R ⊓ centralizer (L : Set G) : Subgroup G) = ⊥ ∧
      IsElementaryAbelian 2 ((L ⊔ ChapterB.baumann R).pCoreIn 2) := by
  let B := ChapterB.baumann R
  let Q := (L ⊔ B).pCoreIn 2
  let C := B ⊓ centralizer (L : Set G)
  let P := (frattini C).map C.subtype
  have hBa : B.map (MulAut.conj x⁻¹).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hx)
  have hBQ : B ≤ normalizer (Q : Set G) :=
    le_sup_right.trans ((L ⊔ B).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ B) (pCore 2 (L ⊔ B : Subgroup G))))
  have hphi := frattini_conjugate_central_factors B V Q C (MulAut.conj x⁻¹)
    hBa hcore hprod hc hspan chosen.elementary (isPGroup_pCoreIn 2 (L ⊔ B)) hBQ
  have hCN : L ⊔ (T : Subgroup G) ≤ normalizer (C : Set G) := by
    apply sup_le
    · exact (le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)
    · exact (le_inf (hTR.trans (Stellmacher.normalizer_le_normalizer_baumann R))
        (chosen.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
          inf_normalizer_le_normalizer_inf
  have hPN : L ⊔ (T : Subgroup G) ≤ normalizer (P : Set G) :=
    hCN.trans (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hPzero : P = ⊥ := by
    by_contra hp
    have hPM := chosen.normal_subgroup_normalizer_le
      (unitary_original_hypothesis1223 h hmax eL).toHypothesis1221
      ((map_subtype_le _).trans (inf_le_left.trans (inf_le_left.trans (hRT.trans le_sup_right))))
      hp hPN
    have hxM : x⁻¹ ∈ normalizer (L : Set G) :=
      hPM (mem_normalizer_iff_map_conj_eq.mpr hphi)
    have hNV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
      rw [RecognitionSource.FusionReducibleNormalizer.chosen_eq_blockU chosen hshort]
      exact normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)
    have hVa : V.map (MulAut.conj x⁻¹).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (hNV hxM)
    apply hext
    rw [hVa,hprod]
    exact le_sup_left
  have hCzero : frattini C = ⊥ :=
    ((frattini C).map_eq_bot_iff_of_injective C.subtype_injective).mp hPzero
  have hQphi := frattini_map_eq_of_central_elementary_supplement Q C V
    (isPGroup_pCoreIn 2 (L ⊔ B)) chosen.elementary
    (le_centralizer_iff.mp (hcore.le.trans inf_le_right)) hprod
  have hQzero : frattini Q = ⊥ :=
    ((frattini Q).map_eq_bot_iff_of_injective Q.subtype_injective).mp (hQphi.trans hPzero)
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 (L ⊔ B)⟩
  exact ⟨hCzero,(frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hQzero⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
