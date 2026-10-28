module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.UnitaryEnlargement
public import Theory.SpecificGroups.SU3.SpecialNormalizerDisplacements
public import Theory.GroupTheory.PCoreInnerSylowSupplement

/-!
# The full special-unitary enlargement, retaining its scalar center

For SU₃(2^n), n at least two, the original Borel-core quotient action is
inner by faithful descent to the projective model. Its marked starred
Sylow lies in the full Borel two-core. The inner-Sylow supplement theorem
therefore absorbs that core into the starred subgroup and the enlargement
core. The previously proved same-core identity gives literal equality
with the original starred subgroup.

This handles every odd and even n at least two without quotienting away
the cubic scalar center. The degree-one models remain separate. Only
finite local subgroups are required; the ambient completion is unrestricted.
Source: DGS, Groups and Graphs (1985), 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}
/-- The special-unitary branch of 6.1 for every fixed-field degree at least two.
The enlargement is the original starred subgroup. -/
theorem localEnlargement_eq_star_of_special_unitary (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup) :
    localEnlargement d = d.Pstar := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let R := B.pCoreIn 2
  have hn : R ≤ normalizer (d.Pstar : Set G) :=
    ((pCoreIn_le 2 B).trans hBP).trans
      ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)
  have hTR : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ R :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  have hT : (d.sylow : Subgroup d.Pstar) = R.subgroupOf d.Pstar :=
    (d.sylow.is_maximal' (isPGroup_pCoreIn 2 B).comap_subtype
      (fun _ hx => hTR (mem_map_of_mem d.Pstar.subtype hx))).symm
  have hBR : (normalizer (d.sylow : Set d.Pstar)).map d.Pstar.subtype ≤ normalizer (R : Set G) := by
    rw [← source_star_borel d,subgroupOf_map_subtype]
    exact inf_le_left.trans
      (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  let f : d.Pstar →* J.specialSubgroup := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.Pstar))
  let a : R →* MulAut (J.specialSubgroup) :=
    (MulAut.congr e).toMonoidHom.comp
      ((pCoreJoinAction 2 hn).comp (inclusion le_sup_right))
  have ha (r : R) (x : d.Pstar) : a r (f x) =
      f (d.Pstar.normalizerMonoidHom ⟨r,hn r.property⟩ x) := by
    change e (pCoreJoinAction 2 hn (inclusion le_sup_right r)
      (e.symm (e (QuotientGroup.mk' (pCore 2 d.Pstar) x)))) = _
    rw [e.symm_apply_apply,pCoreJoinAction_mk]
    rfl
  obtain ⟨T,_,hdisp⟩ := NormalSylowQuotientAction.quotient_displacements_of_local_sylow
    R d.Pstar hn d.sylow hT hBR f (e.surjective.comp (QuotientGroup.mk'_surjective _)) a ha
  have hi (r : R) : pCoreJoinAction 2 hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (d.Pstar ⧸ pCore 2 d.Pstar) := by
    obtain ⟨k,hk⟩ := isPGroup_pCoreIn 2 B r
    have hp : a r ^ (2^k) = 1 := by rw [←map_pow,hk,map_one]
    have hh := HermitianForm.NormalizerDisplacements.special_inner J hnpos hcard hconj
      T (a r) hp (hdisp r).1 (hdisp r).2
    obtain ⟨b,hb⟩ := hh
    obtain ⟨c,hc⟩ := (MulAut.congr_inner_iff e _).mp ⟨b,hb.symm⟩
    exact ⟨c,hc.symm⟩
  let : Finite (d.Pstar ⊔ R : Subgroup G) :=
    Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  have hR := le_sup_pCoreIn_of_inner_core_action d.Pstar R hn (isPGroup_pCoreIn 2 B)
    d.sylow hTR hi
  change R ≤ d.Pstar ⊔ (localEnlargement d).pCoreIn 2 at hR
  rw [localEnlargement_core d,sup_eq_left.mpr (source_core_le_star d)] at hR
  exact sup_eq_left.mpr hR

/-- The original special-unitary model predicate retains its full scalar center. -/
theorem localEnlargement_eq_star_of_isSU (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : IsSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 (2^n)) :
    localEnlargement d = d.Pstar := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  exact localEnlargement_eq_star_of_special_unitary d hB J hn hcard hconj e

end CFSG.Quasithin.ChapterF.Source.DGS85
