module
public import Theory.SpecificGroups.SU3.SmallSpecialNormalizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalEnlargement
public import Theory.GroupTheory.NormalSylowQuotientAction.Local
public import Theory.GroupTheory.PCoreInnerSylowSupplement

/-!
# The actual Borel-core action on a small special-unitary quotient

Transport the original conjugation action on G*/O₂(G*) through its given
marking. The marked starred Sylow is the intersection with the full Borel
core; its normalizer normalizes that core. Thus the quotient action has
trivial displacements on the whole Sylow normalizer modulo the same Sylow.
For SU₃(2) this fixes the cubic scalar center and eliminates every nonidentity
field parameter in an actual semilinear formula.

If those actual actors have semilinear formulas, the scalar and determinant
calculations make them inner. The inner-Sylow supplement and the unchanged
embedded core then give literal equality of the enlargement and starred
subgroup. Existence of these formulas for arbitrary small-unitary actors
remains open; the theorem does not assert unrestricted DGS 6.1.
Source: DGS, Groups and Graphs (1985), 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The full-Borel-core conjugation action, transported by the supplied quotient marking. -/
@[expose] def markedBorelCoreAction (d : LocalRankOneData P B)
    {D : Type*} [Group D] (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* D) :
    B.pCoreIn 2 →* MulAut D :=
  (MulAut.congr e).toMonoidHom.comp
    ((pCoreJoinAction 2 (show B.pCoreIn 2 ≤ normalizer (d.Pstar : Set G) from
      ((pCoreIn_le 2 B).trans (le_sup_right.trans d.supplement.le)).trans
        ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))).comp
      (inclusion le_sup_right))

/-- On each original starred representative, the marked action is literal ambient conjugation. -/
theorem markedBorelCoreAction_mk (d : LocalRankOneData P B)
    {D : Type*} [Group D] (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* D)
    (r : B.pCoreIn 2) (x : d.Pstar) :
    markedBorelCoreAction d e r (e (QuotientGroup.mk' (pCore 2 d.Pstar) x)) =
      e (QuotientGroup.mk' (pCore 2 d.Pstar)
        (d.Pstar.normalizerMonoidHom ⟨r,
          (((pCoreIn_le 2 B).trans (le_sup_right.trans d.supplement.le)).trans
            ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)) r.property⟩ x)) := by
  have hn : B.pCoreIn 2 ≤ normalizer (d.Pstar : Set G) :=
    ((pCoreIn_le 2 B).trans (le_sup_right.trans d.supplement.le)).trans
      ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)
  change e (pCoreJoinAction 2 hn (inclusion le_sup_right r)
    (e.symm (e (QuotientGroup.mk' (pCore 2 d.Pstar) x)))) = _
  rw [e.symm_apply_apply,pCoreJoinAction_mk]
  rfl

/-- The same actual quotient Sylow works for every full-Borel-core actor. -/
theorem markedBorelCoreAction_normalizer_displacements (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {D : Type*} [Group D] (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* D) :
    ∃ T : Sylow 2 D, ∀ r : B.pCoreIn 2,
      (T : Subgroup D).map (markedBorelCoreAction d e r).toMonoidHom = T ∧
      ∀ x ∈ normalizer (T : Set D), x⁻¹ * markedBorelCoreAction d e r x ∈ T := by
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
  let f : d.Pstar →* D := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.Pstar))
  let a := markedBorelCoreAction d e
  have ha (r : R) (x : d.Pstar) : a r (f x) =
      f (d.Pstar.normalizerMonoidHom ⟨r,hn r.property⟩ x) := by
    change e (pCoreJoinAction 2 hn (inclusion le_sup_right r)
      (e.symm (e (QuotientGroup.mk' (pCore 2 d.Pstar) x)))) = _
    rw [e.symm_apply_apply,pCoreJoinAction_mk]
    rfl
  obtain ⟨T,_,hdisp⟩ := NormalSylowQuotientAction.quotient_displacements_of_local_sylow
    R d.Pstar hn d.sylow hT hBR f (e.surjective.comp (QuotientGroup.mk'_surjective _)) a ha
  exact ⟨T,hdisp⟩

/-- The full source Borel core fixes the cubic center in the marked SU₃(2) quotient. -/
theorem small_special_borel_core_fixes_center (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup)
    (r : B.pCoreIn 2) :
    ∀ z ∈ center J.specialSubgroup, markedBorelCoreAction d e r z = z := by
  obtain ⟨T,hT⟩ := markedBorelCoreAction_normalizer_displacements d hB e
  exact HermitianForm.SmallSpecialNormalizer.fixes_center_of_normalizer_displacements
    J hc hconj T (markedBorelCoreAction d e r) (hT r).2

/-- The field parameter of any semilinear formula for the actual source actor is identity. -/
theorem small_special_borel_core_field_parameter (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup)
    (r : B.pCoreIn 2) (σ : F ≃+* F)
    (hs : J.HasSpecialUnitarySemilinearForm (markedBorelCoreAction d e r) σ) : σ = 1 :=
  HermitianForm.SmallSpecialNormalizer.field_eq_one_of_center_fixed J hc hconj
    (markedBorelCoreAction d e r) σ hs (small_special_borel_core_fixes_center d hB J hc hconj e r)

/-- Small special-unitary enlargement from semilinear coverage of the actual Borel-core actors. The coverage premise is retained for final discharge. -/
theorem localEnlargement_eq_star_of_small_special_semilinear (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup)
    (hs : ∀ r : B.pCoreIn 2, ∃ σ : F ≃+* F,
      J.HasSpecialUnitarySemilinearForm (markedBorelCoreAction d e r) σ) :
    localEnlargement d = d.Pstar := by
  let := d.finite_P
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let R := B.pCoreIn 2
  have hn : R ≤ normalizer (d.Pstar : Set G) :=
    ((pCoreIn_le 2 B).trans hBP).trans
      ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)
  have hTR : (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype ≤ R :=
    pGroup_le_core_of_core_sylow B _ (source_star_sylow_le_borel d) (d.sylow.isPGroup'.map _) hB
  obtain ⟨T,hT⟩ := markedBorelCoreAction_normalizer_displacements d hB e
  have hi (r : R) : pCoreJoinAction 2 hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (d.Pstar ⧸ pCore 2 d.Pstar) := by
    obtain ⟨k,hk⟩ := isPGroup_pCoreIn 2 B r
    have hp : markedBorelCoreAction d e r ^ (2^k) = 1 := by rw [←map_pow,hk,map_one]
    obtain ⟨b,hb⟩ := HermitianForm.SmallSpecialNormalizer.inner_of_semilinear_normalizer_displacements
      J hc hconj T (markedBorelCoreAction d e r) hp (hT r).2 (hs r)
    obtain ⟨c,hc⟩ := (MulAut.congr_inner_iff e _).mp ⟨b,hb.symm⟩
    exact ⟨c,hc.symm⟩
  let : Finite (d.Pstar ⊔ R : Subgroup G) :=
    Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  have hR := le_sup_pCoreIn_of_inner_core_action d.Pstar R hn (isPGroup_pCoreIn 2 B)
    d.sylow hTR hi
  change R ≤ d.Pstar ⊔ (localEnlargement d).pCoreIn 2 at hR
  rw [localEnlargement_core d,sup_eq_left.mpr (source_core_le_star d)] at hR
  exact sup_eq_left.mpr hR
end CFSG.Quasithin.ChapterF.Source.DGS85
