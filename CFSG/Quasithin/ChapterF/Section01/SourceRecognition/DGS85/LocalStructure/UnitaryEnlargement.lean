module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import Theory.SpecificGroups.SU3.NormalizerDisplacements
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# Projective-unitary endpoints in the DGS enlargement

The full Borel two-core normalizes the marked starred Sylow. Its quotient
action preserves that Sylow and has trivial displacements on its whole
normalizer quotient. The binary PSU₃ normalizer detector makes this action
inner for every fixed-field degree n at least two. The unchanged embedded
two-core then forces the enlargement to equal the original starred subgroup.

For even n, the canonical special-to-projective equivalence also proves
the equality from an original SU₃ marking. No odd-degree scalar center is
discarded: those special-unitary covers and both degree-one models remain
separate obligations. Only the finite endpoint is used; the completion
need not be finite.

Source: DGS, Groups and Graphs (1985), 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}
/-- The projective-unitary branch of 6.1 for every fixed-field degree at least two.
The enlargement is the original starred subgroup. -/
theorem localEnlargement_eq_star_of_projective_unitary (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hnpos : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
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
  let f : d.Pstar →* ProjectiveSpecialUnitaryMatrixGroup J := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.Pstar))
  let a : R →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
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
    have hh := HermitianForm.NormalizerDisplacements.inner J hnpos hcard hconj
      T (a r) hp (hdisp r).1 (hdisp r).2
    obtain ⟨b,hb⟩ := hh
    obtain ⟨c,hc⟩ := (MulAut.congr_inner_iff e _).mp ⟨b,hb.symm⟩
    exact ⟨c,hc.symm⟩
  have hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥ := by
    apply bot_unique
    intro z hz
    have he : e z ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) := (centerCongr e ⟨z,hz⟩).property
    rw [HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj,mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  have hm := map_subgroupOf_pCoreJoin_eq_top_of_inner d.Pstar R hn (isPGroup_pCoreIn 2 B) hz hi
  have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 (d.Pstar ⊔ R : Subgroup G)))) hm
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hc
  have hh := congrArg (Subgroup.map (d.Pstar ⊔ R).subtype) hc
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show d.Pstar ≤ d.Pstar ⊔ R from le_sup_left),
    ←MonoidHom.range_eq_map,range_subtype] at hh
  change d.Pstar ⊔ (localEnlargement d).pCoreIn 2 = localEnlargement d at hh
  rw [localEnlargement_core d,sup_eq_left.mpr (source_core_le_star d)] at hh
  exact hh.symm

/-- The source projective-unitary model predicate supplies the same actual equality. -/
theorem localEnlargement_eq_star_of_isPSU (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 (2^n)) :
    localEnlargement d = d.Pstar := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  exact localEnlargement_eq_star_of_projective_unitary d hB J hn hcard hconj e

/-- For even degree the canonical special-to-projective map is injective;
this also settles the special-unitary enlargement without replacing its marking. -/
theorem localEnlargement_eq_star_of_even_special_unitary (d : LocalRankOneData P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup) :
    localEnlargement d = d.Pstar :=
  localEnlargement_eq_star_of_projective_unitary d hB J hn hcard hconj
    (e.trans (HermitianForm.EvenProjectiveComparison.specialProjectiveEquiv J heven hconj))

end CFSG.Quasithin.ChapterF.Source.DGS85
