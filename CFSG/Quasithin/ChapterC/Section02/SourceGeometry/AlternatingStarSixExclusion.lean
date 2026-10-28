module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SixStarModels
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalControl
public import Theory.SpecificGroups.AlternatingSixNormalizer
public import Theory.Alternating.Aut

/-!
# Alternating C.2.7 star components cannot enlarge an A6 residual

The genuine source kernel and offender conclusions identify K* with the
whole generalized Fitting subgroup of the star extension. For K* = A7
or A8, conjugation and the actual automorphism theorem therefore embed that
extension faithfully in the symmetric group, with its original K* marking.
The nontrivial radical image is normalized by the perfect A6 residual image.
The intrinsic permutation normalizer exclusions apply; in degree eight,
the original ambient Sylow also supplies a full Sylow of A8 normalizing
the radical image. No transposition or module marking is assumed.

The fixed-coset application is in LocalAnalysisSylowResidualsComponentsSourceModels.
Source: Aschbacher--Smith C.2.7(1--3), printed pp.145--147, and 3.3.22, p.597.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

/-- Conjugation gives a faithful permutation realization of the whole star
extension, with its original alternating subgroup marking. -/
theorem alternating_star_embedding
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : starImage K R K ≃* alternatingGroup (Fin n)) :
    ∃ f : StarQuotient K R →* Equiv.Perm (Fin n), Function.Injective f ∧
      ∀ k : starImage K R K, f k = (e k : Equiv.Perm (Fin n)) := by
  let A := starImage K R K
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : A.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hfit := (star_fitting_quasisimple (source_join_input h)).1
  let a : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)
  let f : StarQuotient K R →* Equiv.Perm (Fin n) := a.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : StarQuotient K R →* MulAut A))
  have hf (k : A) : f k = (e k : Equiv.Perm (Fin n)) := by
    apply a.injective
    change a (a.symm (MulAut.congr e (MulAut.conjNormal (k : StarQuotient K R)))) = _
    rw [a.apply_symm_apply]
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (e (k * e.symm z * k⁻¹) : Equiv.Perm (Fin n)) =
      (e k : Equiv.Perm (Fin n)) * z * (e k : Equiv.Perm (Fin n))⁻¹
    simp only [map_mul,map_inv,e.apply_symm_apply,Subgroup.coe_mul,Subgroup.coe_inv]
  refine ⟨f,?_,hf⟩
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hc : x ∈ centralizer (A : Set (StarQuotient K R)) := by
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    change MulAut.conjNormal x = 1
    have hh : a.symm (MulAut.congr e (MulAut.conjNormal x)) = 1 := hx
    rw [←map_one a.symm,a.symm.injective.eq_iff,
      ←map_one (MulAut.congr e),(MulAut.congr e).injective.eq_iff] at hh
    exact hh
  have hxA : x ∈ A := by
    apply (show centralizer (A : Set (StarQuotient K R)) ≤ A from ?_) hc
    dsimp only [A]
    rw [←hfit]
    exact centralizer_generalizedFitting_le _
  have hz : (⟨x,hxA⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_iff.mp hc y y.property
  have hez : e ⟨x,hxA⟩ ∈ center (alternatingGroup (Fin n)) :=
    (centerCongr e ⟨⟨x,hxA⟩,hz⟩).property
  rw [alternatingGroup.center_eq_bot (by simp; omega)] at hez
  have hh : (⟨x,hxA⟩ : A) = 1 := e.injective (by simpa using mem_bot.mp hez)
  exact mem_bot.mpr (congrArg Subtype.val hh)

omit [Finite G] in
private theorem star_image_normalizes_radical {k : K}
    (hk : (k : G) ∈ normalizer (R : Set G)) :
    (toStarImage K R k : StarQuotient K R) ∈ normalizer (starImage K R R : Set _) := by
  apply (R.subgroupOf (K ⊔ R)).le_normalizer_map (QuotientGroup.mk' (starKernel K R))
  apply mem_map_of_mem
  rw [←subgroupOf_normalizer_eq (show R ≤ K ⊔ R from le_sup_right)]
  exact hk

/-- Direct exclusion of both large alternating star models. The original
radical is normalized by the A6 residual and by the inherited Sylow. -/
theorem no_large_alternating_star_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hBR : B ≤ normalizer (R : Set G))
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {n : ℕ} (hn : n = 7 ∨ n = 8)
    (e : starImage K R K ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨f,hf,hfe⟩ := alternating_star_embedding h (by omega) (by omega) e
  let A := starImage K R K
  let Q := (starImage K R R).map f
  let b := (toStarImage K R).comp (inclusion (hB.trans inf_le_right))
  let g := f.comp (A.subtype.comp b)
  let N := g.range
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hQ : IsPGroup 2 Q := (hR.comap_subtype.map (QuotientGroup.mk' (starKernel K R))).map f
  have hQne : Q ≠ ⊥ := by
    intro hh
    let : (K.subgroupOf (K ⊔ R)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
    exact star_radical_ne_bot (source_join_input h)
      (((starImage K R R).map_eq_bot_iff_of_injective hf).mp hh)
  have hN : N ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨x,rfl⟩
    change f (b x) ∈ _
    rw [hfe]
    exact (e (b x)).property
  have hnorm (k : K) (hk : (k : G) ∈ normalizer (R : Set G)) :
      f (toStarImage K R k) ∈ normalizer (Q : Set _) :=
    (starImage K R R).le_normalizer_map f
      (mem_map_of_mem f (star_image_normalizes_radical hk))
  have hNQ : N ≤ normalizer (Q : Set _) := by
    rintro _ ⟨x,rfl⟩
    exact hnorm (inclusion (hB.trans inf_le_right) x) (hBR x.property)
  let : Group.IsSolvable g.ker := by
    dsimp only [g]
    rw [MonoidHom.ker_comp_of_injective _ _ hf,
      MonoidHom.ker_comp_of_injective _ _ A.subtype_injective]
    exact six_star_map_ker_solvable h _
  have h5 : 5 ∣ Nat.card N := (by decide : 5 ∣ 360).trans (six_card_dvd_range e6 g)
  rcases hn with rfl | rfl
  · have he : g.rangeRestrict.ker = g.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable g.rangeRestrict.ker := he.symm ▸ inferInstanceAs (Group.IsSolvable g.ker)
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (B ⧸ pCore 2 B) := e6.isSimpleGroup
    have hr := PerfectCoreTwoExtension.odd_rank_le_of_solvable_kernel (by decide : Odd 3)
      g.rangeRestrict
    have hB3 : primeRank 3 B = 2 := by
      rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
        primeRank_equiv 3 e6,
        GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]
    rw [hB3] at hr
    exact Theory.SpecificGroups.AlternatingSixNormalizer.seven_no_normalized_two Q N hQ hQne hN hNQ h5 hr
  · obtain ⟨U,hU⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
    let P := (U.mapSurjective (toStarImage_surjective K R)).mapSurjective
      (f := e.toMonoidHom) e.surjective
    apply Theory.SpecificGroups.AlternatingSixNormalizer.eight_no_normalized_two Q N hQ hQne hN hNQ h5 P
    rintro _ ⟨x,⟨y,⟨k,hk,rfl⟩,rfl⟩,rfl⟩
    change (e (toStarImage K R k) : Equiv.Perm (Fin 8)) ∈ normalizer (Q : Set _)
    rw [←hfe]
    apply hnorm
    apply hTR
    change k ∈ (U : Subgroup K) at hk
    rw [hU] at hk
    exact hk

end CFSG.Quasithin.ChapterC.C27Source
