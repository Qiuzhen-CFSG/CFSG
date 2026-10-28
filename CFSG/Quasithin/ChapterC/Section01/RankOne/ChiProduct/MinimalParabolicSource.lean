module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport
/-!
# Residual chi-zero products under characteristic exclusion

If no nontrivial characteristic subgroup of the Sylow two-group is normal,
its characteristic-normalizer closure lies in the unique maximal overgroup.
The complete ordered chi-zero product source then supplies a moved block
outside that maximal subgroup. This block and the Sylow subgroup generate
the group. Its Sylow orbit consists of commuting blocks and generates the
two-residual, retaining the original Thompson commutator identity.

This is the full block-product branch of C.1.26 on the stronger domain
available in 13.6.18–19 from 13.6.16(2). It does not choose a universal
characteristic pair or assert the unrestricted C.1.26 alternatives.
Source: Aschbacher–Smith C.1.26 and C.1.28–29, printed pp.132–134.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem control_le_maximal_of_characteristic_exclusion
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hno : ∀ A : Subgroup T, A.Characteristic → A ≠ ⊥ →
      ¬ (A.map (T : Subgroup G).subtype).Normal) :
    (T : Subgroup G).characteristicNormalizerClosure ≤ minimalParabolicMax T hP := by
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro A hA hne
  let := hA
  have hn : normalizer (A.map (T : Subgroup G).subtype : Set G) ≠ ⊤ := by
    intro h
    exact hno A hA hne (normalizer_eq_top_iff.mp h)
  obtain ⟨M,hM,hNM⟩ := (eq_top_or_exists_le_coatom _).resolve_left hn
  have hTN : (T : Subgroup G) ≤ normalizer (A.map (T : Subgroup G).subtype : Set G) := by
    have := A.normal_of_characteristic
    exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le A)).mp (by
      simpa only [subgroupOf,comap_map_eq_self_of_injective (T : Subgroup G).subtype_injective]
        using (inferInstance : A.Normal))
  exact hNM.trans_eq (minimalParabolicMax_unique T hP hM (hTN.trans hNM))

/-- The complete central-product orbit, including literal two-residual
generation and movement by the original Thompson subgroup. -/
theorem residual_chiZero_orbit_of_characteristic_exclusion
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hno : ∀ A : Subgroup T, A.Characteristic → A ≠ ⊥ →
      ¬ (A.map (T : Subgroup G).subtype).Normal) :
    ∃ F : Set (Subgroup G), F.Nonempty ∧
      (∀ K ∈ F, IsChiZeroBlockIn K) ∧ sSup F = pResidual 2 G ∧
      F.Pairwise (fun K L => ⁅K,L⁆ = ⊥) ∧
      (∀ K ∈ F, ∀ t : T, K.map (MulAut.conj (t : G)).toMonoidHom ∈ F) ∧
      (∀ K ∈ F, ∀ L ∈ F, ∃ t : T, K.map (MulAut.conj (t : G)).toMonoidHom = L) ∧
      ∀ K ∈ F, K = ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  classical
  let M := minimalParabolicMax T hP
  have hM : M ≠ ⊤ := (minimalParabolicMax_spec T hP).1.1
  have hcpu := control_le_maximal_of_characteristic_exclusion T hP hno
  obtain ⟨r,_,L,hL,hout,hm,hprod⟩ := SelectedRankOne.ordered_chiZero_product_knownSimple hG hf T M hcpu
  have hr : 0 < r := by
    by_contra! hn
    have he : r = 0 := by omega
    subst r
    apply hM
    apply top_unique
    intro g _
    obtain ⟨m,b,hg⟩ := hprod g
    simp only [List.ofFn_zero,List.prod_nil,mul_one] at hg
    exact hg.symm ▸ m.property
  let K := L ⟨0,hr⟩
  have hb : IsChiZeroBlockIn K := hL _
  have ho : ¬ K ≤ M := hout _
  have hmove : K = ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ := hm _
  have hgen : K ⊔ (T : Subgroup G) = ⊤ := by
    by_contra hn
    obtain ⟨N,hN,hKN⟩ := (eq_top_or_exists_le_coatom _).resolve_left hn
    have he : N = M := minimalParabolicMax_unique T hP hN (le_sup_right.trans hKN)
    exact ho (le_sup_left.trans (hKN.trans_eq he))
  let X := conjugateSpanBy K (T : Subgroup G)
  let : X.Normal := conjugateSpanBy_sylow_normal K T
    (normal_or_index_two hf (hG.stronglyQuasithin 3 Nat.prime_three (by decide)) hb.chi)
  have hXT : X ⊔ (T : Subgroup G) = ⊤ := top_unique (hgen ▸ sup_le_sup (le_conjugateSpanBy K _) le_rfl)
  have hX : X = pResidual 2 G := by
    apply le_antisymm
    · exact conjugateSpanBy_le (le_pResidual_of_isPPerfect K hb.1.short.twoPerfect) le_normalizer_of_normal
    · exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top X (T : Subgroup G) T.isPGroup' hXT⟩
  let F : Set (Subgroup G) := Set.range (fun t : T => K.conjBy (t : G))
  have hblocks : ∀ A ∈ F, IsChiZeroBlockIn A := by
    rintro A ⟨t,rfl⟩
    exact ⟨hb.1.map_equiv (MulAut.conj (t : G)),
      hb.2.of_mulEquiv ((MulAut.conj (t : G)).subgroupMap K)⟩
  refine ⟨F,⟨K,⟨1,by simp [Subgroup.conjBy_one]⟩⟩,hblocks,?_,?_,?_,?_,?_⟩
  · rw [sSup_range]
    exact (conjugateSpanBy_eq_iSup_conj K (T : Subgroup G)).symm.trans hX
  · intro A hA B hB hne
    exact blocks_commute (blockCommutationHypothesis_of_fitting hf) (hblocks A hA).1 (hblocks B hB).1 hne
  · rintro A ⟨s,rfl⟩ t
    refine ⟨t*s,?_⟩
    exact (conjBy_conjBy K (s : G) (t : G)).symm
  · rintro A ⟨s,rfl⟩ B ⟨t,rfl⟩
    refine ⟨t*s⁻¹,?_⟩
    change (K.conjBy (s : G)).conjBy ((t : G)*(s : G)⁻¹) = K.conjBy (t : G)
    rw [conjBy_conjBy,inv_mul_cancel_right]
  · rintro A ⟨t,rfl⟩
    exact moved_conjugate (T : Subgroup G) hmove t
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
