module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.BorelSource.Setup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction
public import Theory.GroupTheory.CComponent.QuotientLifting


/-!
# The invariant Borel of the actual starred component orbit

The source normalizer-index bound and two-perfectness force L₁ to normalize
K, even when T permutes its conjugates. The quotient C-component theorem
preserves the index bound, and the literal image of T is a Sylow subgroup
of H/O₂(H). Quasisimplicity turns K* into an ordinary component and
`starModelEquiv` supplies the genuine Suzuki matrix identification.

The previously proved intrinsic Suzuki orbit construction now supplies the
Borel containing T* ∩ K₀*, its L₁*T* invariance, and an equivalence carrying
the whole Borel to the product of one or two concrete Borels. The orbit is
never collapsed by assuming normality of K.

Source: Aschbacher–Smith, 13.8.16, printed pp.952–953, using 1.2.1(3)
and A.3; combined manuscript (1 March 2004).
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
variable {G : Type*} [Group G] [Finite G]

private theorem intrinsic_borel (K Y S : Subgroup G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = S) (hK : IsComponent G K) (m : ℕ) (hm : 0 < m)
    (e : K ≃* SuzukiMatrixGroup m) (hSY : S ≤ normalizer (Y : Set G))
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hYK : Y ≤ normalizer (K : Set G))
    (hindex : (normalizer (K : Set G)).index ≤ 2) :
    ∃ B : Subgroup G, B ≤ localSpan K S ∧ S ⊓ localSpan K S ≤ B ∧
      Y ⊔ S ≤ normalizer (B : Set G) ∧
      ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ ∃ f : localSpan K S ≃* (Fin n → SuzukiMatrixGroup m),
        (B.subgroupOf (localSpan K S)).map f.toMonoidHom =
          pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
  let Ptop : Sylow 2 (⊤ : Subgroup G) := P.mapSurjective (f := (topEquiv (G := G)).symm.toMonoidHom)
    (topEquiv (G := G)).symm.surjective
  have hPtop : (Ptop : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = S := by
    change ((P : Subgroup G).map (topEquiv (G := G)).symm.toMonoidHom).map
      (⊤ : Subgroup G).subtype = S
    rw [map_map]
    change (P : Subgroup G).map (MonoidHom.id G) = S
    rwa [map_id]
  have hI : (normalizer (K.subgroupOf ⊤ : Set (⊤ : Subgroup G))).index ≤ 2 := by
    rw [← subgroupOf_normalizer_eq (show K ≤ ⊤ from le_top)]
    rw [subgroupOf, index_comap_of_surjective _ (topEquiv (G := G)).surjective]
    exact hindex
  obtain ⟨_, hcontains, hle, hn⟩ := suzuki_orbit_normalizer_invariance
    (I := ⊤) le_top le_top Ptop hPtop (hK.subgroupOf le_top) m hm e hSY hY hYK
  obtain ⟨n, hn', f, hf⟩ := BorelConstruction.orbitNormalizer_model
    (I := ⊤) le_top Ptop hPtop (hK.subgroupOf le_top) m hm e hI
  exact ⟨BorelConstruction.orbitNormalizer K S, hle, hcontains, hn, n, hn', f, hf⟩

omit [Finite G] in
private theorem starImage_orbit (H K T : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H) :
    Source.starImage H (conjugateSpanBy K T) =
      localSpan (Source.starImage H K) (Source.starImage H T) := by
  have hO : conjugateSpanBy K T ≤ H := conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have he : (conjugateSpanBy K T).subgroupOf H =
      conjugateSpanBy (K.subgroupOf H) (T.subgroupOf H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hO, map_conjugateSpan,
      map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hTH]
  rw [Source.starImage, he, map_conjugateSpan]
  rfl

omit [Finite G] in
private theorem normalizes_orbit {K Y T : Subgroup G}
    (hTY : T ≤ normalizer (Y : Set G)) (hYK : Y ≤ normalizer (K : Set G)) :
    Y ≤ normalizer (conjugateSpanBy K T : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro y hy x ⟨t, ht, k, hk, rfl⟩
  have hy' : t⁻¹ * y * t ∈ Y := by
    simpa only [inv_inv] using le_normalizer_iff.mp hTY t⁻¹ (T.inv_mem ht) y hy
  have hk' := le_normalizer_iff.mp hYK _ hy' k hk
  apply Subgroup.subset_closure
  refine ⟨t, ht, (t⁻¹ * y * t) * k * (t⁻¹ * y * t)⁻¹, hk', ?_⟩
  group

variable {H K L₁ T G₁ M : Subgroup G} {m : ℕ}

theorem exists_invariantBorel (d : Earlier H K L₁ T G₁ M m) :
    Nonempty (InvariantBorel H K L₁ T m) := by
  have hLH : L₁ ≤ H := le_sup_left.trans d.base_le
  have hTH : T ≤ H := le_sup_right.trans d.base_le
  have hLK : L₁ ≤ normalizer (K : Set G) := by
    apply ComponentIntersection.normalizes_of_index_le_two hLH d.twoPerfect
    change ((normalizer (K : Set G)).subgroupOf H).index ≤ 2
    rw [subgroupOf_normalizer_eq d.component_le]
    exact d.component_index
  have horbit := starImage_orbit H K T d.component_le hTH
  let K' := Source.starImage H K
  let Y' := Source.starImage H L₁
  let S' := Source.starImage H T
  let q := QuotientGroup.mk' (pCore 2 H)
  let P := d.sylow.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hP : (P : Subgroup (Source.Hstar H)) = S' := by
    change (d.sylow : Subgroup H).map q = (T.subgroupOf H).map q
    congr 1
    apply map_injective H.subtype_injective
    rw [d.sylow_eq, map_subgroupOf_eq_of_le hTH]
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hindex : (normalizer (K' : Set (Source.Hstar H))).index ≤ 2 := by
    change (normalizer ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) : Set (Source.Hstar H))).index ≤ 2
    rw [cComponent_normalizer_index_quotient d.component (pCore 2 H)]
    exact d.component_index
  have hcomponent : IsComponent (Source.Hstar H) K' :=
    ⟨(starImage_isCComponent H K d.component).subnormal, d.star_quasisimple⟩
  obtain ⟨B, hB, hcontains, hn, n, hn', e, he⟩ := intrinsic_borel K' Y' S' P hP
    hcomponent m d.parameter_pos (starModelEquiv H K d.component_le d.component m d.model)
    (starImage_normalizes H L₁ T d.sylow_normalizes)
    (starImage_three_quotient H L₁ hLH d.three_quotient)
    (starImage_normalizes H K L₁ hLK) hindex
  have hsup : Source.starImage H (L₁ ⊔ T) = Y' ⊔ S' := by
    rw [Source.starImage, subgroupOf_sup hLH hTH, Subgroup.map_sup]
    rfl
  have hmodel : ∃ f : Source.starImage H (conjugateSpanBy K T) ≃*
      (Fin n → SuzukiMatrixGroup m),
      (B.subgroupOf (Source.starImage H (conjugateSpanBy K T))).map f.toMonoidHom =
        pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
    rw [horbit]
    exact ⟨e, he⟩
  obtain ⟨f, hf⟩ := hmodel
  exact ⟨{
    borel := B
    le_orbit := horbit.symm ▸ hB
    contains_sylow := horbit.symm ▸ hcontains
    orbit_normalized := sup_le (normalizes_orbit d.sylow_normalizes hLK)
      (le_normalizer_conjugateSpanBy K T)
    normalized := hsup.symm ▸ hn
    factors := n
    factors_one_or_two := hn'
    equiv := f
    borel_map := hf }⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.BorelSource
