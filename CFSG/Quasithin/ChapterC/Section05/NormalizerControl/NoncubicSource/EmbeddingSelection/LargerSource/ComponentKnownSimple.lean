module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceComponentKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.FullSpanKernel

/-!
# The original larger-span components from unique source containment

The proved auxiliary C-component puts the original normalizer span in the
larger local family. Known-simple unique containment and the two-orbit bound
then give a normal containing C-component in X. Normal generation identifies
that component with the actual conjugate span of K under X.

These are the structural inputs for the later X/O₂(X) embedding analysis.
No assertion of its proper embedding list or Sylow faithfulness is used.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163, using 1.2.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_larger_local_family_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    L ∈ Chapter1.LIn X T ∧ T ≤ normalizer (L : Set G) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  have hfamily := noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q,hQ⟩ := hfamily.2.2
  have hcore : A.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAN) inf_le_right
  have hNH : N ∈ Chapter1.H G := by
    intro he
    exact hfamily.1.2.2.2 (bot_unique (hcore.trans he.le))
  have hcomp := noncubic_source_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  exact ⟨⟨hLN.trans inf_le_left,Chapter1.mem_L_of_cComponent hNH ⟨Q,hQ⟩ hLN hcomp⟩,
    (le_sup_right.trans hAN).trans (le_normalizer_conjugateSpanBy K N)⟩

theorem source_larger_quotient_sqtk_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  have hlocal := (source_larger_local_family_knownSimple hG K T X hK h3 hTK hAX hX S hS).1
  have hLX : L ≤ X := hlocal.1
  have hXH : X ∈ Chapter1.H G := by
    intro he
    have hXbot : X = ⊥ := by
      apply bot_unique
      have hh : X ⊓ centralizer (X.pCoreIn 2 : Set G) ≤ X.pCoreIn 2 := hX
      rw [he] at hh
      intro x hx
      apply hh
      refine ⟨hx, ?_⟩
      intro y hy
      have hy : y = 1 := hy
      simp only [hy,one_mul,mul_one]
    have hLbot : L = ⊥ := bot_unique (hLX.trans hXbot.le)
    have hsolv : Group.IsSolvable L := by rw [hLbot]; infer_instance
    exact Chapter1.mem_L_not_isSolvable hlocal.2 hsolv
  exact uniqueness_local_quotient_sqtk hG hXH

theorem source_larger_normal_component_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    ∃ D : Subgroup X, D.IsCComponent ∧ L.subgroupOf X ≤ D ∧
      (∀ E : Subgroup X, E.IsCComponent → L.subgroupOf X ≤ E → E = D) ∧
      D.Normal := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  obtain ⟨hlocal,hTL⟩ := source_larger_local_family_knownSimple hG K T X hK h3 hTK hAX hX S hS
  have hLX : L ≤ X := hlocal.1
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : L.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hLX).mp hlocal
  have hQX := source_larger_quotient_sqtk_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let := pCore_isNilpotent (p := 2) (G := X)
  obtain ⟨D, ⟨hD, hLD⟩, hu⟩ := lemma_1_2_4_containment_of_A_3_12
    (fun _ _ _ hY hO U B hB =>
      ChapterA.Section03.SourceComponents.containment_knownSimple hY hO U B hB) hQX S hmem
  have hnorm : D.Normal := by
    apply cComponent_normal_of_unique_of_orbit_two hD hLD
      (fun E hE hLE => hu E ⟨hE, hLE⟩) S
    · rw [← subgroupOf_normalizer_eq hLX]
      intro s hs
      exact hTL (hS ▸ mem_map_of_mem X.subtype hs)
    · apply cComponent_normal_or_index_two_of_quotient hD (pCore 2 X)
      exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
        (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
        hQX (pCore_quotient_pCore_eq_bot 2) (hD.map_quotient _)
  exact ⟨D, hD, hLD, (fun E hE hLE => hu E ⟨hE, hLE⟩), hnorm⟩


theorem source_larger_span_component_knownSimple {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    ((conjugateSpanBy K X).subgroupOf X).IsCComponent := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let D := conjugateSpanBy K X
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hDX : D ≤ X := conjugateSpanBy_le_self hKX
  obtain ⟨E,hE,hLE,_hu,hEn⟩ := source_larger_normal_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let : E.Normal := hEn
  have hKE : K.subgroupOf X ≤ E := (subgroupOf_mono X (le_conjugateSpanBy K N)).trans hLE
  have hnsolv : ¬ Group.IsSolvable (K.subgroupOf X) := by
    intro hs
    let : Group.IsSolvable (K.subgroupOf X) := hs
    have hh : Group.IsSolvable K := Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hKX).toMonoidHom) (subgroupOfEquivOfLe hKX).surjective
    exact Chapter1.mem_L_not_isSolvable
      (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS).1.2 hh
  have hspan := normal_span_eq_component (K.subgroupOf X) E hE hKE hnsolv
  have hEq : D.subgroupOf X = E := by
    apply map_injective X.subtype_injective
    rw [← hspan,map_conjugateSpanBy,map_subgroupOf_eq_of_le hKX,
      ← MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le hDX]
  change (D.subgroupOf X).IsCComponent
  rw [hEq]
  exact hE

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
