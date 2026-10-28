module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingOrbit
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment.KnownSimple

/-!
# The actual C.5.13 component without an embedding-list assumption

The full-catalogue containment theorem places the original noncubic block
in a unique C-component of its auxiliary normalizer. The source orbit bound
and the prescribed Sylow normalization make that component normal. Its
normal closure is therefore the actual conjugate span of the original block.
The ambient simple QTKE hypotheses supply the required SQTK quotient.

This constructs the component needed by the remaining model inspection,
independently of the proper-embedding list of A.3.12.
Source: Aschbacher–Smith C.5.13, printed p.162, using A.3.12 and 1.2.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Unique source containment and the two-orbit theorem identify the
component with the literal auxiliary conjugate span. -/
theorem noncubic_auxiliary_component_knownSimple
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T)
    (hQ : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    ((conjugateSpanBy K N).subgroupOf N).IsCComponent := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let := pCore_isNilpotent (p := 2) (G := N)
  obtain ⟨hlocal, _hN, ⟨S, hS⟩⟩ :=
    noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX P hP
  have hKN : K ≤ N := hlocal.1
  have hTN : T ≤ N := hS ▸ map_subtype_le _
  have hTs : T.subgroupOf N = (S : Subgroup N) := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hTN, hS]
  have hb : K.subgroupOf N ∈ Chapter1.L N (S : Subgroup N) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTN hKN).mp hlocal
  obtain ⟨D, ⟨hD, hKD⟩, hu⟩ := lemma_1_2_4_containment_of_A_3_12
    (fun _ _ _ hY hO U B hB =>
      ChapterA.Section03.SourceComponents.containment_knownSimple hY hO U B hB) hQ S hb
  have hnorm : D.Normal := by
    apply cComponent_normal_of_unique_of_orbit_two hD hKD
      (fun E hE hKE => hu E ⟨hE, hKE⟩) S
    · rw [← subgroupOf_normalizer_eq hKN]
      intro s hs
      exact hTK (hS ▸ mem_map_of_mem N.subtype hs)
    · apply cComponent_normal_or_index_two_of_quotient hD (pCore 2 N)
      exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
        (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
        hQ (pCore_quotient_pCore_eq_bot 2) (hD.map_quotient _)
  let := hnorm
  have hspan := normal_span_eq_component (K.subgroupOf N) D hD hKD
    (Chapter1.mem_L_not_isSolvable hb)
  have hm : (conjugateSpanBy (K.subgroupOf N) ⊤).map N.subtype = conjugateSpanBy K N := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hKN,
      ← MonoidHom.range_eq_map, range_subtype]
  have he : (conjugateSpanBy K N).subgroupOf N = D := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hKN), ← hm, hspan]
  change ((conjugateSpanBy K N).subgroupOf N).IsCComponent
  rw [he]
  exact hD

/-- The original QTKE domain discharges the auxiliary SQTK premise. -/
theorem noncubic_source_component_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    ((conjugateSpanBy K N).subgroupOf N).IsCComponent := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hlocal := (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX P hP).1
  have hcore : A.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAN) inf_le_right
  have hNH : N ∈ Chapter1.H G := by
    intro he
    exact hlocal.2.2.2 (bot_unique (hcore.trans he.le))
  exact noncubic_auxiliary_component_knownSimple K T X hK h3 hTK hAX hX P hP
    (uniqueness_local_quotient_sqtk hG hNH)

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
