module
public import Theory.SpecificGroups.SymmetricThreeSevenSylowNormalizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The symmetric action-quotient branch of C.5.12

Sylow two-subgroups of S₃ and S₇ are self-normalizing. In the literal
quotient X/C_X(V), the image of N_X(T) therefore lies in the image of T.
Its inverse image is T C_X(V), which normalizes U whenever U≤V and T
normalizes U. The final application keeps the actual source conjugate span.

Source: Aschbacher–Smith C.5.12, printed p.163, final paragraph.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]
/-- The symmetric quotient alternative yields the literal source normalizer bound. -/
theorem normalizer_control_of_symmetric_quotient
    (X T U V : Subgroup G) (hUV : U ≤ V) (hVX : V ≤ X)
    (hXV : X ≤ normalizer (V : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hmodel : let : (V.subgroupOf X).Normal :=
        (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
      Nonempty ((X ⧸ centralizer (V.subgroupOf X : Set X)) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((X ⧸ centralizer (V.subgroupOf X : Set X)) ≃* Equiv.Perm (Fin 7))) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U : Set G) := by
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let C := centralizer (V.subgroupOf X : Set X)
  let q := QuotientGroup.mk' C
  let P := S.mapSurjective (QuotientGroup.mk'_surjective C)
  have hP := SymmetricThreeSeven.sylow_normalizer_eq_self P hmodel
  have hm : (normalizer (S : Set X)).map q ≤ (S : Subgroup X).map q := by
    rw [← show normalizer (P : Set (X ⧸ C)) = (S : Subgroup X).map q from hP]
    exact (S : Subgroup X).le_normalizer_map q
  have hn : normalizer (S : Set X) ≤ (S : Subgroup X) ⊔ C := by
    have hh := map_le_iff_le_comap.mp hm
    rwa [comap_map_eq,QuotientGroup.ker_mk'] at hh
  have hTX : T ≤ X := hS ▸ map_subtype_le _
  have he : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hsup : ((S : Subgroup X) ⊔ C).map X.subtype ≤ normalizer (U : Set G) := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rwa [hS]
    · rintro _ ⟨c,hc,rfl⟩
      apply centralizer_le_normalizer (U : Set G)
      intro u hu
      exact congrArg X.subtype (hc ⟨u,hVX (hUV hu)⟩ (hUV hu))
  rintro g ⟨hgX,hgT⟩
  have hg : (⟨g,hgX⟩ : X) ∈ normalizer (S : Set X) := by
    change (⟨g,hgX⟩ : X) ∈ normalizer ((S : Subgroup X) : Set X)
    rw [← he,← subgroupOf_normalizer_eq hTX]
    exact hgT
  exact hsup (mem_map_of_mem X.subtype (hn hg))
open ConjugateSource.RankOne
/-- C.5.12 for the actual U-conjugate span used in C.5.10–11. Its
normalization is the previously proved source span result; the only
new alternative is the actual S₃ or S₇ quotient isomorphism. -/
theorem source_span_control_of_symmetric_quotient
    (K T N X : Subgroup G) (hKX : K ≤ X) (hNX : N ≤ X)
    (hTK : T ≤ normalizer (K : Set G))
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hXV : X ≤ normalizer (conjugateSpanBy (U K) N : Set G))
    (hmodel : let : ((conjugateSpanBy (U K) N).subgroupOf X).Normal :=
        normal_subgroupOf_of_le_normalizer hXV
      Nonempty ((X ⧸ centralizer ((conjugateSpanBy (U K) N).subgroupOf X : Set X)) ≃*
        Equiv.Perm (Fin 3)) ∨
      Nonempty ((X ⧸ centralizer ((conjugateSpanBy (U K) N).subgroupOf X : Set X)) ≃*
        Equiv.Perm (Fin 7))) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  have hUX : U K ≤ X := (map_subtype_le _).trans hKX
  have hVX : conjugateSpanBy (U K) N ≤ X :=
    conjugateSpanBy_le hUX (hNX.trans X.le_normalizer)
  exact normalizer_control_of_symmetric_quotient X T (U K) (conjugateSpanBy (U K) N)
    (le_conjugateSpanBy _ _) hVX hXV
    (hTK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))) S hS hmodel
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
