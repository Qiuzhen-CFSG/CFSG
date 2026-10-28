module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.PCoreRestriction
/-!
# Literal quotient and Sylow data for the C.5.13 restriction comparison

The original two-core of KT is normal in the auxiliary N. Restricting this
core to the normal span L proves the exact K-to-L quotient kernel. The source
commutator identity places U(K) in U(L). Finally the original full Sylow subgroup
restricts to L and continues to normalize K. None of the finite placement or
module conclusions is assumed.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem source_matching_data (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let L := conjugateSpanBy K N
    ∃ hKL : K ≤ L,
      ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hKL)).ker = pCore 2 K ∧
      U K ≤ U L ∧
      ∃ Q : Sylow 2 L, (Q : Subgroup L) ≤ normalizer (K.subgroupOf L : Set L) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  have hKL : K ≤ L := le_conjugateSpanBy K N
  have hUK := DualOffender.noncubic_source_moved_core K T X hK h3 hT hUT hTK P hP hA hAX S hS
  have hUL : U K ≤ U L := hUK.1.trans_eq hUK.2.2.2.2
  have hKNcore : K.pCoreIn 2 ≤ N.pCoreIn 2 :=
    (pCoreIn_mono_of_normalizes (show K ≤ A from le_sup_left)
      (sup_le K.le_normalizer hTK)).trans
      (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A)
        ((pCoreIn_le 2 A).trans hAN) inf_le_right)
  have hKLcore : K.pCoreIn 2 ≤ L.pCoreIn 2 :=
    (le_inf ((pCoreIn_le 2 K).trans hKL) hKNcore).trans
      (inf_pCoreIn_le_of_le 2 hLN)
  have hk : ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hKL)).ker = pCore 2 K := by
    apply le_antisymm
    · have he : ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hKL)).ker =
          (pCore 2 L).comap (inclusion hKL) := by
        ext k
        exact QuotientGroup.eq_one_iff (inclusion hKL k)
      rw [he]
      have hp : IsPGroup 2 ((pCore 2 L).comap (inclusion hKL)) :=
        pCore_isPGroup.comap_of_injective _ (inclusion_injective hKL)
      exact le_sSup ⟨inferInstance,hp⟩
    · intro k hk
      have hh := hKLcore (mem_map_of_mem K.subtype hk)
      obtain ⟨l,hl,he⟩ := hh
      apply (QuotientGroup.eq_one_iff _).mpr
      exact (Subtype.ext he : l=inclusion hKL k) ▸ hl
  obtain ⟨Q,hQ⟩ := (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS).2.2
  let : (L.subgroupOf N).Normal := DualOffender.source_span_normal K N hKN
  obtain ⟨R,hR⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (show Chapter1.IsSylowIn 2 T N from ⟨Q,hQ⟩) hLN
    (inferInstance : (L.subgroupOf N).Normal).isSubnormal
  refine ⟨hKL,hk,hUL,R,?_⟩
  intro l hl
  have ht : (l : G) ∈ T := (hR ▸ mem_map_of_mem L.subtype hl).1
  rw [← subgroupOf_normalizer_eq hKL]
  exact hTK ht
theorem exists_quotient_sylow_normalizing {K L : Subgroup G} (hKL : K ≤ L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (P : Sylow 2 L) (hP : (P : Subgroup L) ≤ normalizer (K.subgroupOf L : Set L)) :
    ∃ S : Sylow 2 (alternatingGroup (Fin 7)),
      (S : Subgroup _) ≤ normalizer
      ((e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hKL))).range :
        Set (alternatingGroup (Fin 7))) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  refine ⟨S,?_⟩
  have he : (K.subgroupOf L).map f = (f.comp (inclusion hKL)).range := by
    ext x
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l.val,hl⟩,rfl⟩
    · rintro ⟨k,rfl⟩
      exact ⟨inclusion hKL k,k.property,rfl⟩
  change (P : Subgroup L).map f ≤ _
  have hh := (map_mono (f := f) hP).trans (le_normalizer_map _)
  rw [he] at hh
  exact hh

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.Matching
