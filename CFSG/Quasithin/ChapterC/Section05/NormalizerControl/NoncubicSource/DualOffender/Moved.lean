module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Source
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
/-!
# The literal component image and its original moved module

The definitions retain the actual centralizer quotient, normal closure
of K, and subgroup commutator [V,L]. The map identities identify these
intrinsic constructions with the original ambient source L and I.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
variable {G : Type*} [Group G]
/-- A normal elementary section inside V, with the literal canonical action. -/
@[expose] noncomputable def canonicalSubrepresentation (V I : Subgroup G)
    [V.Normal] [I.Normal] [IsElementaryAbelian 2 V] :
    Subrepresentation (centralizerQuotient V) where
  toSubmodule := AddSubgroup.toZModSubmodule 2 (I.subgroupOf V).toAddSubgroup
  apply_mem_toSubmodule g := by
    intro w hw
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (V : Set G)) g
    change ((centralizerQuotient V (QuotientGroup.mk' _ a) w).toMul : G) ∈ I
    rw [centralizerQuotient_apply]
    exact (inferInstance : I.Normal).conj_mem _ hw a
/-- The actual conjugate span is normal in its specified actor. -/
theorem source_span_normal (K N : Subgroup G) (hKN : K ≤ N) :
    ((conjugateSpanBy K N).subgroupOf N).Normal :=
  (normal_subgroupOf_iff_le_normalizer (conjugateSpanBy_le_self hKN)).mpr
    (le_normalizer_conjugateSpanBy K N)
/-- The subrepresentation used below is exactly the original group commutator
I=[V,L], including the original ambient inclusions. -/
theorem moved_subrepresentation_map (V L N : Subgroup G)
    (hVN : V ≤ N) (hLN : L ≤ N) (hNV : N ≤ normalizer (V : Set G)) :
    ((⁅V.subgroupOf N,L.subgroupOf N⁆.subgroupOf (V.subgroupOf N)).map
      ((V.subgroupOf N).subtype)).map N.subtype = ⁅V,L⁆ := by
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hVN).mpr hNV
  rw [map_subgroupOf_eq_of_le (commutator_le_left _ _),map_commutator,
    map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hLN]

/-- The literal image of the normal conjugate span in the canonical quotient. -/
@[expose] noncomputable def closureImage (V K : Subgroup G) [V.Normal] :
    Subgroup (G ⧸ centralizer (V : Set G)) :=
  (normalClosure (K : Set G)).map (QuotientGroup.mk' (centralizer (V : Set G)))
/-- The original moved subgroup [V,⟨K^G⟩] as an invariant binary subspace. -/
@[expose] noncomputable def movedSpace (V K : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] : Subrepresentation (centralizerQuotient V) :=
  canonicalSubrepresentation V ⁅V,normalClosure (K : Set G)⁆
/-- Restriction to the literal image of L on its original moved module I. -/
@[expose] noncomputable def movedRepresentation (V K : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] :
    Representation (ZMod 2) (closureImage V K) (movedSpace V K).toSubmodule :=
  (movedSpace V K).toRepresentation.comp (closureImage V K).subtype
/-- Relative normal closure is exactly the source subgroup L=⟨K^N⟩. -/
theorem source_closure_map (K N : Subgroup G) (hKN : K ≤ N) :
    (normalClosure (K.subgroupOf N : Set N)).map N.subtype = conjugateSpanBy K N := by
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy K N hKN,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hKN)]
/-- The moved subgroup in the representation is exactly the source I=[V,L]. -/
theorem source_moved_map (V K N : Subgroup G) (hVN : V ≤ N) (hKN : K ≤ N) :
    ⁅V.subgroupOf N,normalClosure (K.subgroupOf N : Set N)⁆.map N.subtype =
      ⁅V,conjugateSpanBy K N⁆ := by
  rw [map_commutator,map_subgroupOf_eq_of_le hVN,source_closure_map K N hKN]
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
