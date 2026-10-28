module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.TrioGeometry
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups.TrioCore
/-!
# The native trio stabilizer normalizes the elementary candidate

The certified transporter sends the 64 row-20 words to precisely the
translations whose three binary vectors sum to zero. Every element of the
actual trio stabilizer has a common affine linear part. Conjugation permutes
the three translation vectors and applies this common linear map, preserving
their zero sum. Thus the whole trio stabilizer normalizes the literal native
six-generator elementary candidate. Rows 20 and 21 are also identified
with the two candidates directly from their closure definitions.

Source: GLS3 Table 5.3e; Aschbacher--Smith 15.3.41--42, printed p.1138;
Aschbacher, *Sporadic Groups*, Lemma 20.2, for the existing affine coordinates.
-/
@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
open PairOvergroups.QuotientConstruction
open SylowNormalizer.OrderEnumeration
/-- The translations of the 64 certified words of the trio elementary subgroup. -/
def translationTable : Table (Fin 3 → Vector) 6 :=
  ((((((![![0,0,0],![0,0,0],![0,0,0]], ![![0,1,1],![1,1,1],![1,0,0]]), (![![0,1,0],![0,1,1],![0,0,1]], ![![0,0,1],![1,0,0],![1,0,1]])), ((![![0,0,0],![1,0,0],![1,0,0]], ![![0,1,1],![0,1,1],![0,0,0]]), (![![0,1,0],![1,1,1],![1,0,1]], ![![0,0,1],![0,0,0],![0,0,1]]))), (((![![0,1,0],![0,1,0],![0,0,0]], ![![0,0,1],![1,0,1],![1,0,0]]), (![![0,0,0],![0,0,1],![0,0,1]], ![![0,1,1],![1,1,0],![1,0,1]])), ((![![0,1,0],![1,1,0],![1,0,0]], ![![0,0,1],![0,0,1],![0,0,0]]), (![![0,0,0],![1,0,1],![1,0,1]], ![![0,1,1],![0,1,0],![0,0,1]])))), ((((![![1,1,1],![0,0,0],![1,1,1]], ![![1,0,0],![1,1,1],![0,1,1]]), (![![1,0,1],![0,1,1],![1,1,0]], ![![1,1,0],![1,0,0],![0,1,0]])), ((![![1,1,1],![1,0,0],![0,1,1]], ![![1,0,0],![0,1,1],![1,1,1]]), (![![1,0,1],![1,1,1],![0,1,0]], ![![1,1,0],![0,0,0],![1,1,0]]))), (((![![1,0,1],![0,1,0],![1,1,1]], ![![1,1,0],![1,0,1],![0,1,1]]), (![![1,1,1],![0,0,1],![1,1,0]], ![![1,0,0],![1,1,0],![0,1,0]])), ((![![1,0,1],![1,1,0],![0,1,1]], ![![1,1,0],![0,0,1],![1,1,1]]), (![![1,1,1],![1,0,1],![0,1,0]], ![![1,0,0],![0,1,0],![1,1,0]]))))), (((((![![1,1,1],![1,1,1],![0,0,0]], ![![1,0,0],![0,0,0],![1,0,0]]), (![![1,0,1],![1,0,0],![0,0,1]], ![![1,1,0],![0,1,1],![1,0,1]])), ((![![1,1,1],![0,1,1],![1,0,0]], ![![1,0,0],![1,0,0],![0,0,0]]), (![![1,0,1],![0,0,0],![1,0,1]], ![![1,1,0],![1,1,1],![0,0,1]]))), (((![![1,0,1],![1,0,1],![0,0,0]], ![![1,1,0],![0,1,0],![1,0,0]]), (![![1,1,1],![1,1,0],![0,0,1]], ![![1,0,0],![0,0,1],![1,0,1]])), ((![![1,0,1],![0,0,1],![1,0,0]], ![![1,1,0],![1,1,0],![0,0,0]]), (![![1,1,1],![0,1,0],![1,0,1]], ![![1,0,0],![1,0,1],![0,0,1]])))), ((((![![0,0,0],![1,1,1],![1,1,1]], ![![0,1,1],![0,0,0],![0,1,1]]), (![![0,1,0],![1,0,0],![1,1,0]], ![![0,0,1],![0,1,1],![0,1,0]])), ((![![0,0,0],![0,1,1],![0,1,1]], ![![0,1,1],![1,0,0],![1,1,1]]), (![![0,1,0],![0,0,0],![0,1,0]], ![![0,0,1],![1,1,1],![1,1,0]]))), (((![![0,1,0],![1,0,1],![1,1,1]], ![![0,0,1],![0,1,0],![0,1,1]]), (![![0,0,0],![1,1,0],![1,1,0]], ![![0,1,1],![0,0,1],![0,1,0]])), ((![![0,1,0],![0,0,1],![0,1,1]], ![![0,0,1],![1,1,0],![1,1,1]]), (![![0,0,0],![0,1,0],![0,1,0]], ![![0,1,1],![1,0,1],![1,1,0]]))))))
def translation (j : Fin 64) : Fin 3 → Vector := lookup 6 translationTable j.val
end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
open Subgroup PairOvergroups PairOvergroups.QuotientConstruction
open scoped Pointwise
set_option maxRecDepth 100000

/-- The two final rows are literally the existing six-generator elementary groups. -/
theorem last_ambient (k : Fin 2) : ambient (if k = 0 then 20 else 21) = EvenCandidates.elementary k := by
  rw [ambient, subgroup, MonoidHom.map_closure, ← Set.range_comp]
  unfold EvenCandidates.elementary
  apply congrArg closure
  apply congrArg Set.range
  funext j
  have h : ∀ (k : Fin 2) (j : Fin 6),
      generatorIndex (if k = 0 then 20 else 21) j = EvenCandidates.generatorIndex k j := by
    decide +kernel
  change (SylowNormalizer.OrderEnumeration.element
    (generatorIndex (if k = 0 then 20 else 21) j)).val = _
  rw [h]
  rfl

noncomputable def transported (a : M24) : M24 :=
  (MulAut.conj (FourNormalizers.certificateElement 0)) a

def HasTranslation (a : M24) (t : Fin 3 → Vector) : Prop :=
  ∀ (i : Fin 3) (v : Vector), (transported a).val (QuotientConstruction.point (i,v)) =
    QuotientConstruction.point (i, v + t i)

private theorem translation_zero : ∀ j : Fin 64,
    translation j 0 + translation j 1 + translation j 2 = 0 := by decide +kernel

private theorem translation_cover : ∀ t : Fin 3 → Vector,
    t 0 + t 1 + t 2 = 0 → ∃ j : Fin 64, translation j = t := by decide +kernel

private theorem translation_action_check : ∀ (j : Fin 64) (i : Fin 3) (v : Vector),
    FourNormalizers.certificatePerm 0
      (point (rowCode 20 j)
        ((FourNormalizers.certificatePerm 0).symm (QuotientConstruction.point (i,v)))) =
          QuotientConstruction.point (i, v + translation j i) := by decide +kernel

theorem row20_translation (j : Fin 64) : HasTranslation (rowElement 20 j) (translation j) := by
  intro i v
  change FourNormalizers.certificatePerm 0
    ((rowElement 20 j).val
      ((FourNormalizers.certificatePerm 0).symm (QuotientConstruction.point (i,v)))) = _
  rw [rowElement_apply]
  exact translation_action_check j i v

private theorem translated_ext (a b : M24) {t : Fin 3 → Vector}
    (ha : HasTranslation a t) (hb : HasTranslation b t) : a = b := by
  apply (MulAut.conj (FourNormalizers.certificateElement 0)).injective
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,v⟩, rfl⟩ := QuotientConstruction.point.surjective x
  exact (ha i v).trans (hb i v).symm

/-- The elementary candidate consists of exactly the native zero-sum translations. -/
theorem mem_elementary_zero_iff (a : M24) :
    a ∈ EvenCandidates.elementary 0 ↔
      ∃ t : Fin 3 → Vector, t 0 + t 1 + t 2 = 0 ∧ HasTranslation a t := by
  rw [← last_ambient 0]
  change a ∈ ambient 20 ↔ _
  rw [mem_ambient_iff]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨translation j, translation_zero j, row20_translation j⟩
  · rintro ⟨t, ht, ha⟩
    obtain ⟨j, rfl⟩ := translation_cover t ht
    exact ⟨j, translated_ext _ _ (row20_translation j) ha⟩

private theorem sum_permuted (s : Equiv.Perm (Fin 3)) (t : Fin 3 → Vector) :
    t (s 0) + t (s 1) + t (s 2) = t 0 + t 1 + t 2 := by
  revert s t
  decide +kernel

private theorem conjugate_elementary_mem (g : M24) (hg : g ∈ trioGroup)
    (a : M24) (ha : a ∈ EvenCandidates.elementary 0) :
    g * a * g⁻¹ ∈ EvenCandidates.elementary 0 := by
  obtain ⟨t, ht, ha⟩ := (mem_elementary_zero_iff a).mp ha
  let g' : FourNormalizers.trioGroup := ⟨g, hg⟩
  obtain ⟨q, u, hq⟩ := affineCoverage (FourNormalizers.trioEquiv g')
  have hgform (i : Fin 3) (v : Vector) :
      (transported g).val (QuotientConstruction.point (i,v)) =
      QuotientConstruction.point (q.1 i, Matrix.SpecialLinearGroup.toLin' q.2 v + u i) := by
    have h := hq i v
    rw [FourNormalizers.trioEquiv_apply] at h
    exact h
  let L := Matrix.SpecialLinearGroup.toLin' q.2
  let t' : Fin 3 → Vector := fun i => L (t (q.1.symm i))
  have ht' : t' 0 + t' 1 + t' 2 = 0 := by
    change L (t (q.1.symm 0)) + L (t (q.1.symm 1)) + L (t (q.1.symm 2)) = 0
    rw [← map_add, ← map_add, sum_permuted, ht, map_zero]
  obtain ⟨j, hj⟩ := translation_cover t' ht'
  let b := rowElement 20 j
  have hb : HasTranslation b t' := hj ▸ row20_translation j
  have he : g * a = b * g := by
    apply (MulAut.conj (FourNormalizers.certificateElement 0)).injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨⟨i,v⟩, rfl⟩ := QuotientConstruction.point.surjective x
    change (transported g).val ((transported a).val (QuotientConstruction.point (i,v))) =
      (transported b).val ((transported g).val (QuotientConstruction.point (i,v)))
    rw [ha, hgform, hgform, hb]
    apply congrArg QuotientConstruction.point
    refine Prod.ext rfl ?_
    change L (v + t i) + u i = (L v + u i) + L (t (q.1.symm (q.1 i)))
    rw [q.1.symm_apply_apply, map_add]
    ac_rfl
  rw [he, mul_inv_cancel_right]
  exact (mem_elementary_zero_iff b).mpr ⟨t', ht', hb⟩

/-- Every native stabilizer of this trio normalizes the actual elementary candidate. -/
theorem trio_le_elementary_normalizer : trioGroup ≤ EvenCandidates.localGroup 0 := by
  intro g hg
  apply mem_set_normalizer_iff.mpr
  intro a
  constructor
  · exact conjugate_elementary_mem g hg a
  · intro ha
    have h := conjugate_elementary_mem g⁻¹ ((trioGroup).inv_mem hg) _ ha
    simpa [mul_assoc] using h

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
