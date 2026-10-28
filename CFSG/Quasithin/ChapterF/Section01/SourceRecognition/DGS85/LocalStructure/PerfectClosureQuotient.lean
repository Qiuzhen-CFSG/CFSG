module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CoreClosure
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# The adjacent-core closure over a perfect local quotient

The contrary-normality closure contains the two-residual of the enlarged
endpoint. A perfect quotient is its own two-residual, so restriction of
the original quotient map is surjective. Relative normality identifies
its kernel with both O₂(X) and X intersect Q_lambda. This applies to
special-unitary central covers without discarding their scalar center.

Source: DGS, Groups and Graphs (1985), 6.2(a) and 6.4, pp.119--121.
The special-unitary replacement exclusion is the consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G D : Type*} [Group G] [Group D] [Group.IsPerfect D]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Restrict the original enlarged perfect quotient to the literal opposite-core closure. -/
theorem source_perfect_closure_quotient (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* D) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ∃ f : X →* D, Function.Surjective f ∧ f.ker = pCore 2 X ∧
      f.ker = ((P (other i)).pCoreIn 2).subgroupOf X ∧
      ∀ x : X, ∃ y : localEnlargement d, (y : G) = (x : G) ∧ f x = q y := by
  let J := localEnlargement d
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hBP : B ≤ P (other i) := le_sup_right.trans d.supplement.le
  let := d.finite_P
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  have hQJ : (P i).pCoreIn 2 ≤ J := (pGroup_le_core_of_core_sylow B _
    (source_core_le_borel (Classical.choice (h.local_data i))) (isPGroup_pCoreIn 2 _) hB).trans le_sup_right
  have hXJ : X ≤ J := conjugateSpanBy_le hQJ
    (localEnlargement_normalized d)
  have hXP : X ≤ P (other i) := hXJ.trans (localEnlargement_le d)
  let N := X.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((localEnlargement_le d).trans (le_normalizer_conjugateSpanBy _ _))
  let f : X →* D := q.comp (inclusion hXJ)
  have hker : f.ker = ((P (other i)).pCoreIn 2).subgroupOf X := by
    ext x
    change q (inclusion hXJ x) = 1 ↔ (x : G) ∈ (P (other i)).pCoreIn 2
    rw [←MonoidHom.mem_ker,hk]
    have he : (x : G) ∈ J.pCoreIn 2 ↔ inclusion hXJ x ∈ pCore 2 J := by
      constructor
      · rintro ⟨y,hy,he⟩
        exact (show y = inclusion hXJ x from Subtype.ext he) ▸ hy
      · intro hx
        exact mem_map_of_mem J.subtype hx
    rw [←he,localEnlargement_core d]
  have hcore : ((P (other i)).pCoreIn 2).subgroupOf X = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [subgroupOf_map_subtype]
    change (P (other i)).pCoreIn 2 ⊓ X = X.pCoreIn 2
    apply le_antisymm
    · rw [inf_comm]
      exact inf_pCoreIn_le_of_le 2 hXP
    · exact le_inf (pCoreIn_mono_of_normalizes hXP
        (le_normalizer_conjugateSpanBy _ _)) (pCoreIn_le 2 X)
  let : Finite J := Finite.of_injective (inclusion (localEnlargement_le d))
    (inclusion_injective _)
  let : Finite D := Finite.of_surjective q hq
  have hr := (core_closure_residual_of_inter_normal h hB i d hn).1
  have him : (pResidual 2 J).map q = ⊤ := by
    rw [map_pResidual_of_surjective 2 q hq,pResidual_eq_top_of_isPerfect 2]
  have honto : Function.Surjective f := by
    intro a
    obtain ⟨y,hy,hya⟩ := him.symm ▸ (mem_top a)
    exact ⟨⟨y,hr (mem_map_of_mem J.subtype hy)⟩,hya⟩
  exact ⟨f,honto,hker.trans hcore,hker,fun x => ⟨inclusion hXJ x,rfl,rfl⟩⟩
end CFSG.Quasithin.ChapterF.Source.DGS85
