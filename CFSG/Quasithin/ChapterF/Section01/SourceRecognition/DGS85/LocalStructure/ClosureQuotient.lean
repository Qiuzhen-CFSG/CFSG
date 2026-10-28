module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CoreClosure
public import Theory.GroupTheory.PCoreKernelRange

/-!
# Restriction to the actual adjacent-core closure

Restrict any original enlarged core quotient to X=<Q_delta^G_lambda>.
Its kernel is both O₂(X) and the literal intersection with Q_lambda,
because X is normal in the full neighboring endpoint. No surjectivity onto
the enlarged quotient is inferred. Original quotient representatives are
retained, including when the closure image is proper.

Source: DGS, Groups and Graphs (1985), 6.4, pp.120--121. The small
Suzuki and dihedral replacement argument consumes this restriction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G D : Type*} [Group G] [Group D]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Restrict the original enlarged quotient without assuming that the closure covers it. -/
theorem source_closure_quotient_restriction (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (q : localEnlargement d →* D)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ∃ f : X →* D, f.ker = pCore 2 X ∧
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
  exact ⟨f,hker.trans hcore,hker,fun x => ⟨inclusion hXJ x,rfl,rfl⟩⟩
end CFSG.Quasithin.ChapterF.Source.DGS85
