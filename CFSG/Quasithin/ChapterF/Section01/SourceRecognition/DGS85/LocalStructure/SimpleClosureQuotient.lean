module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CoreClosure
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The actual adjacent-core closure over a simple local quotient

The full neighboring endpoint normalizes X=<Q_delta^G_lambda>. Under the
contrary intersection-normality assumption, Q_delta escapes Q_lambda.
Consequently X has nontrivial normal image in a simple enlarged quotient,
and covers that quotient. Restriction retains the literal quotient map;
its kernel is both O₂(X) and X intersect Q_lambda. The proof uses relative
normality and only finiteness of the endpoint, not of the completion.

This supplies the simple-model kernel input for the replacement argument
in DGS, Groups and Graphs (1985), 6.4, printed pp.120--121. It makes no
Sylow assertion about Q_delta.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G D : Type*} [Group G] [Group D] [IsSimpleGroup D]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Restrict the original enlarged simple quotient to the literal opposite-core closure. -/
theorem source_simple_closure_quotient (h : LocallyRankOneTriple P B)
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
  have hr : f.range = N.map q := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨inclusion hXJ x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  let : (N.map q).Normal := (inferInstance : N.Normal).map q hq
  have hrne : N.map q ≠ ⊥ := by
    intro he
    have hfk : f.ker = ⊤ := by
      apply top_unique
      intro x _
      exact mem_bot.mp (he ▸ (hr ▸ (show f x ∈ f.range from ⟨x,rfl⟩)))
    apply core_not_le_of_inter_normal h i hn
    intro x hx
    have hxk : (⟨x,le_conjugateSpanBy _ _ hx⟩ : X) ∈ f.ker := by
      rw [hfk]
      exact mem_top _
    change (⟨x,le_conjugateSpanBy _ _ hx⟩ : X) ∈ ((P (other i)).pCoreIn 2).subgroupOf X
    rwa [←hker]
  have honto : Function.Surjective f := MonoidHom.range_eq_top.mp
    (hr.trans ((inferInstance : (N.map q).Normal).eq_bot_or_eq_top.resolve_left hrne))
  exact ⟨f,honto,hker.trans hcore,hker,fun x => ⟨inclusion hXJ x,rfl,rfl⟩⟩
end CFSG.Quasithin.ChapterF.Source.DGS85
