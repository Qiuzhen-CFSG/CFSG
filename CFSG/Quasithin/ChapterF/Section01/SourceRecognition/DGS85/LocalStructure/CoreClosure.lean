module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalEnlargement
public import Theory.GroupTheory.SylowCenterFixedSpan
public import Theory.GroupTheory.AmalgamGraph.Centralizer
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# The exact adjacent-core closure in DGS 6.4

The enlarged local group and the full vertex stabilizer generate the same
normal closure of the opposite core. The Borel normalizes the intersection
of the two cores, so normality under the enlarged group is equivalent to
normality under the full stabilizer. This supplies the literal hypothesis
printed in 6.4, without strengthening it.

A common edge Sylow places its omega-center in the opposite core. Conjugating
this seed proves Z_lambda lies in the center omega of O_2(X), where
X = <Q_delta^{G_lambda}>. Under the contrary normality hypothesis, the
commutator of X with Q_lambda lies in Q_delta intersect Q_lambda. In
particular O_2(X) is central modulo that intersection. The reduced F1.11
applications retain the original completion inclusions.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.4(a) and the central-extension step, printed pp.120--121.
The Sylow and SL2 conclusions, and the 6.5 contradiction, remain separate
obligations; no quotient-recognition conclusion is assumed here.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem core_normalized (R : Subgroup G) :
    R ≤ normalizer (R.pCoreIn 2 : Set G) :=
  R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R))

private theorem borel_le (h : LocallyRankOneTriple P B) (i : Fin 2) : B ≤ P i :=
  le_sup_right.trans (Classical.choice (h.local_data i)).supplement.le

/-- The Chapter 6 local enlargement still supplements the full Borel. -/
theorem localEnlargement_sup_borel {R : Subgroup G} (d : LocalRankOneData R B) :
    localEnlargement d ⊔ B = R := by
  rw [localEnlargement, sup_assoc, sup_eq_right.mpr (pCoreIn_le 2 B), d.supplement]

/-- The full Borel normalizes the actual intersection of the endpoint cores. -/
theorem inter_core_normalized_by_borel (h : LocallyRankOneTriple P B) (i : Fin 2) :
    B ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) :=
  (le_inf ((borel_le h i).trans (core_normalized _))
    ((borel_le h (other i)).trans (core_normalized _))).trans inf_normalizer_le_normalizer_inf

/-- The normality assumption printed in 6.4 is equivalent to full-vertex normality. -/
theorem inter_core_local_normal_iff (h : LocallyRankOneTriple P B) (i : Fin 2)
    (d : LocalRankOneData (P (other i)) B) :
    localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) ↔
      P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G) := by
  constructor
  · intro hn
    exact (localEnlargement_sup_borel d).ge.trans
      (sup_le hn (inter_core_normalized_by_borel h i))
  · exact fun hn => (localEnlargement_le d).trans hn

/-- The enlarged and full stabilizers give the same literal opposite-core closure. -/
theorem core_closure_local_eq_full (h : LocallyRankOneTriple P B) (i : Fin 2)
    (d : LocalRankOneData (P (other i)) B) :
    conjugateSpanBy ((P i).pCoreIn 2) (localEnlargement d) =
      conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) := by
  have he := conjugateSpanBy_sup_of_normalizes_seed ((P i).pCoreIn 2) (localEnlargement d) B
    ((borel_le h i).trans (core_normalized _))
    ((borel_le h (other i)).trans (localEnlargement_normalized d))
  rw [localEnlargement_sup_borel d] at he
  exact he.symm

private theorem seed_le_core_of_between (R T : Subgroup G)
    (hTR : T ≤ R) (hQT : R.pCoreIn 2 ≤ T)
    (hc : centralizer (pCore 2 R : Set R) ≤ pCore 2 R) :
    omegaCenterIn T ≤ R.pCoreIn 2 := by
  intro z hz
  have hzT := (mem_omegaCenterIn_iff T z).mp hz
  have hzc : (⟨z, hTR hzT.1⟩ : R) ∈ centralizer (pCore 2 R : Set R) := by
    intro a ha
    apply Subtype.ext
    exact hzT.2.1 a (hQT (mem_map_of_mem R.subtype ha))
  exact mem_map_of_mem R.subtype (hc hzc)

/-- A common edge Sylow puts the second center span in the opposite-core closure. -/
theorem source_center_le_core_closure (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) :
    sylowCenterSpan (P (other i)) ≤ conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) := by
  let := (Classical.choice (h.local_data (other i))).finite_P
  let := (Classical.choice (h.local_data i)).finite_P
  obtain ⟨T, hT⟩ := hS (other i)
  obtain ⟨R, hR⟩ := hS i
  have hTS := sylow_image_eq_edge_core (P (other i)) B (borel_le h _) hB T hT
  have hRS := sylow_image_eq_edge_core (P i) B (borel_le h _) hB R hR
  rw [sylowCenterSpan_eq_conjugateSpan (P (other i)) (P (other i)) le_rfl
    (fun _ => map_subtype_le _) T]
  apply conjugateSpanBy_mono _ le_rfl
  apply seed_le_core_of_between (P i) _ (hT.trans (borel_le h i)) _
    (source_core_selfCentralizing (Classical.choice (h.local_data i)))
  rw [hTS, ← hRS]
  exact pCoreIn_le_sylow _ R

/-- The center-containment clause of 6.4(a), independent of its contrary normality assumption. -/
theorem source_center_le_closure_core_omega (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) :
    sylowCenterSpan (P (other i)) ≤
      omegaCenterIn ((conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).pCoreIn 2) := by
  let d := Classical.choice (h.local_data (other i))
  let := d.finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _))
  have hcore : X.pCoreIn 2 ≤ (P (other i)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hXP (le_normalizer_conjugateSpanBy _ _)
  have hZQ := sylowCenterSpan_le_coreOmega (P (other i)) (source_core_selfCentralizing d)
  have hZX : sylowCenterSpan (P (other i)) ≤ X := source_center_le_core_closure h hB hS i
  have hZXQ : sylowCenterSpan (P (other i)) ≤ X.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes _ hZX
      (hXP.trans ((normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp
        (sylowCenterSpan_normal _)))
    exact (isPGroup_pCoreIn 2 _).to_le (hZQ.trans (map_subtype_le _))
  intro z hz
  obtain ⟨_, hzc, hzs⟩ := (mem_omegaCenterIn_iff _ _).mp (hZQ hz)
  exact (mem_omegaCenterIn_iff _ _).mpr ⟨hZXQ hz, centralizer_le hcore hzc, hzs⟩

/-- The second vertex core centralizes X modulo the actual core intersection. -/
theorem core_closure_commutator_le_inter (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    ⁅conjugateSpanBy ((P i).pCoreIn 2) (P (other i)), (P (other i)).pCoreIn 2⁆ ≤
      (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 := by
  have hQiB := source_core_le_borel (Classical.choice (h.local_data i))
  have hQjB := source_core_le_borel (Classical.choice (h.local_data (other i)))
  rw [commutator_conjugateSpanBy_of_normalized_right _ _ _
    (hQiB.trans (borel_le h _)) (core_normalized _)]
  apply conjugateSpanBy_le _ hn
  exact le_inf (le_normalizer_iff_commutator_le_left.mp
    ((hQjB.trans (borel_le h i)).trans (core_normalized _)))
    (le_normalizer_iff_commutator_le_right.mp
      ((hQiB.trans (borel_le h (other i))).trans (core_normalized _)))

/-- The core of X is central in X modulo the original intersection. -/
theorem core_closure_core_commutator_le_inter (h : LocallyRankOneTriple P B) (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ⁅X.pCoreIn 2, X⁆ ≤ (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 := by
  dsimp only
  rw [commutator_comm]
  apply le_trans (commutator_mono le_rfl _) (core_closure_commutator_le_inter h i hn)
  exact pCoreIn_mono_of_normalizes (conjugateSpanBy_le_self
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _)))
    (le_normalizer_conjugateSpanBy _ _)

/-- The original core intersection lies in the intrinsic core of X. -/
theorem core_inter_le_closure_core (h : LocallyRankOneTriple P B) (i : Fin 2) :
    (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 ≤
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).pCoreIn 2 := by
  exact (inf_le_inf_right _ (le_conjugateSpanBy _ _)).trans
    (inf_pCoreIn_le_of_le 2 (conjugateSpanBy_le_self
      ((source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _))))

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual reduced F1.11 center is central elementary in the core of the
literal opposite-core closure, with no remaining local-theorem premise. -/
theorem reduced_center_le_closure_core_omega (h : HypothesisF11 L S) (i : Fin 2) :
    sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤
      omegaCenterIn ((conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S))).pCoreIn 2) :=
  source_center_le_closure_core_omega (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i

/-- The original 6.4 normality premise gives the reduced central-extension
commutator bound. All subgroups live in the actual reduced completion G₀. -/
theorem reduced_core_closure_central_extension (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S))) :
    let X := conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
      ((P₀ L S (other i)).subgroupOf (G₀ L S))
    (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
      ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2 ≤ X.pCoreIn 2) ∧
    ⁅X.pCoreIn 2, X⁆ ≤ ((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
      ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2 := by
  have hn' := (inter_core_local_normal_iff (reduced_triple h) i _).mp hn
  exact ⟨core_inter_le_closure_core (reduced_triple h) i,
    core_closure_core_commutator_le_inter (reduced_triple h) i hn'⟩
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
