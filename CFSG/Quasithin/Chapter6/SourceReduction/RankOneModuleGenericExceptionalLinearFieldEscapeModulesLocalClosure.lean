module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalPair
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCartan
public import Theory.GroupTheory.PResidual.ConjugateSpanNormalizer
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The original cubic closure and its surviving image

The generated-core condition prevents any nontrivial two-subgroup containing
the H-span from being normalized by both H and the original cubic. Thus an
elementary cubic closure inside H strictly enlarges that span and is not
H-invariant. In the opposite geometry, the H-span cannot lie in S₂: the
bound [S₂,I] ≤ V would make the cubic normalize the H-span.

The cubic closure is normalized by the original opposite core, C and B.
The exact opposite-action kernel then proves that the moving cubic conjugate
of the H-span has nontrivial image on the full centralizer span modulo ⟨z⟩.
The Chapter12 application places this specific image inside the surviving
centralizer factor. These constraints do not yet exclude that factor.

Source: Aschbacher--Smith G.2.3 and 5.1.23, and the generated-core condition
at the end of 5.1.14, printed pp.333--334,645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ} {z : G}

private theorem LocalData.no_common_normal_two_subgroup (d : LocalData T H C z)
    (N : Subgroup G) (hN : IsPGroup 2 N) (hNH : N ≤ H)
    (hUN : (setup T H C z).U ≤ N)
    (hHN : H ≤ normalizer (N : Set G)) (hCN : C ≤ normalizer (N : Set G)) : False := by
  let J := (actor T C ⊔ (T : Subgroup G)) ⊔ H
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.g2.local_le
  have hJN : J ≤ normalizer (N : Set G) := by
    apply sup_le (sup_le ?_ (hTH.trans hHN)) hHN
    exact conjugateSpanBy_le hCN ((hTH.trans hHN).trans (normalizer _).le_normalizer)
  have hNQ : N ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hN
    (hNH.trans le_sup_right) hJN
  have hQ : J.pCoreIn 2 = ⊥ := by
    change (pCore 2 J).map J.subtype = ⊥
    rw [d.generated_core, Subgroup.map_bot]
  have hzN : z ∈ N := hUN (le_conjugateSpanBy _ _
    (le_conjugateSpanBy _ _ (mem_zpowers z)))
  apply d.point_ne
  simpa only [hQ, mem_bot] using hNQ hzN

/-- The generated-core condition forces actual enlargement by the original cubic. -/
theorem LocalData.local_cubic_span_escape (d : LocalData T H C z)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C))
    (hle : conjugateSpanBy (setup T H C z).U C ≤ H) :
    (setup T H C z).U < conjugateSpanBy (setup T H C z).U C ∧
      ¬ H ≤ normalizer (conjugateSpanBy (setup T H C z).U C : Set G) := by
  let N := conjugateSpanBy (setup T H C z).U C
  have hCN : C ≤ normalizer (N : Set G) := le_normalizer_conjugateSpanBy _ _
  have hn : ¬ H ≤ normalizer (N : Set G) := fun hHN =>
    d.no_common_normal_two_subgroup N he.isPGroup hle
      (le_conjugateSpanBy _ _) hHN hCN
  refine ⟨lt_of_le_of_ne (le_conjugateSpanBy _ _) ?_, hn⟩
  intro hh
  apply hn
  change H ≤ normalizer (conjugateSpanBy (setup T H C z).U C : Set G)
  rw [← hh]
  exact le_normalizer_conjugateSpanBy _ _

/-- The original H-span cannot lie in the elementary middle intersection. -/
theorem LocalData.local_span_not_le_middle (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    ¬ (setup T H C z).U ≤ (setup T (centralizer ({z} : Set G)) C z).S₂ g := by
  let D := setup T (centralizer ({z} : Set G)) C z
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,hnorm,hi,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hEC,_⟩ :=
    D.binary_source_clauses_three_to_seven s b s.U_normal_in_T.1 s.frattini_U_le_point
      g hga hgn hI (binarySourceCoreEquiv s b s.U_normal_in_T.1 g hga hgn) hnorm hi
  have hCI : C ≤ D.I g := (le_conjugateSpanBy C (T : Subgroup G)).trans
    (le_sup_left.trans hI.ge)
  intro hle
  apply d.no_common_normal_two_subgroup (setup T H C z).U d.g2.U_isPGroup
    d.g2.U_le_H le_rfl (le_normalizer_conjugateSpanBy _ _)
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono hle hCI).trans hEC).trans (le_conjugateSpanBy _ _)

/-- The literal cubic closure is normalized by the original opposite core and Cartan. -/
theorem LocalData.local_cubic_span_normalizers
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hle : (setup T H C z).U ≤ (setup T (centralizer ({z} : Set G)) C z).W g) :
    let D := setup T (centralizer ({z} : Set G)) C z
    let N := conjugateSpanBy (setup T H C z).U C
    N ≤ D.S g ∧ D.S g ⊔ C ⊔ B ≤ normalizer (N : Set G) := by
  intro D N
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,_,_,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  have hST : D.S g ≤ (T : Subgroup G) :=
    (binary_S_le_LT_core s.U_normal_in_T.1 g hga
      (binaryStarEquiv s.toBaseHypothesis b s.U_normal_in_T.1)
      (binary_source_star_generation s b s.U_normal_in_T.1 g hga hgn)).trans
        s.toBaseHypothesis.binary_core_le_T
  have hSH : D.S g ≤ H := hST.trans (le_sup_right.trans d.g2.local_le)
  have hCI : C ≤ D.I g := (le_conjugateSpanBy C (T : Subgroup G)).trans
    (le_sup_left.trans hI.ge)
  have hCS : C ≤ normalizer (D.S g : Set G) := hCI.trans (D.binary_core_normalized g)
  refine ⟨conjugateSpanBy_le (hle.trans inf_le_right) hCS, sup_le (sup_le ?_ ?_) ?_⟩
  · exact normalizes_conjugateSpanBy_of_normalized_actor _ _ _
      (hSH.trans (le_normalizer_conjugateSpanBy _ _)) hCS
  · exact le_normalizer_conjugateSpanBy _ _
  · exact normalizes_conjugateSpanBy _ _ _
      ((c.right_le.trans inf_le_right).trans (le_normalizer_conjugateSpanBy _ _))
      ((right_cartan_centralizes_cubic c).trans (Subgroup.centralizer_le_normalizer _))

/-- The actual moving local span survives the full centralizer-span projection. -/
theorem LocalData.moving_local_span_image_ne_bot (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hle : (setup T H C z).U ≤ (setup T (centralizer ({z} : Set G)) C z).W g) :
    ((conjugate (setup T H C z).U g).subgroupOf (centralizer ({z} : Set G))).map
      (SpanAction.projection s) ≠ ⊥ := by
  let D := setup T (centralizer ({z} : Set G)) C z
  let U₀ := (setup T H C z).U
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,hnorm,hi,hgI⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hEN,_⟩ :=
    D.binary_source_clauses_three_to_seven s b s.U_normal_in_T.1 s.frattini_U_le_point
      g hga hgn hI (binarySourceCoreEquiv s b s.U_normal_in_T.1 g hga hgn) hnorm hi
  have hEg : (D.S₂ g).map (MulAut.conj g).toMonoidHom = D.S₂ g :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normal_subgroupOf_iff_le_normalizer
        (show D.S₂ g ≤ D.I g from inf_le_left.trans le_sup_left)).mp hEN hgI)
  have hHC : H ≤ D.H := by
    change H ≤ centralizer ({z} : Set G)
    simpa only [zpowers_eq_closure, centralizer_closure] using d.H_centralizes_point
  have hgH : conjugate U₀ g ≤ D.H :=
    (d.local_pair_containment s b g hg hgn hle).1.trans hHC
  intro he
  have hk := (Subgroup.map_eq_bot_iff _).mp he
  have hgm : conjugate U₀ g ≤ D.S₂ g := by
    intro x hx
    have hm : (⟨x,hgH hx⟩ : D.H) ∈
        (SpanAction.projection s).ker ⊓ (conjugate (D.W g) g).subgroupOf D.H :=
      ⟨hk hx, map_mono hle hx⟩
    rw [SpanAction.binary_opposite_kernel s b g hga hgn] at hm
    exact hm
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hgm
  rw [hEg] at hh
  have hc : (conjugate U₀ g).map (MulAut.conj g).toMonoidHom = U₀ := by
    simpa only [conjugate, inv_inv] using
      Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.conjugate_inverse_cancel g⁻¹ U₀
  rw [hc] at hh
  exact d.local_span_not_le_middle s b g hg hgn hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
