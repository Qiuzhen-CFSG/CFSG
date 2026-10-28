module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreSection

/-!
# The natural middle-core quotient after adapted splitting

Central derived subgroups at the two neighbors make their core intersection
normal in the middle local actor. The full Sylow image of a neighboring core
then recognizes the quotient as the natural binary module. The two local
fields remain separate; only their orders are identified.

Source: DGS, *Groups and Graphs* (1985), printed p.150, the paragraph after
the construction of M.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Central derived subgroups at the two endpoints make their core intersection
normal in the middle local actor. -/
theorem adjacent_core_intersection_normal
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta x d : Vertex (family P)}
    (hb : (graph (family P)).Adj x beta) (hd : (graph (family P)).Adj x d)
    (hne : beta ≠ d)
    (hbesc : ¬ Q (family P) beta ≤ Q (family P) x)
    (hdesc : ¬ Q (family P) d ≤ Q (family P) x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    (hZb : Z (family P) beta ≤ Q (family P) d)
    (hZd : Z (family P) d ≤ Q (family P) beta)
    (hdb : ⁅Q (family P) beta,Q (family P) beta⁆ ≤ Z (family P) beta)
    (hdd : ⁅Q (family P) d,Q (family P) d⁆ ≤ Z (family P) d) :
    Q (family P) beta ⊓ Q (family P) d ≤ Q (family P) x ∧
      graphLocalGroup (family P) x ≤ normalizer
        ((Q (family P) beta ⊓ Q (family P) d : Subgroup G) : Set G) := by
  let Γ := family P
  let N := Q Γ beta ⊓ Q Γ d
  have hQnN : Q Γ x ≤ normalizer (N : Set G) :=
    (le_inf ((neighbor_core_le_localGroup h hB hS hb.symm).trans
        ((sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ beta)))
      ((neighbor_core_le_localGroup h hB hS hd.symm).trans
        ((sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ d)))).trans
      inf_normalizer_le_normalizer_inf
  have hZbQ : Z Γ beta ≤ Q Γ beta := (source_Z_Q_U h beta).1.trans (map_subtype_le _)
  have hZdQ : Z Γ d ≤ Q Γ d := (source_Z_Q_U h d).1.trans (map_subtype_le _)
  have hbn : Q Γ beta ≤ normalizer (N : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono inf_le_left le_rfl).trans hdb).trans (le_inf hZbQ hZb))
  have hdn : Q Γ d ≤ normalizer (N : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono inf_le_right le_rfl).trans hdd).trans (le_inf hZd hZdQ))
  have hn : graphLocalGroup Γ x ≤ normalizer (N : Set G) := by
    rw [linear_neighbor_core_generation h hB hS hb hd hne hbesc hdesc ex]
    exact sup_le (sup_le hQnN hbn) hdn
  refine ⟨?_,hn⟩
  have hh := le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 _).to_le (show N ≤ Q Γ beta from inf_le_left))
    (inf_le_left.trans (neighbor_core_le_localGroup h hB hS hb)) hn
  exact hh.trans (graphLocalGroup_core h x).le

/-- The same original middle quotient is natural after the neighboring
core-derived subgroups collapse into their central lines. -/
theorem adjacent_core_intersection_natural_section
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {beta x d : Vertex (family P)}
    (hb : (graph (family P)).Adj x beta) (hd : (graph (family P)).Adj x d)
    (hne : beta ≠ d)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,K))
    (ed : (graphLocalGroup (family P) d ⧸ pCore 2 (graphLocalGroup (family P) d)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F)
    (hZb : Z (family P) beta ≤ Q (family P) d)
    (hZd : Z (family P) d ≤ Q (family P) beta)
    (hdb : ⁅Q (family P) beta,Q (family P) beta⁆ ≤ Z (family P) beta)
    (hdd : ⁅Q (family P) d,Q (family P) d⁆ ≤ Z (family P) d) :
    CoreQuotientSection (family P) beta x d K ex := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ x
  let : Finite (Q Γ x) := Finite.of_injective
    (inclusion (Q_le_stabilizer Γ x)) (inclusion_injective _)
  let N := Q Γ beta ⊓ Q Γ d
  have hbesc := core_escape_of_intersection_obstruction Γ (hob beta x hb.symm)
  have hdesc := core_escape_of_intersection_obstruction Γ (hob d x hd.symm)
  obtain ⟨hNQ,hnN⟩ := adjacent_core_intersection_normal h hB hS hb hd hne hbesc hdesc ex
    hZb hZd hdb hdd
  obtain ⟨hNorm,hElem,hcard⟩ := middle_core_quotient_elementary_order h hB hS hob hb.symm hd hne ex eb ed
  let := hNorm
  have hcardK : Nat.card (Q Γ x ⧸ N.subgroupOf (Q Γ x)) = Nat.card K ^ 2 := by
    rw [hKF]
    exact hcard
  let := hElem
  let q := ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hker : q.ker = (Q Γ x).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ ex.injective,QuotientGroup.ker_mk']
    have hcore : (pCore 2 H).map H.subtype = Q Γ x := graphLocalGroup_core h x
    rw [←hcore]
    exact (comap_map_eq_self_of_injective H.subtype_injective (pCore 2 H)).symm
  obtain ⟨σ,c,hc⟩ := BinaryConjugationSection.exists_canonical H (Q Γ x) N
    (core_le_graphLocalGroup h x) hNQ
    ((sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ x)) hnN q
    (ex.surjective.comp (QuotientGroup.mk'_surjective _)) hker
  refine ⟨hNorm,hcardK,hElem,σ,c,hc,?_⟩
  intro n hn hF
  have hZdd : Z Γ d ≤ Q Γ d := (source_Z_Q_U h d).1.trans (map_subtype_le _)
  have hcomm : ⁅Q Γ d,Q Γ x ⊓ Q Γ d⁆ ≤ N :=
    ((commutator_mono le_rfl inf_le_right).trans hdd).trans (le_inf hZd hZdd)
  have hiD : (Q Γ x ⊓ Q Γ d).relIndex (Q Γ x) = Nat.card K := by
    rw [hKF,inf_relIndex_left]
    exact linear_adjacent_core_index h hB hS hd.symm
      (core_escape_of_intersection_obstruction Γ (hob x d hd)) ed
  exact middle_core_section_natural h hB hS hd (hob x d hd) ex σ c hn hF hcardK
    (Q Γ d) (isPGroup_pCoreIn 2 _) (neighbor_core_le_localGroup h hB hS hd)
    (linear_adjacent_core_index h hB hS hd hdesc ex) hiD hcomm

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
