module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.TheoremBFullCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.AdjacentParameterEquality

/-!
# Excluding commuting distance three for the original mixed pair

The literal A₅/S₃ quotient markings give adjacent quotient-Sylow omega
orders four and two. If the critical displacement vanishes, Chapter 9
makes both orders two. Otherwise every moving neighbor has a linear
quotient, so 8.1 makes the displacement central. The proved equivalences
in 8.6 give starting naturality, and 8.7 equates the adjacent orders.
Both branches contradict the original unequal markings.

Thus a commuting critical pair has distance one. Together with the
noncommuting bound this excludes distance three for the original F.1.1
mixed pair, without a recognition or field-comparison premise.
Source: DGS, *Groups and Graphs* (1985), 8.1, 8.6--8.7 and 9.10,
printed pp.132--140,147--150; Aschbacher--Smith F.1.12(I), pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

private theorem adjacent_quotient_omega_card_ne
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta : Vertex F} (hab : (graph F).Adj a beta)
    (Rα : Sylow 2 (graphLocalGroup F a)) (Rβ : Sylow 2 (graphLocalGroup F beta)) :
    Nat.card (omegaCenterIn ((Rα : Subgroup (graphLocalGroup F a)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup F a))))) ≠
    Nat.card (omegaCenterIn ((Rβ : Subgroup (graphLocalGroup F beta)).map
      (QuotientGroup.mk' (pCore 2 (graphLocalGroup F beta))))) := by
  let : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
  let : ∀ v : Vertex F, Finite (graphLocalGroup F v) := fun v =>
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  have htwo : Nat.card (ZMod 2) = 2 := by norm_num [Nat.card_eq_fintype_card]
  have hbtype : beta.type = !a.type := Bool.eq_not_of_ne hab.1.symm
  cases ha : a.type with
  | false =>
    have hb : beta.type = true := by simpa only [ha,Bool.not_false] using hbtype
    have hα := (linear_marking_quotient_sylow_omega_card
      (graph_linear_four h eK a ha).some Rα).trans hfour
    have hβ := (linear_marking_quotient_sylow_omega_card
      (graph_linear_two h eU beta hb).some Rβ).trans htwo
    omega
  | true =>
    have hb : beta.type = false := by simpa only [ha,Bool.not_true] using hbtype
    have hα := (linear_marking_quotient_sylow_omega_card
      (graph_linear_two h eU a ha).some Rα).trans htwo
    have hβ := (linear_marking_quotient_sylow_omega_card
      (graph_linear_four h eK beta hb).some Rβ).trans hfour
    omega

/-- A commuting critical pair of the original mixed A₅/S₃ family has
distance one, retaining its directed critical pair and first path edge. -/
theorem commuting_distance_one
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hcomm : ⁅Z F a,Z F a'⁆ = ⊥) : b F = 1 := by
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : ∀ v : Vertex F, Finite (graphLocalGroup F v) := fun v =>
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hp : 0 < b F := source_b_positive ht
  by_contra hb1
  have hb : 1 < b F := by omega
  let Rα : Sylow 2 (graphLocalGroup F a) := default
  let Rβ : Sylow 2 (graphLocalGroup F beta) := default
  apply adjacent_quotient_omega_card_ne h eK eU hab Rα Rβ
  by_cases htriv : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = ⊥
  · obtain ⟨_,k,hk,hkf,hkc,l,hl,hlf,hlc,hk2,hl2,ek,el⟩ :=
      reduced_critical_fields_two_from_chapterEight h (graph_models h eK eU)
        hc hab hd hb hcomm htriv
    let := hk
    let := hkf
    let := hkc
    let := hl
    let := hlf
    let := hlc
    exact ((linear_marking_quotient_sylow_omega_card el.some Rα).trans hl2).trans
      ((linear_marking_quotient_sylow_omega_card ek.some Rβ).trans hk2).symm
  · obtain ⟨w,hw,_⟩ := exists_moving_neighbor F
      (fun v => (source_Z_Q_U ht v).1) beta a' htriv
    have hcentral : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≤ Z F a' := by
      by_cases hwtype : w.val.type = false
      · exact reduced_linear_moving_commutator_central h (graph_models h eK eU)
          hc hab hd hb hcomm w hw (graph_linear_four h eK w.val hwtype).some
      · exact reduced_linear_moving_commutator_central h (graph_models h eK eU)
          hc hab hd hb hcomm w hw
          (graph_linear_two h eU w.val (by cases ht : w.val.type <;> simp_all)).some
    obtain ⟨_,mid,_,_,hAD,hDI,hIN,_⟩ := reduced_critical_central_equivalences
      h (graph_models h eK eU) hc hab hd hb hcomm htriv
    have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
    exact reduced_natural_start_adjacent_parameter_equality h (graph_models h eK eU)
      hc hab hd hb hcomm htriv hnat Rα Rβ

/-- The original mixed quotient markings leave only critical distances
one and two; no critical-pair or catalogue premise remains. -/
theorem critical_distance_one_or_two
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) : b F = 1 ∨ b F = 2 := by
  have ht := Reduction.reduced_triple h
  have hpair : ∃ a a' : Vertex F, IsCriticalPair F a a' := source_exists_criticalPair ht
  obtain ⟨a,a',hc⟩ := hpair
  have hne : a' ≠ a := by
    intro he
    have hp : 0 < b F := source_b_positive ht
    have hd := hc.1
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨beta,hab,hd⟩ := exists_predecessor F ht.generate a' a hne
  rw [SimpleGraph.dist_comm (u := a') (v := beta),
    SimpleGraph.dist_comm (u := a') (v := a),hc.1] at hd
  by_cases hcomm : ⁅Z F a,Z F a'⁆ = ⊥
  · exact Or.inl (commuting_distance_one h eK eU hc hab hd hcomm)
  · exact Reduction.reduced_intrinsic_noncommuting_bound h hc hcomm

/-- Distance three is impossible for the literal original mixed A₅/S₃
F.1.1 family, independently of recognition. -/
theorem critical_distance_ne_three
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) : b F ≠ 3 := by
  have hb := critical_distance_one_or_two h eK eU
  omega

end CFSG.Quasithin.ChapterF.Source.MixedDGS
