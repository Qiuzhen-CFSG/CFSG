module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceCommutingOne
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceNoncommutingRegular

/-!
# The original mixed bound sufficient for Chapter 15

The complete commuting branch has Borel two-core order 64. The
noncommuting branch has Borel two-core order at most 512. The original
full-Borel comparison bounds the original Sylow by twice this order,
giving at most 1024 directly from the literal A₅/S₃ F.1.1 markings.
This is the numerical estimate used by Chapter 15's two-chief-factor
contradiction; the sharper Chapter 10 bound remains separate.

Source: DGS, *Groups and Graphs* (1985), Chapters 10--11, pp.152--176,
and (15.1), p.226; Aschbacher--Smith 15.2.8, pp.1109--1110.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source.DGS85
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

/-- The noncommuting mixed branch has the required bound, with its critical
walk and additional neighbor constructed from the source graph. -/
theorem noncommuting_core_card_le_512 {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {a a' : Vertex (Reduction.reducedFamily ![K,U] S)}
    (hc : IsCriticalPair (Reduction.reducedFamily ![K,U] S) a a')
    (hne : ⁅Z (Reduction.reducedFamily ![K,U] S) a,
      Z (Reduction.reducedFamily ![K,U] S) a'⁆ ≠ ⊥) :
    Nat.card (twoCore (commonBorel ![K,U] S)) ≤ 512 := by
  have hbound :=
    CFSG.Quasithin.ChapterF.Source.DGS85.Reduction.reduced_intrinsic_noncommuting_bound
      h hc hne
  rcases hbound with hb1 | hb2
  · exact False.elim
      (CFSG.Quasithin.ChapterF.Source.MixedDGS.noncommuting_distance_one_false
        h eK eU hc hne hb1)
  · have hdist : (graph (Reduction.reducedFamily ![K,U] S)).dist a a' = 2 :=
      hc.1.trans hb2
    obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_dist_ne_zero
      (by rw [hdist]; decide)
    have hlen : p.length = 2 := hp.trans hdist
    let m := p.getVert 1
    have ham : (graph (Reduction.reducedFamily ![K,U] S)).Adj a m := by
      simpa [m] using p.adj_getVert_succ (i := 0) (by omega)
    have hma' : p.getVert p.length = a' := p.getVert_length
    have hlast : p.getVert 2 = a' := by simpa [hlen] using hma'
    have hmw : (graph (Reduction.reducedFamily ![K,U] S)).Adj m a' := by
      simpa [m, hlast] using p.adj_getVert_succ (i := 1) (by omega)
    have hval : 3 ≤ Nat.card
        ((graph (Reduction.reducedFamily ![K,U] S)).neighborSet a) := by
      rw [card_neighbors_of_indices (Reduction.reducedFamily ![K,U] S)
        (fun i => (((Reduction.reducedFamily ![K,U] S) (!i)).subgroupOf
          ((Reduction.reducedFamily ![K,U] S) i)).index) (fun _ => rfl)]
      exact source_valence_ge_three (Reduction.reduced_triple h)
        (Reduction.reduced_vertex_sylow h) a.type
    obtain ⟨t,hat,htne⟩ := Set.exists_ne_of_one_lt_ncard
      (s := (graph (Reduction.reducedFamily ![K,U] S)).neighborSet a)
      (by rw [←Nat.card_coe_set_eq]; omega) m
    exact CFSG.Quasithin.ChapterF.Source.MixedDGS.noncommuting_two_borel_core_le_fivehundredtwelve
      h eK eU hc hne hb2 ham hmw hat htne

/-- The complete original mixed pair has Borel two-core order at most 512. -/
theorem mixed_borel_core_card_le_512 (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Nat.card (twoCore (commonBorel ![K,U] S)) ≤ 512 := by
  have hpair : ∃ a a' : Vertex F, IsCriticalPair F a a' :=
    source_exists_criticalPair (Reduction.reduced_triple h)
  obtain ⟨a,a',hc⟩ := hpair
  by_cases hcomm : ⁅Z F a,Z F a'⁆ = ⊥
  · have hs := (commuting_size h eK eU hc hcomm).1
    omega
  · exact noncommuting_core_card_le_512 h eK eU hc hcomm

/-- The original Sylow bound needed by Chapter 15, with all profile,
critical-distance and recognition premises discharged. -/
theorem mixed_a5_s3_sylow_card_le_1024 (h : HypothesisF11 ![K,U] S)
    (hK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hU : Nonempty ((U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))) :
    Nat.card S ≤ 1024 := by
  have hc := mixed_borel_core_card_le_512 h hK.some hU.some
  have hmap : Nat.card (twoCore (commonBorel ![K,U] S)) =
      Nat.card (pCore 2 (commonBorel ![K,U] S)) :=
    card_map_of_injective (commonBorel ![K,U] S).subtype_injective
  have hs := h.mixed_sylow_card_le_twice_borel_core hK.some hU.some
  rw [←hmap] at hs
  omega

end CFSG.Quasithin.ChapterF.Source.MixedDGS
