module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualNaturalSize
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.TwoKernelCyclicLift

/-!
# The actual cyclic torus in the Chapter 8 residual join

The Sylow-normalizer map of a group with binary SL₂ core quotient
surjects onto the field units with a two-group kernel. Lift that odd
cyclic group with its exact order. Apply this to the residual join
D = O²(L_alpha') Q_lambda, using its proved original quotient embedding.

Its Sylow image equals the full edge Sylow image in L_alpha'/Q_alpha'.
Thus its normalizer lies in the original edge, by the source edge
normalizer theorem. The lifted cyclic subgroup lies in D and the full
edge, is disjoint from Q_alpha', and normalizes the residual intersection.
In the reduced counterexample application, the proved intersection identity
makes this the literal quotient-omega preimage. This constructs the torus
needed for the natural-case exclusion; the exclusion itself is not asserted.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
proof of (8.3), p.136, the cyclic torus of order q_alpha' - 1.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
universe u
variable {G : Type u} [Group G]

private theorem linear_normalizer_cyclic_subgroup [Finite G]
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (q : G →* SL(2,K)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (S : Sylow 2 G)
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n) :
    ∃ C : Subgroup G, C ≤ normalizer (S : Set G) ∧
      IsCyclic C ∧ Nat.card C = Nat.card K - 1 ∧ Odd (Nat.card C) ∧
      Disjoint C (pCore 2 G) := by
  obtain ⟨f,hf,hker⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal q hq S
    (hk ▸ pCore_isPGroup.le_sylow_of_normal S)
  have hke : f.ker = (S : Subgroup G).subgroupOf (normalizer (S : Set G)) := by
    ext x
    exact hker x
  have hp : IsPGroup 2 f.ker := hke.symm ▸ S.isPGroup'.comap_subtype
  have ho : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units,hK]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow (n := n))
      (even_two.pow_of_ne_zero (by omega)) odd_one
  let : IsCyclic (⊤ : Subgroup Kˣ) := inferInstance
  obtain ⟨C,hcy,hC,hcard⟩ := Theory.GroupTheory.exists_cyclic_lift_of_two_kernel
    f hf hp (⊤ : Subgroup Kˣ) (by simpa only [card_top] using ho)
  let D := C.map (normalizer (S : Set G)).subtype
  have hd : Nat.card D = Nat.card Kˣ := by
    rw [card_map_of_injective (normalizer (S : Set G)).subtype_injective,hcard,card_top]
  have hodd : Odd (Nat.card D) := hd.symm ▸ ho
  refine ⟨D,map_subtype_le _,?_,hd.trans (Nat.card_units K),hodd,?_⟩
  · let := hcy
    exact isCyclic_of_surjective ((normalizer (S : Set G)).subtype.subgroupMap C)
      ((normalizer (S : Set G)).subtype.subgroupMap_surjective C)
  · obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hr]
    exact hodd.coprime_two_right.pow_right r

open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A large-field linear endpoint supplies an actual cyclic odd torus
inside its residual join and the full original edge. It normalizes the
literal residual intersection and meets the original endpoint core trivially. -/
theorem source_linear_residual_edge_torus (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup w))
    (hR : (R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype =
      (stabilizer (family P) w ⊓ stabilizer (family P) v).pCoreIn 2)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* SL(2,K)) :
    let F := family P
    let L := d.localGroup v
    let E := (pResidual 2 L).map L.subtype
    let D := E ⊔ Q F w
    let T₀ := ((R : Subgroup (d.localGroup w)).map (d.localGroup w).subtype) ⊓ D
    ∃ C : Subgroup G, C ≤ D ∧ C ≤ stabilizer F w ∧
      C ≤ normalizer (T₀ : Set G) ∧ IsCyclic C ∧
      Nat.card C = Nat.card K - 1 ∧ Odd (Nat.card C) ∧ Disjoint C (Q F v) := by
  intro F L E D T₀
  let : ∀ i, Finite (F i) := finite_endpoints h
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨hDL,hnD,S,hS⟩ := source_residual_join_sylow h hB d hvw R hR
  let : Finite D := Finite.of_injective (inclusion hDL) (inclusion_injective _)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
  obtain ⟨_,eD,heD⟩ := source_residual_join_linear_quotient h hB d hvw R hR hK4 e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let π := eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hπ : Function.Surjective π := eD.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ eD.injective,QuotientGroup.ker_mk']
  obtain ⟨C,hCN,hcy,hcard,hodd,hdis⟩ := linear_normalizer_cyclic_subgroup π hπ hker S (by omega) hK
  let C₀ := C.map D.subtype
  have hc : Nat.card C₀ = Nat.card C := card_map_of_injective D.subtype_injective
  have hC₀D : C₀ ≤ D := map_subtype_le _
  have hC₀N : C₀ ≤ normalizer (T₀ : Set G) := by
    have hS' : (S : Subgroup D).map D.subtype = T₀ := hS
    rw [←hS']
    exact (map_mono hCN).trans ((S : Subgroup D).le_normalizer_map D.subtype)
  have hC₀cy : IsCyclic C₀ := by
    let := hcy
    exact isCyclic_of_surjective (D.subtype.subgroupMap C) (D.subtype.subgroupMap_surjective C)
  have hC₀odd : Odd (Nat.card C₀) := hc.symm ▸ hodd
  have hC₀dis : Disjoint C₀ (Q F v) := by
    let : Finite (Q F v) := Finite.of_injective (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
    have hp : IsPGroup 2 (Q F v) := isPGroup_pCoreIn 2 (stabilizer F v)
    obtain ⟨r,hr⟩ := hp.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [show Nat.card (Q F v) = 2^r from hr]
    exact hC₀odd.coprime_two_right.pow_right r
  refine ⟨C₀,hC₀D,?_,hC₀N,hC₀cy,hc.trans hcard,hC₀odd,hC₀dis⟩
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hvw
  have hST : (S : Subgroup D).map (inclusion hDL) ≤ T := by
    rintro _ ⟨s,hs,rfl⟩
    have hsT : (s : G) ∈ (T : Subgroup L).map L.subtype := by
      have hh := hS ▸ mem_map_of_mem D.subtype hs
      rw [hT,inf_comm]
      exact hR ▸ hh.1
    obtain ⟨t,ht,he⟩ := hsT
    exact (Subtype.ext he : t = inclusion hDL s) ▸ ht
  have hmap : (S : Subgroup D).map π = (T : Subgroup L).map q := by
    have hcomp : π = q.comp (inclusion hDL) := MonoidHom.ext heD
    have hle : (S : Subgroup D).map π ≤ (T : Subgroup L).map q := by
      rw [hcomp,←map_map]
      exact map_mono hST
    let T' := T.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    let S' := S.mapSurjective (f := π) hπ
    exact (S'.is_maximal' T'.isPGroup' hle).symm
  have hkT : q.ker ≤ T := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal T
  have hedge := (source_edge_local_normalizer h d hvw M T hT).2
  rintro _ ⟨c,hcC,rfl⟩
  have hN : π c ∈ normalizer ((S : Subgroup D).map π : Set SL(2,K)) :=
    (S : Subgroup D).le_normalizer_map π (mem_map_of_mem π (hCN hcC))
  rw [hmap] at hN
  have he : π c = q (inclusion hDL c) := heD c
  rw [he] at hN
  have hTc : inclusion hDL c ∈ normalizer (T : Set L) := by
    have hh := le_normalizer_comap q hN
    rwa [comap_map_eq_self hkT] at hh
  have hh : inclusion hDL c ∈ (stabilizer F w).subgroupOf L := hedge.symm ▸ hTc
  exact hh

variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The same cyclic torus on the reduced source lies in the full original
edge and normalizes the actual quotient-omega preimage, after the proved
residual-intersection identity. Its order and endpoint core are unchanged. -/
theorem reduced_counterexample_linear_edge_torus
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SL(2,K)) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F a'
    let D := (pResidual 2 L).map L.subtype ⊔ Q F w.val
    ∃ C : Subgroup (Reduction.G₀ J S₀), C ≤ D ∧
      C ≤ stabilizer F a' ⊓ stabilizer F w.val ∧
      C ≤ normalizer (quotientSylowOmegaPreimage (graphLocalGroup F w.val) R : Set (Reduction.G₀ J S₀)) ∧
      IsCyclic C ∧ Nat.card C = 2^n - 1 ∧ Odd (Nat.card C) ∧ Disjoint C (Q F a') := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hescape := CommutingTrivial.core_escape_of_intersection_obstruction F
    (hob w.val a' w.property.symm)
  obtain ⟨C,hCD,hCw,hCN,hcy,hcard,hodd,hdis⟩ := source_linear_residual_edge_torus
    ht (Reduction.reduced_borel_core_sylow h) d w.property (models a') R hR hn hK e
  have hD := (source_residual_join_sylow ht (Reduction.reduced_borel_core_sylow h)
    d w.property R hR).1
  have heq := source_counterexample_residual_edge_eq_omega ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models w hm hescape R hR hbad
  exact ⟨C,hCD,le_inf (hCD.trans (hD.trans (d.local_le a'))) hCw,
    heq ▸ hCN,hcy,hcard.trans (by rw [hK]),hodd,hdis⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
