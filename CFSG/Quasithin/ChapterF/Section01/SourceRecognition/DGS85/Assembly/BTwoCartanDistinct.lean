module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoPathCartan

/-!
# Distinct local factors in the full binary Cartan

The full path Cartan is normalized by the intrinsic movers. Conjugating one
local factor therefore lands in the local factor at the moved vertex. Its
commutator with the mover lies in the product of the two factors and in the
fixed beta factor. If the two local factors were equal, disjointness of the
odd factors would force the mover to centralize the first factor. The source
contradiction then uses the marked SL₂ quotient and its natural alpha-core.

The final H-intersection statement is retained as a separate algebraic
consumer so the residual argument can use exactly the subgroup it needs.
Source: DGS, *Groups and Graphs* (1985), (10.8), printed pp.160--161.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem cartan_local_conjugate (h : LocallyRankOneTriple P B)
    (K : Subgroup G) {a : G} (ha : a ∈ normalizer (K : Set G))
    (v : Vertex (family P)) :
    (K ⊓ graphLocalGroup (family P) v).map (MulAut.conj a).toMonoidHom =
      K ⊓ graphLocalGroup (family P) (a • v) := by
  have hk : K.map (MulAut.conj a).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp ha
  rw [map_inf _ _ _ (MulAut.conj a).injective, hk,
    ←graphLocalGroup_conjugate h]

theorem cartan_mover_commutator_mem (h : LocallyRankOneTriple P B)
    (K : Subgroup G) {v w : Vertex (family P)}
    (hKw : K ≤ stabilizer (family P) w)
    {a : G} (ha : a ∈ graphLocalGroup (family P) w)
    (haK : a ∈ normalizer (K : Set G))
    {x : G} (hx : x ∈ K ⊓ graphLocalGroup (family P) v) :
    ⁅a,x⁆ ∈ ((K ⊓ graphLocalGroup (family P) v) ⊔
      (K ⊓ graphLocalGroup (family P) (a • v))) ⊓
      (K ⊓ graphLocalGroup (family P) w) := by
  let _ := finite_endpoints h
  have hconj : a*x*a⁻¹ ∈ K ⊓ graphLocalGroup (family P) (a • v) := by
    rw [←cartan_local_conjugate h K haK v]
    exact mem_map_of_mem (MulAut.conj a).toMonoidHom hx
  have hcomK : ⁅a,x⁆ ∈ K := by
    exact K.mul_mem hconj.1 (K.inv_mem hx.1)
  have hn : K ≤ normalizer (graphLocalGroup (family P) w : Set G) :=
    hKw.trans (sylowGenerated_normalized _)
  have hcomL : ⁅a,x⁆ ∈ graphLocalGroup (family P) w :=
    le_normalizer_iff_commutator_le_left.mp hn (commutator_mem_commutator ha hx.1)
  exact ⟨(K ⊓ graphLocalGroup (family P) v ⊔
    K ⊓ graphLocalGroup (family P) (a • v)).mul_mem
      (mem_sup_right hconj) (mem_sup_left ((K ⊓ graphLocalGroup (family P) v).inv_mem hx)),
    hcomK,hcomL⟩

theorem distinct_local_tori_intersection_ne_bot (h : LocallyRankOneTriple P B)
    (K : Subgroup G) {v w : Vertex (family P)}
    (hKw : K ≤ stabilizer (family P) w)
    {a : G} (ha : a ∈ graphLocalGroup (family P) w)
    (haK : a ∈ normalizer (K : Set G))
    (hne : K ⊓ graphLocalGroup (family P) (a • v) ≠
      K ⊓ graphLocalGroup (family P) v) :
    ((K ⊓ graphLocalGroup (family P) v) ⊔
      (K ⊓ graphLocalGroup (family P) (a • v))) ⊓
      (K ⊓ graphLocalGroup (family P) w) ≠ ⊥ := by
  let _ := finite_endpoints h
  intro hbot
  have hcomm (x : G) (hx : x ∈ K ⊓ graphLocalGroup (family P) v) :
      a*x*a⁻¹ = x := by
    have hh := cartan_mover_commutator_mem h K hKw ha haK hx
    rw [hbot,mem_bot] at hh
    exact mul_inv_eq_one.mp hh
  apply hne
  rw [←cartan_local_conjugate h K haK v]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change a*x*a⁻¹ ∈ K ⊓ graphLocalGroup (family P) v
    rw [hcomm x hx]
    exact hx
  · intro x hx
    exact ⟨x,hx,hcomm x hx⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
