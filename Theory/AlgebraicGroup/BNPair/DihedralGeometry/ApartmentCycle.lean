module

public import Theory.AlgebraicGroup.BNPair.DihedralGeometry
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The standard apartment of an octagonal Tits system

The normalizer orbit of the two standard parabolic cosets is the support of
an actual simple sixteen-cycle in the typed coset incidence graph.

Choose normalizer lifts of the rotations in the marked dihedral quotient.
Alternating the vertices represented by `r k` of type `false` and `r (k + 1)`
of type `true` gives the cycle. A lift of `sr (-k)` supplies their common
representative, and the next edge has a common rotation representative.
The rank-one quotient criterion proves distinctness. Every reflected
representative gives one of these rotation vertices, proving exact support
coverage. No finiteness or geometric assumptions are needed.

Source: the dihedral BN-pair building construction, GLS3 §§2.3 and 2.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup DihedralGroup

namespace Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
namespace OctagonalDatum
noncomputable section
variable {X I : Type*} [Group X] {T : TitsSystem (X := X)} {F : I → Subgroup X}
variable (D : OctagonalDatum T F)

/-- The marked quotient map on the actual normalizer. -/
private def weylMap : T.N →* DihedralGroup 8 :=
  D.weylEquiv.toMonoidHom.comp (QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N))

private theorem weylMap_surjective : Function.Surjective D.weylMap :=
  D.weylEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

private def lift (w : DihedralGroup 8) : T.N := (D.weylMap_surjective w).choose

@[simp] private theorem weylMap_lift (w : DihedralGroup 8) :
    D.weylMap (D.lift w) = w := (D.weylMap_surjective w).choose_spec

/-- Rotation representatives, with the original vertex types recovered by the marking. -/
private def vertex (k : ZMod 8) (b : Bool) : CosetGeometry.Vertex F :=
  (D.lift (r k) : X) • CosetGeometry.base F (D.typeEquiv.symm b)

@[simp] private theorem vertex_type (k : ZMod 8) (b : Bool) :
    (D.vertex k b).type = D.typeEquiv.symm b := rfl

private theorem lift_eq_iff (w w' : DihedralGroup 8) (b : Bool) :
    (D.lift w : X) • CosetGeometry.base F (D.typeEquiv.symm b) =
      (D.lift w' : X) • CosetGeometry.base F (D.typeEquiv.symm b) ↔
    w⁻¹ * w' = 1 ∨ w⁻¹ * w' = sr (if b then 1 else 0) := by
  rw [D.normalizer_smul_base_eq_iff]
  change D.weylMap ((D.lift w)⁻¹ * D.lift w') = 1 ∨
    D.weylMap ((D.lift w)⁻¹ * D.lift w') = sr (if D.typeEquiv (D.typeEquiv.symm b) then 1 else 0) ↔ _
  simp only [map_mul, map_inv, weylMap_lift, Equiv.apply_symm_apply]

private theorem vertex_eq_iff (k l : ZMod 8) (b : Bool) :
    D.vertex k b = D.vertex l b ↔ k = l := by
  rw [vertex, vertex, D.lift_eq_iff]
  simp only [inv_r, r_mul_r, one_def, r.injEq, reduceCtorEq, or_false]
  exact neg_add_eq_zero

private theorem vertex_adj_same (k : ZMod 8) :
    (graph F).Adj (D.vertex k false) (D.vertex k true) := by
  refine ⟨?_, ?_⟩
  · simpa only [vertex_type, ne_eq, D.typeEquiv.symm.injective.eq_iff] using Bool.false_ne_true
  · exact (CosetGeometry.incident_base F _ _).smul F (D.lift (r k) : X)

/-- A reflected representative joins successive rotation indices. -/
private theorem vertex_adj_next (k : ZMod 8) :
    (graph F).Adj (D.vertex k false) (D.vertex (k + 1) true) := by
  refine ⟨?_, ?_⟩
  · simpa only [vertex_type, ne_eq, D.typeEquiv.symm.injective.eq_iff] using Bool.false_ne_true
  · apply (incident_iff_common_translate F _ _).mpr
    refine ⟨(D.lift (sr (-k)) : X), ?_, ?_⟩
    · change _ = (D.lift (r k) : X) • _
      rw [vertex_type, D.lift_eq_iff]
      exact Or.inr (by simp)
    · change _ = (D.lift (r (k + 1)) : X) • _
      rw [vertex_type, D.lift_eq_iff]
      exact Or.inr (by simp)

/-- Reflected representatives contribute no additional apartment vertices. -/
private theorem vertex_range :
    Set.range (fun p : ZMod 8 × Bool => D.vertex p.1 p.2) = apartment T F := by
  ext v
  constructor
  · rintro ⟨⟨k, b⟩, rfl⟩
    exact ⟨D.lift (r k), (D.lift (r k)).property, D.typeEquiv.symm b, rfl⟩
  · rintro ⟨n, hn, i, rfl⟩
    let n' : T.N := ⟨n, hn⟩
    have heq (k : ZMod 8) : D.vertex k (D.typeEquiv i) = n • CosetGeometry.base F i ↔
        (r k)⁻¹ * D.weylMap n' = 1 ∨
        (r k)⁻¹ * D.weylMap n' = sr (if D.typeEquiv i then 1 else 0) := by
      simp only [vertex, Equiv.symm_apply_apply]
      rw [D.normalizer_smul_base_eq_iff i (D.lift (r k)) n']
      change D.weylMap ((D.lift (r k))⁻¹ * n') = 1 ∨
        D.weylMap ((D.lift (r k))⁻¹ * n') = sr (if D.typeEquiv i then 1 else 0) ↔ _
      simp only [map_mul, map_inv, weylMap_lift]
    cases h : D.weylMap n' with
    | r k =>
      refine ⟨(k, D.typeEquiv i), (heq k).mpr ?_⟩
      exact Or.inl (by simp [h])
    | sr k =>
      let e : ZMod 8 := if D.typeEquiv i then 1 else 0
      refine ⟨(e - k, D.typeEquiv i), (heq (e - k)).mpr ?_⟩
      exact Or.inr (by simp [h, e])

/-- The cyclic order is `(0, false), (1, true), (1, false), …, (0, true)`. -/
private def coordinates (a : Fin 16) : ZMod 8 × Bool :=
  (((a.val + 1) / 2 : ℕ), decide (a.val % 2 = 1))

-- These finite checks concern only the enumeration of the sixteen coordinates.
private theorem coordinates_injective : Function.Injective coordinates := by decide
private theorem coordinates_surjective : Function.Surjective coordinates := by decide

private theorem coordinates_adj (a b : Fin 16) (h : (SimpleGraph.cycleGraph 16).Adj a b) :
    (coordinates a).2 = false ∧ (coordinates b).2 = true ∧
      ((coordinates b).1 = (coordinates a).1 ∨ (coordinates b).1 = (coordinates a).1 + 1) ∨
    (coordinates a).2 = true ∧ (coordinates b).2 = false ∧
      ((coordinates a).1 = (coordinates b).1 ∨ (coordinates a).1 = (coordinates b).1 + 1) := by
  revert a b
  decide

/-- The standard cycle visits every vertex of the sixteen-cycle graph. -/
private theorem cycle_support (a : Fin 16) : a ∈ (SimpleGraph.cycleGraph.cycle 13).support := by
  have h : (SimpleGraph.cycleGraph.cycle 13).getVert (16 - a.val) = a := by
    rw [SimpleGraph.cycleGraph.getVert_cycle (by omega)]
    apply Fin.ext
    change (16 - (16 - a.val)) % 16 = a.val
    omega
  rw [← h]
  exact SimpleGraph.Walk.getVert_mem_support _ _

private def cycleHom : SimpleGraph.cycleGraph 16 →g graph F where
  toFun a := D.vertex (coordinates a).1 (coordinates a).2
  map_rel' := by
    intro a b h
    rcases coordinates_adj a b h with ⟨ha, hb, hk | hk⟩ | ⟨ha, hb, hk | hk⟩
    · rw [ha, hb, hk]
      exact D.vertex_adj_same _
    · rw [ha, hb, hk]
      exact D.vertex_adj_next _
    · rw [ha, hb, hk]
      exact (D.vertex_adj_same _).symm
    · rw [ha, hb, hk]
      exact (D.vertex_adj_next _).symm

private theorem cycleHom_injective : Function.Injective D.cycleHom := by
  intro a b hab
  have ht := congrArg CosetGeometry.Vertex.type hab
  change D.typeEquiv.symm (coordinates a).2 = D.typeEquiv.symm (coordinates b).2 at ht
  have ht' := D.typeEquiv.symm.injective ht
  change D.vertex (coordinates a).1 (coordinates a).2 =
    D.vertex (coordinates b).1 (coordinates b).2 at hab
  rw [ht', D.vertex_eq_iff] at hab
  exact coordinates_injective (Prod.ext hab ht')

private theorem cycleHom_range : Set.range D.cycleHom = apartment T F := by
  rw [← D.vertex_range]
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨coordinates a, rfl⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨a, rfl⟩ := coordinates_surjective p
    exact ⟨a, rfl⟩

include D in
/-- The standard normalizer apartment is exactly the support of a simple
sixteen-cycle in the original coset incidence graph. -/
theorem standardApartmentCycle : StandardApartmentCycle T F := by
  refine ⟨D.cycleHom 0, (SimpleGraph.cycleGraph.cycle 13).map D.cycleHom, ?_, ?_, ?_⟩
  · exact (SimpleGraph.Walk.isCycle_map_iff_of_injective D.cycleHom_injective).mpr
      SimpleGraph.cycleGraph.isCycle_cycle
  · simp only [SimpleGraph.Walk.length_map, SimpleGraph.cycleGraph.length_cycle]
  · rw [← D.cycleHom_range]
    ext v
    simp only [Set.mem_ofPred_eq, SimpleGraph.Walk.support_map, List.mem_map, Set.mem_range]
    constructor
    · rintro ⟨a, _, ha⟩
      exact ⟨a, ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, cycle_support a, ha⟩

end
end OctagonalDatum
end Theory.AlgebraicGroup.TitsSystem.DihedralGeometry
