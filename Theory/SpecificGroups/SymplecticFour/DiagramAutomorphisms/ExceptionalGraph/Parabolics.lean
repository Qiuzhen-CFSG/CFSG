module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses
import Mathlib.Tactic.FinCases

/-!
# The exceptional map exchanges the two actual parabolic types

The plane stabilizer has no invariant line: its four indicated root
involutions have zero common fixed space. It therefore cannot be conjugate
to the point stabilizer. The minors defining the exceptional automorphism
send the plane stabilizer into the point stabilizer; their equal orders
make this an equality. Squaring the automorphism gives Frobenius, which
fixes both parabolics, and hence proves the reverse interchange.

Source: GLS3, Theorems 2.5.1 and 2.5.12(e),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, Proposition 1.3.4,
printed p.511 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
variable {F : Type*} [Field F] [CharP F 2]
local notation "I" => Fin 2 ⊕ Fin 2
local notation "a" => (Sum.inl (0 : Fin 2) : I)
local notation "b" => (Sum.inl (1 : Fin 2) : I)
local notation "c" => (Sum.inr (0 : Fin 2) : I)
local notation "d" => (Sum.inr (1 : Fin 2) : I)

private lemma involution_fixes_line (r : Sp F) (hr : r*r=1)
    (v : Vector F) (hv : v ≠ 0) (t : F) (ht : r • v = t • v) : r • v = v := by
  have hs : t^2 • v = (1 : F) • v := by
    calc
      t^2 • v = t • (t • v) := by rw [pow_two, mul_smul]
      _ = t • (r • v) := congrArg (t • ·) ht.symm
      _ = r • (t • v) := ((toLinear r).map_smul t v).symm
      _ = r • (r • v) := congrArg (r • ·) ht.symm
      _ = (1 : F) • v := by rw [← mul_smul, hr, one_smul, one_smul]
  have ht1 : t = 1 := CharTwo.sq_injective (by simpa using smul_left_injective F hv hs)
  simpa [ht1] using ht

set_option maxHeartbeats 800000 in
private lemma root_square (r : Fin 8) (t : F) : rootElement r t * rootElement r t = 1 := by
  apply Subtype.ext
  ext i j
  change (rootMatrix r t * rootMatrix r t) i j = _
  fin_cases r <;> rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.fromBlocks, Matrix.single, Matrix.one_apply, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private lemma plane_no_invariant_line (v : Vector F) (hv : v ≠ 0)
    (h : ∀ r ∈ planeParabolic (F := F), ∃ t : F, r • v = t • v) : False := by
  have fixed (r : Fin 8) (hr : rootElement r (1 : F) ∈ planeParabolic) :
      rootElement r (1 : F) • v = v := by
    obtain ⟨t, ht⟩ := h _ hr
    exact involution_fixes_line _ (root_square r 1) v hv t ht
  have h0 := fixed 0 (by simp [mem_planeParabolic_iff, rootElement, rootMatrix, fromBlocks, single])
  have h2 := fixed 2 (by simp [mem_planeParabolic_iff, rootElement, rootMatrix, fromBlocks, single])
  have h6 := fixed 6 (by simp [mem_planeParabolic_iff, rootElement, rootMatrix, fromBlocks, single])
  have h7 := fixed 7 (by simp [mem_planeParabolic_iff, rootElement, rootMatrix, fromBlocks, single])
  have hc := congrFun h0 a
  have hd := congrFun h2 b
  have hb := congrFun h6 a
  have ha := congrFun h7 b
  simp [rootElement, rootMatrix, fromBlocks, single,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at hc hd hb ha
  apply hv
  funext i
  rcases i with i|i <;> fin_cases i <;> assumption

/-- The full plane stabilizer is not any conjugate of the full point stabilizer. -/
lemma planeParabolic_ne_conjugate_point (g : Sp F) :
    planeParabolic ≠ pointParabolic.map (MulAut.conj g).toMonoidHom := by
  intro h
  let v : Vector F := g • e 0
  have hv : v ≠ 0 := by
    change toLinear g (e 0) ≠ 0
    rw [ne_eq, (toLinear g).map_eq_zero_iff]
    intro he
    have := congrFun he a
    simp [e] at this
  apply plane_no_invariant_line v hv
  intro r hr
  rw [h] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  have he := (mem_stabilizer_iff (point F) q).mp hq (e 0)
    (Submodule.subset_span (Set.mem_singleton _))
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp he
  refine ⟨t, ?_⟩
  change (MulAut.conj g q) • (g • e 0) = t • (g • e 0)
  calc
    _ = g • (q • e 0) := by simp [mul_smul]
    _ = g • (t • e 0) := by rw [← ht]
    _ = _ := (toLinear g).map_smul t (e 0)

/-- The two actual parabolic conjugacy classes are distinct. -/
lemma parabolicClasses_distinct :
    subgroupConjugacyClass (pointParabolic (F := F)) ≠ subgroupConjugacyClass planeParabolic := by
  intro h
  have hp : planeParabolic (F := F) ∈ subgroupConjugacyClass planeParabolic := by
    exact ⟨1, by simp⟩
  rw [← h] at hp
  obtain ⟨g, hg⟩ := hp
  exact planeParabolic_ne_conjugate_point g hg.symm

variable [Finite F]
/-- The exceptional automorphism sends the plane stabilizer onto the point stabilizer. -/
lemma graphAut_map_plane : planeParabolic.map (graphAut (F := F)).toMonoidHom = pointParabolic := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, hg, rfl⟩
    change g ∈ planeParabolic at hg
    rw [mem_planeParabolic_iff] at hg
    rw [mem_pointParabolic_iff]
    constructor
    · simp [graphAut_apply, graphEnd, graphMatrix, minor, first, second, hg]
    · intro i
      fin_cases i <;> simp [graphAut_apply, graphEnd, graphMatrix, minor, first, second, hg]
  · rw [Subgroup.card_map_of_injective (f := graphAut.toMonoidHom) graphAut.injective,
      card_pointParabolic_eq_card_planeParabolic]

/-- The exceptional automorphism sends the point stabilizer onto the plane stabilizer. -/
lemma graphAut_map_point : pointParabolic.map (graphAut (F := F)).toMonoidHom = planeParabolic := by
  rw [← graphAut_map_plane, Subgroup.map_map]
  have he : (graphAut (F := F)).toMonoidHom.comp graphAut.toMonoidHom =
      (fieldAutomorphism (frobeniusEquiv F 2)).toMonoidHom := graphEnd_square
  rw [he, field_map_planeParabolic]

/-- The exceptional automorphism does not preserve the individual parabolic types. -/
lemma graphAut_not_preservesDiagram : ¬ PreservesDiagram (graphAut (F := F)) := by
  rintro ⟨⟨g, hg⟩, _⟩
  rw [graphAut_map_point] at hg
  exact planeParabolic_ne_conjugate_point g hg

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
