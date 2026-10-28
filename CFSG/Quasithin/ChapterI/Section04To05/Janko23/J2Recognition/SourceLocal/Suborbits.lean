module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Incidence
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Counting
public import Theory.AtlasPort.OtherSporadic.GroupTheory.FiniteSuborbitPrimitivity

/-!
# Maximality from the four J₂ suborbits

The four source suborbits have sizes 1, 36, 135 and 108. A block containing
X is a union of these suborbits, and its size divides 280. The only possible
sizes are 1 and 280. Thus the action is primitive and N_G(X) is maximal.
Any subgroup moving X to a neighbor consequently generates G with N_G(X).

This discharges the global generation step of Aschbacher, *Sporadic Groups*
(1994), 47.10, p.266, conditional on the genuine 47.5 suborbit calculation.
It avoids reapplying recognition or source type to the generated subgroup.
The finite block theorem is reused from the attributed ATLAS port.
-/

@[expose] public section

open Subgroup MulAction
open scoped BigOperators
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

namespace FourSuborbits
variable (R : FourSuborbits D)
include R

theorem vertex_card : Nat.card D.Vertex = 280 := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (orbitLabel D)), Nat.card_sigma]
  simp_rw [R.card]
  decide +kernel

theorem preprimitive : IsPreprimitive G D.Vertex := by
  let : IsPretransitive G D.Vertex := ⟨by
    intro x y
    obtain ⟨g, rfl⟩ := D.transitive x
    obtain ⟨h, rfl⟩ := D.transitive y
    exact ⟨h * g⁻¹, by simp [mul_smul]⟩⟩
  apply Atlas.GroupTheory.primitive_of_suborbit_sums D.base (orbitLabel D)
    (d := subdegrees) _ R.card
  · intro T hT hdvd
    rw [R.vertex_card] at hdvd ⊢
    rw [orbitLabel_base] at hT
    have arithmetic : ∀ T : Finset (Fin 4), 0 ∈ T →
        (∑ i ∈ T, subdegrees i) ∣ 280 →
        (∑ i ∈ T, subdegrees i) = 1 ∨ (∑ i ∈ T, subdegrees i) = 280 := by
      decide +kernel
    exact arithmetic T hT hdvd
  · intro x y h
    obtain ⟨g, hg⟩ := R.transitive x y h
    exact ⟨⟨g, by rw [D.stabilizer_eq_normalizer]; exact g.property⟩, hg⟩

theorem normalizer_isCoatom : IsCoatom (normalizer (D.X : Set G)) := by
  let : IsPreprimitive G D.Vertex := R.preprimitive
  have : Nontrivial D.Vertex := Finite.one_lt_card_iff_nontrivial.mp (by rw [R.vertex_card]; omega)
  simpa only [D.stabilizer_eq_normalizer, Seed.base] using
    (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := G) D.base)

theorem generate_of_moves_to_neighbor (K : Subgroup G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) (hm : ∃ k : K, (k : G) • D.base = Y) :
    K ⊔ normalizer (D.X : Set G) = ⊤ := by
  apply (R.normalizer_isCoatom.ne_iff_eq_top le_sup_right).mp
  intro he
  obtain ⟨k, hk⟩ := hm
  have hkm : (k : G) ∈ normalizer (D.X : Set G) :=
    he ▸ (show K ≤ K ⊔ normalizer (D.X : Set G) from le_sup_left) k.property
  have hkfix : (k : G) ∈ stabilizer G D.base := by
    rw [D.stabilizer_eq_normalizer]
    exact hkm
  exact hY.ne (hkfix.symm.trans hk)

theorem neighbors (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (V : D.Vertex) (hV : D.graph.Adj D.base V) :
    ∃ k : normalizer (D.X : Set G), (k : G) • Y = V :=
  R.transitive Y V ((orbitLabel_of_adj D hY).trans (orbitLabel_of_adj D hV).symm)

end FourSuborbits

/-- The actual neighbor set has the source subdegree 36. -/
theorem FourSuborbits.neighbor_card {D : Seed G} (R : FourSuborbits D) :
    {V | D.graph.Adj D.base V}.ncard = 36 := by
  have he : {V | D.graph.Adj D.base V} = {V | orbitLabel D V = 1} := by
    ext V
    exact (orbitLabel_eq_one_iff D V).symm
  rw [he, ← Nat.card_coe_set_eq]
  exact R.card 1

theorem FourSuborbits.common_neighbors_card_of_intersections {D : Seed G}
    (R : FourSuborbits D) {Y : D.Vertex} (hY : D.graph.Adj D.base Y)
    (hsl : {U | D.graph.Adj D.base U ∧ sl2Join D Y U}.ncard = 15)
    (ha5 : {U | D.graph.Adj D.base U ∧ a5Join D Y U}.ncard = 12) :
    {U | D.graph.Adj D.base U ∧ D.graph.Adj Y U}.ncard = 8 :=
  common_neighbors_card D R.joins hY R.neighbor_card hsl ha5

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
