module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Model
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Projection
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections

/-!
# Coordinates for the binary component's central Sylow involution

The actual PSL action transports Sylow subgroups to the binary linear group.
Its nonidentity Sylow-centralizing elements are transvections, giving the
coordinates used by the centralizer geometry. In the local setup, the
component Sylow intersection and its centrality are supplied by the proved
projection lemmas. No block obstruction or classification conclusion is used.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup
variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} [NeZero n]

/-- Nonidentity elements centralizing a binary component Sylow subgroup have
rank-one coordinates in the actual matrix action. -/
theorem exists_transvectionCoordinates_of_centralizes_sylow
    (hn : 2 ≤ n) (e : L ≃* PSL n) (T : Sylow 2 L) {t : L}
    (ht : t ≠ 1) (hc : ∀ x : L, x ∈ T → x * t = t * x) :
    Nonempty (TransvectionCoordinates e t) := by
  let a := linearModel e
  let : Finite L := Finite.of_injective e e.injective
  let U := T.mapSurjective (f := a.toMonoidHom) a.surjective
  have ha : a t ≠ 1 := by
    intro he
    exact ht (a.injective (he.trans a.map_one.symm))
  have hU : ∀ x : BinaryLinear.GL (Vector n), x ∈ U → x * a t = a t * x := by
    intro x hx
    change x ∈ (T : Subgroup L).map a.toMonoidHom at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change a y * a t = a t * a y
    simpa only [map_mul] using congrArg a (hc y hy)
  have hV : 2 ∣ Nat.card (Vector n) := by
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    exact dvd_pow_self 2 (by omega)
  have hdim : 1 < Module.finrank (ZMod 2) (Vector n) := by
    rw [Module.finrank_fin_fun]
    omega
  obtain ⟨w, f, hw, hf, hfw, hact⟩ :=
    BinaryLinear.central_sylow_eq_transvection hV hdim U ha hU
  exact ⟨⟨w, f, hw, hf, hfw, hact⟩⟩

/-- The degree-four and degree-five central involutions required by the
binary parabolic-pair argument have actual transvection coordinates. -/
theorem exists_transvectionCoordinates (hn : n = 4 ∨ n = 5)
    (e : L ≃* PSL n) (T : Sylow 2 L) {t : L} (ht : orderOf t = 2)
    (hc : ∀ x : L, x ∈ T → x * t = t * x) :
    Nonempty (TransvectionCoordinates e t) := by
  apply exists_transvectionCoordinates_of_centralizes_sylow (by omega) e T _ hc
  intro he
  simp [he] at ht

/-- Construct the coordinates from the source's actual involution projection. -/
theorem projection_transvectionCoordinates {H M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (hn : n = 4 ∨ n = 5) (e : L ≃* PSL n)
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    Nonempty (TransvectionCoordinates e t) := by
  obtain ⟨T, hT⟩ := exists_component_sylow h
  exact exists_transvectionCoordinates hn e T ht2
    (projection_mem_center_component_sylow h e ht ht2 T hT).2

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
