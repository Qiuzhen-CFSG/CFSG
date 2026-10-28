module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.SylowCommutingJoin

/-!
# Sylow containment from every component

Distinct components commute. A p-subgroup containing a Sylow subgroup of
each component therefore contains a Sylow subgroup of the entire layer.
Its intersection with the layer is exactly that Sylow subgroup. The proof
uses the actual commuting product, allowing central component intersections.

Source application: Aschbacher--Smith 2.5.3(4), printed p.552.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_layer_sylow_eq_inf (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hL : ∀ L : Subgroup G, IsComponent G L →
      ∃ P : Sylow p L, (P : Subgroup L).map L.subtype ≤ Q) :
    ∃ P : Sylow p (componentLayer G),
      (P : Subgroup (componentLayer G)).map (componentLayer G).subtype =
        componentLayer G ⊓ Q := by
  classical
  let I := {L : Subgroup G // IsComponent G L}
  let C : I → Subgroup G := Subtype.val
  have he : (⨆ i, C i) = componentLayer G := (sSup_eq_iSup' _).symm
  have hc : Pairwise fun i j : I => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    have hh := i.property.commutator_eq_bot_of_ne j.property
      (fun h => hij (Subtype.ext h))
    exact ((commutator_eq_bot_iff_le_centralizer.mp hh) hx y hy).symm
  choose P hP using fun i : I => hL i.val i.property
  obtain ⟨R, hR⟩ := exists_sylow_iSup_le_of_commuting C hc P Q hP
  let e := MulEquiv.subgroupCongr he
  let T := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : (T : Subgroup (componentLayer G)).map (componentLayer G).subtype ≤ Q := by
    change ((R : Subgroup (⨆ i, C i : Subgroup G)).map e.toMonoidHom).map _ ≤ Q
    rw [map_map]
    exact hR
  have hi : Q.subgroupOf (componentLayer G) = (T : Subgroup (componentLayer G)) :=
    T.is_maximal' hQ.comap_subtype (map_le_iff_le_comap.mp hT)
  refine ⟨T, ?_⟩
  rw [← hi, subgroupOf_map_subtype, inf_comm]

end Theory.GroupTheory
