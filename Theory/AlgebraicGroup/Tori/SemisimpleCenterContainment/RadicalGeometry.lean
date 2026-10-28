module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.Algebra

/-!
The algebraic reduction for radicals of torus centralizers in reductive groups.

A connected normal solvable subgroup lies in every Borel, since its product
with a Borel is again closed, connected and solvable. Apply this inside the
torus centralizer and map its connected unipotent radical into the ambient
group. Borel restriction places that image in every Borel containing a maximal
torus, hence in their intersection's identity component `I(T)`. If `I(T)_u`
is ambient normal, reductivity kills it and therefore kills the image. The
unipotent-radical quotient theorem, applied to the identity map, then gives
torality of all radicals of the centralizer.

Source: Borel, *Linear Algebraic Groups*, Chapter IV, 13.16 and 13.17,
Corollary 1(a) and Corollary 2(a). The final assembly below keeps two missing
geometric inputs explicit: Borel restriction (11.15) and ambient normality
of `I(T)_u` (13.16). Thus it is a conditional reduction, not yet the source
centralizer-reductivity theorem. Relative normality is used only inside the
centralizer; its unipotent radical's ambient image is not assumed normal.
-/

universe u
set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem carrier_connected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- The algebraic implication in 13.17(1a,2a). The two geometric inputs are
Borel restriction to the centralizer (11.15) and ambient normality of the
unipotent radical of `I(T)` (13.16). Normality of `U` is used only inside `C`;
its image in the ambient group is killed by Borel containment. -/
public theorem isReductive_of_borel_restrictions_of_intersection_radical_normal
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) (C T : ClosedSubgroup G)
    (hC : Variety.IsConnected C.carrierVariety) (hT : IsSubtorus T)
    (hfixed : ∀ B : ClosedSubgroup G, IsBorelSubgroup B → T ≤ B →
      IsBorelSubgroup (C.inclusion.closedSubgroupPreimage B))
    (hnormal : ∀ V : ClosedSubgroup G,
      IsUnipotentRadicalOf (torusBorelIntersection T) V → V.toSubgroup.Normal) :
    IsReductiveAlgebraicGroup C.carrierVariety := by
  apply isReductive_of_connected_normal_unipotent_trivial hC
  intro U hUn hUc hUu
  letI : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism U.carrierVariety G := C.inclusion.comp U.inclusion
  let A := f.imageClosedSubgroup
  have hAc : _root_.IsConnected (A : Set (Variety.Point G)) :=
    f.imageClosedSubgroup_isConnected (carrier_connected U hUc)
  have hAu : IsUnipotentAlgebraicGroup A.carrierVariety := by
    obtain ⟨π, hπ, _, _⟩ := f.closedImageProjection_exists
    exact hUu.of_surjective π hπ
  have hAB : ∀ B : ClosedSubgroup G, IsBorelSubgroup B → T ≤ B → A ≤ B := by
    intro B hB hTB
    have hUB := normal_connected_solvable_le_borel U
      (C.inclusion.closedSubgroupPreimage B) hUn hUc
      (isSolvable_of_isUnipotentAlgebraicGroup hUu) (hfixed B hB hTB)
    rintro x ⟨u, rfl⟩
    exact hUB (U.pointEquiv u).property
  have hAbot :=
    unipotent_eq_bot_of_borel_containment_of_intersection_radical_normal
      hG T A hT hAc hAu hAB hnormal
  apply le_antisymm
  · intro x hx
    apply Subgroup.mem_bot.mpr
    apply C.inclusion_injective
    rw [map_one]
    have hm : C.inclusion.onPoints x ∈ A :=
      ⟨U.pointEquiv.symm ⟨x, hx⟩, rfl⟩
    exact Subgroup.mem_bot.mp (hAbot ▸ hm)
  · exact bot_le

/-- Conditional assembly for a subtorus centralizer. The geometric premises
are deliberately explicit until 11.15 and 13.16 have been established. -/
public theorem centralizer_radical_isSubtorus_of_borel_geometry
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsReductiveAlgebraicGroup G) (S : ClosedSubgroup G)
    (hS : IsSubtorus S) (hC : Variety.IsConnected S.centralizer.carrierVariety)
    (hfixed : ∀ B : ClosedSubgroup G, IsBorelSubgroup B → S ≤ B →
      IsBorelSubgroup (S.centralizer.inclusion.closedSubgroupPreimage B))
    (hnormal : ∀ T : ClosedSubgroup G, IsMaximalTorus T →
      ∀ V : ClosedSubgroup G,
        IsUnipotentRadicalOf (torusBorelIntersection T) V → V.toSubgroup.Normal)
    (R : ClosedSubgroup S.centralizer.carrierVariety) (hR : IsRadicalSubgroup R) :
    IsSubtorus R := by
  obtain ⟨T, hT, hST⟩ := exists_maximalTorus_containing S hS
  have hred := isReductive_of_borel_restrictions_of_intersection_radical_normal
    hG S.centralizer T hC hT.1
    (fun B hB hTB => hfixed B hB (fun x hx => hTB (hST hx)))
    (hnormal T hT)
  exact hred.2 R hR

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry
