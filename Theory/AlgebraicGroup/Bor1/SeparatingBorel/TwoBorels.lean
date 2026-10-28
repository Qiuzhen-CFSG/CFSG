module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.Borels
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.Centralizer
public import Theory.AlgebraicGroup.Bor1.SingularTorusQuotient.ToralKernel
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.Source
/-!
# Exactly two Borels in a singular codimension-one centralizer

A radical quotient sends Borels injectively to Borels because the connected
solvable radical lies in every Borel. Its rank-one maximal torus has at most
two containing Borels. Conversely, if a nonsolvable connected group had only
one Borel through its maximal torus, Borel 13.7 would make that Borel the whole
group. Thus a second Borel exists.

The final theorem constructs the actual radical quotient of the original
subtorus centralizer and applies both arguments. The torus in the centralizer
is literally the inverse image of the original maximal torus under inclusion.
No chosen root system or rank-one model is assumed.

Source: Borel, *Linear Algebraic Groups*, IV, 13.7 and 13.11(1),
`refs/KGroup/Bor1/Chapter4.tex`.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
open SemisimpleCenterContainment.RadicalGeometry BorelIntersectionGeometry
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

private theorem exists_borel_of_subtorus (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ T ≤ B := by
  have hconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  exact exists_borelSubgroup_containing_connected_solvable T hconn
    (Group.isSolvable_of_comm (isMulCommutative_iff.mp hT.isMulCommutative))

private theorem maximal_tori_dimension_eq (T U : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hU : IsMaximalTorus U) :
    Variety.dimension T.carrierVariety = Variety.dimension U.carrierVariety := by
  obtain ⟨B, hB, hTB⟩ := exists_borel_of_subtorus T hT.1
  obtain ⟨C, hC, hUC⟩ := exists_borel_of_subtorus U hU.1
  obtain ⟨g, hg⟩ := BorelGeometricConjugacy.conjugacy hB hC
  have hUgB : U.conjugate g⁻¹ ≤ B := by
    have hh := conjugate_le hUC g⁻¹
    rwa [hg, ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
      ClosedSubgroup.conjugate_one] at hh
  obtain ⟨b, hb, hUb⟩ := BorelSelfNormalizer.maximalTori_conjugate_inside_borel
    hB hT (conjugate_isMaximalTorus hU g⁻¹) hTB hUgB
  calc
    Variety.dimension T.carrierVariety = Variety.dimension (T.conjugate b).carrierVariety :=
      T.conjugate_dimension_eq b
    _ = Variety.dimension (U.conjugate g⁻¹).carrierVariety := by rw [← hUb]
    _ = Variety.dimension U.carrierVariety := (U.conjugate_dimension_eq _).symm

private theorem quotient_borel_image_injective
    {Q : Variety k} [AlgebraicGroup Q] (q : AlgebraicGroup.Morphism G Q)
    {R : ClosedSubgroup G} (hR : IsRadicalSubgroup R) (hker : q.kernel = R.toSubgroup)
    (B C : ClosedSubgroup G) (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C)
    (he : (q.comp B.inclusion).imageClosedSubgroup = (q.comp C.inclusion).imageClosedSubgroup) :
    B = C := by
  have hk (A : ClosedSubgroup G) (hA : IsBorelSubgroup A) : q.kernel ≤ A.toSubgroup := by
    rw [hker]
    exact normal_connected_solvable_le_borel R A hR.normal hR.connected hR.solvable hA
  have hle {D E : ClosedSubgroup G} (hE : IsBorelSubgroup E)
      (hDE : (q.comp D.inclusion).imageClosedSubgroup ≤ (q.comp E.inclusion).imageClosedSubgroup) :
      D ≤ E := by
    intro d hd
    have him : q.onPoints d ∈ (q.comp D.inclusion).imageClosedSubgroup :=
      ⟨D.pointEquiv.symm ⟨d, hd⟩, rfl⟩
    obtain ⟨e, he⟩ := hDE him
    have hker : (E.includePoint e)⁻¹ * d ∈ q.kernel := by
      change q.onPoints ((E.includePoint e)⁻¹ * d) = 1
      rw [map_mul, map_inv]
      change ((q.comp E.inclusion).onPoints e)⁻¹ * q.onPoints d = 1
      rw [he, inv_mul_cancel]
    have hm := E.toSubgroup.mul_mem (E.pointEquiv e).property (hk E hE hker)
    change E.includePoint e * ((E.includePoint e)⁻¹ * d) ∈ E.toSubgroup at hm
    rwa [mul_inv_cancel_left] at hm
  apply SetLike.coe_injective
  exact Set.Subset.antisymm
    (hle hC (fun _ hx => he ▸ hx)) (hle hB (fun _ hx => he.symm ▸ hx))

/-- Two Borels different from the prescribed Borel coincide when the actual
radical quotient has semisimple rank one. -/
theorem other_borel_unique_of_rankOne_radical_quotient
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism G Q) (hq : Function.Surjective q.onPoints)
    (R : ClosedSubgroup G) (hR : IsRadicalSubgroup R) (hker : q.kernel = R.toSubgroup)
    (hQ : Variety.IsConnected Q) (U : ClosedSubgroup Q) (hU : IsMaximalTorus U)
    (hUdim : Variety.dimension U.carrierVariety = 1)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (B C D : ClosedSubgroup G) (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C)
    (hD : IsBorelSubgroup D) (hTB : T ≤ B) (hTC : T ≤ C) (hTD : T ≤ D)
    (hCB : C ≠ B) (hDB : D ≠ B) : C = D := by
  let U' := (q.comp T.inclusion).imageClosedSubgroup
  have hU' : IsMaximalTorus U' := maximalTorus_image_of_solvable_kernel q hq
    (hR.quotient_kernel_isSolvable q hker) hT
  have hdim : Variety.dimension U'.carrierVariety = 1 :=
    (maximal_tori_dimension_eq U' U hU' hU).trans hUdim
  have hBq (A : ClosedSubgroup G) (hA : IsBorelSubgroup A) :
      IsBorelSubgroup (q.comp A.inclusion).imageClosedSubgroup :=
    TorusFree.borel_image_of_solvable_kernel q hq (hR.quotient_kernel_isSolvable q hker) A hA
  have hle (A : ClosedSubgroup G) (hTA : T ≤ A) :
      U' ≤ (q.comp A.inclusion).imageClosedSubgroup := by
    rintro y ⟨t, rfl⟩
    exact ⟨A.pointEquiv.symm ⟨T.includePoint t, hTA (T.pointEquiv t).property⟩, rfl⟩
  apply quotient_borel_image_injective q hR hker C D hC hD
  apply RankOneGeometry.rank_one_other_borel_unique hQ U' hU' hdim
    _ _ _ (hBq B hB) (hBq C hC) (hBq D hD) (hle B hTB) (hle C hTC) (hle D hTD)
  · exact fun he => hCB (quotient_borel_image_injective q hR hker C B hC hB he)
  · exact fun he => hDB (quotient_borel_image_injective q hR hker D B hD hB he)

/-- Nonsolvability and Borel 13.7 give a second Borel containing the torus. -/
theorem exists_other_borel_of_not_solvable
    (hG : Variety.IsConnected G) (hns : ¬ Group.IsSolvable (Variety.Point G))
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    ∃ C : ClosedSubgroup G, IsBorelSubgroup C ∧ T ≤ C ∧ C ≠ B := by
  by_contra! h
  have htop := TorusBorelGeneration.closure_borels_containing_maximalTorus_eq_top hG T hT
  have hle : Subgroup.closure (⋃ C : BorelContainingIndex T,
      (C.1 : Set (Variety.Point G))) ≤ B.toSubgroup := by
    apply (Subgroup.closure_le B.toSubgroup).mpr
    intro x hx
    obtain ⟨C, hx⟩ := Set.mem_iUnion.mp hx
    exact h C.1 C.2.1 C.2.2 ▸ hx
  rw [htop] at hle
  have hsurj : Function.Surjective B.inclusion.onPoints := by
    intro g
    exact ⟨B.pointEquiv.symm ⟨g, hle (Subgroup.mem_top g)⟩, rfl⟩
  let := hB.solvable
  exact hns (Group.isSolvable_of_surjective (f := B.inclusion.onPoints) hsurj)

theorem maximalTorus_preimage_inclusion (T H : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hTH : T ≤ H) :
    IsMaximalTorus (H.inclusion.closedSubgroupPreimage T) := by
  let j := T.inclusion.codRestrictClosedSubgroup H
    (fun x => hTH (T.pointEquiv x).property)
  have he : j.imageClosedSubgroup = H.inclusion.closedSubgroupPreimage T := by
    apply SetLike.coe_injective
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change H.inclusion.onPoints (j.onPoints t) ∈ T
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
      exact (T.pointEquiv t).property
    · intro hx
      refine ⟨T.pointEquiv.symm ⟨H.includePoint x, hx⟩, H.inclusion_injective ?_⟩
      rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
      rfl
  refine ⟨he ▸ morphism_image_isTorus j hT.1, ?_⟩
  intro A hA hTA
  let _ : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
  let f := H.inclusion.comp A.inclusion
  have hTf : T ≤ f.imageClosedSubgroup := by
    intro t ht
    let x := H.pointEquiv.symm ⟨t, hTH ht⟩
    have hx : x ∈ A := hTA ht
    exact ⟨A.pointEquiv.symm ⟨x, hx⟩, rfl⟩
  have hfT := hT.2 _ (morphism_image_isTorus f hA) hTf
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro a ha
    change H.inclusion.onPoints a ∈ T
    rw [← hfT]
    exact ⟨A.pointEquiv.symm ⟨a, ha⟩, rfl⟩
  · exact hTA

/-- The centralizer of the original singular codimension-one subtorus has
exactly two Borels through the original torus. The quotient and its rank-one
geometry are derived from the source hypotheses. -/
theorem centralizer_borels_exactly_two
    (hG : Variety.IsConnected G) (S T : ClosedSubgroup G)
    (hS : IsSubtorus S) (hT : IsMaximalTorus T) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hns : ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (B : ClosedSubgroup S.centralizer.carrierVariety) (hB : IsBorelSubgroup B)
    (hTB : S.centralizer.inclusion.closedSubgroupPreimage T ≤ B) :
    ∃ C : ClosedSubgroup S.centralizer.carrierVariety,
      IsBorelSubgroup C ∧ S.centralizer.inclusion.closedSubgroupPreimage T ≤ C ∧ C ≠ B ∧
      ∀ D : ClosedSubgroup S.centralizer.carrierVariety, IsBorelSubgroup D →
        S.centralizer.inclusion.closedSubgroupPreimage T ≤ D → D = B ∨ D = C := by
  have hTC : T ≤ S.centralizer := by
    intro t ht
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht) s (hST hs)
  have hTi := maximalTorus_preimage_inclusion T S.centralizer hT hTC
  have hH := SemisimpleCenterContainment.CartanGeometry.subtorus_centralizer_isConnected hG hS
  obtain ⟨C, hC, hTC, hCB⟩ := exists_other_borel_of_not_solvable hH hns _ hTi B hB
  obtain ⟨q⟩ := SingularTorusQuotient.centralizer_rankOne_quotient_of_not_solvable
    hG hS hT hST hcodim hns
  let _ : AlgebraicGroup q.quotient := q.quotientAlgebraicGroup
  have hk : q.quotientMap.kernel = q.radical.toSubgroup := by
    apply Subgroup.ext
    intro x
    change x ∈ q.quotientMap.kernelClosedSubgroup ↔ x ∈ q.radical
    rw [q.kernel_eq_radical]
  refine ⟨C, hC, hTC, hCB, ?_⟩
  intro D hD hTD
  by_cases hDB : D = B
  · exact Or.inl hDB
  · exact Or.inr (other_borel_unique_of_rankOne_radical_quotient q.quotientMap q.surjective
      q.radical q.radical_isRadical hk q.quotient_isSemisimple.1 q.quotientTorus
      q.quotientTorus_isMaximal q.quotientTorus_dimension _ hTi B D C hB hD hC
      hTB hTD hTC hDB hCB)

end Theory.AlgebraicGroup.Bor1.SeparatingBorel
