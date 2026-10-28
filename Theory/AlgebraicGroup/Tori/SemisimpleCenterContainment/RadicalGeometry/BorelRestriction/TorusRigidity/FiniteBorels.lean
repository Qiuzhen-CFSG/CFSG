module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.Transitivity
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.Generation
public import Theory.AlgebraicGroup.Tori.CartanStructure
public import Theory.AlgebraicGroup.Borel.ElementCoverage.RegularWitness.Transporter

/-!
# Solvable torus centralizers and finitely many containing Borels

Borel restriction implies that a solvable subtorus centralizer lies in every
Borel containing that subtorus. Choose an ambient maximal torus containing it.
All the original Borels therefore contain this maximal torus. Such Borels
are conjugate under the torus normalizer; its identity component lies in the
centralizer and hence in the prescribed Borel. The finite component quotient
thus parametrizes a finite family of Borels.

Consequently a singular subtorus has a nonsolvable centralizer. These are
Borel, *Linear Algebraic Groups*, §11.15 corollary and §13.1, expressed using
the literal `BorelContainingIndex` family and the actual ambient centralizer.
-/

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
set_option backward.isDefEq.respectTransparency false
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

public theorem centralizer_le_borel_of_solvable (hG : Variety.IsConnected G)
    {S B : ClosedSubgroup G} (hS : IsSubtorus S) (hB : IsBorelSubgroup B) (hSB : S ≤ B)
    (hsolv : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety)) : S.centralizer ≤ B := by
  have hK := isBorel_centralizer_restriction hG S B hS hB hSB
  have htopc : _root_.IsConnected
      ((ClosedSubgroup.top : ClosedSubgroup S.centralizer.carrierVariety) : Set (Variety.Point S.centralizer.carrierVariety)) :=
    CartanGeometry.subtorus_centralizer_isConnected hG hS
  let : AlgebraicGroup (ClosedSubgroup.top : ClosedSubgroup S.centralizer.carrierVariety).carrierVariety :=
    ClosedSubgroup.carrierAlgebraicGroup _
  have htops : Group.IsSolvable
      (Variety.Point (ClosedSubgroup.top : ClosedSubgroup S.centralizer.carrierVariety).carrierVariety) := by
    let := hsolv
    exact Group.isSolvable_of_isSolvable_injective (ClosedSubgroup.top : ClosedSubgroup S.centralizer.carrierVariety).inclusion_injective
  have he := hK.maximal ClosedSubgroup.top htopc htops (fun _ _ => trivial)
  intro x hx
  let c := S.centralizer.pointEquiv.symm ⟨x, hx⟩
  have hc : c ∈ (S.centralizer.inclusion.closedSubgroupPreimage B).toSubgroup := by
    rw [← he]
    trivial
  exact hc

public theorem finite_borels_containing_maximalTorus (hG : Variety.IsConnected G)
    {T : ClosedSubgroup G} (hT : IsMaximalTorus T) : Finite (BorelContainingIndex T) := by
  classical
  by_cases hex : Nonempty (BorelContainingIndex T)
  swap
  · let : IsEmpty (BorelContainingIndex T) := not_nonempty_iff.mp hex
    infer_instance
  let B := Classical.choice hex
  have hCTB : T.centralizer ≤ B.1 := centralizer_le_borel_of_solvable hG hT.1 B.2.1 B.2.2
    (CartanGeometry.maximalTorus_centralizer_connected_solvable hG hT).2
  let N := T.normalizer.toSubgroup
  let K := B.1.toSubgroup.subgroupOf N
  have hN0B : T.normalizer.identityComponentAmbient ≤ B.1 :=
    fun x hx => hCTB (CartanStructure.torus_normalizer_identityComponent_le_centralizer hT hx)
  let : K.FiniteIndex := BorelElementCoverage.finiteIndex_subgroupOf_of_identityComponentAmbient_le B.1 T.normalizer hN0B
  let : Finite (Quotient (QuotientGroup.leftRel K)) := Subgroup.finite_quotient_of_finiteIndex
  let f : Quotient (QuotientGroup.leftRel K) → ClosedSubgroup G :=
    @Quotient.lift N (ClosedSubgroup G) (QuotientGroup.leftRel K)
      (fun n => B.1.conjugate n.1) (by
        intro a b hab
        have hab' : a.1⁻¹ * b.1 ∈ B.1.toSubgroup :=
          (QuotientGroup.leftRel_apply (s := K) (x := a) (y := b)).mp hab
        have hb : b.1 = a.1 * (a.1⁻¹ * b.1) := by group
        rw [hb, ← ClosedSubgroup.conjugate_conjugate,
          ClosedSubgroup.conjugate_eq_self_of_mem_normalizer _ (Subgroup.le_normalizer hab')])
  have hsub : {C : ClosedSubgroup G | IsBorelSubgroup C ∧ T ≤ C} ⊆ Set.range f := by
    intro C hC
    obtain ⟨n, hn, hCn⟩ := BorelIntersectionGeometry.normalizer_conjugate_of_borel_conjugate
      B.2.1 hT B.2.2 hC.2 (BorelGeometricConjugacy.conjugacy B.2.1 hC.1)
    exact ⟨@Quotient.mk' N (QuotientGroup.leftRel K) (⟨n, hn⟩ : N), hCn.symm⟩
  exact Set.Finite.to_subtype ((Set.finite_range f).subset hsub)

public theorem finite_borels_containing_subtorus_of_solvable_centralizer
    (hG : Variety.IsConnected G) {S : ClosedSubgroup G} (hS : IsSubtorus S)
    (hsolv : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety)) :
    Finite (BorelContainingIndex S) := by
  obtain ⟨T, hT, hST⟩ := exists_maximalTorus_containing S hS
  have hTC : T ≤ S.centralizer := by
    intro t ht
    change t ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT ht) s (hST hs)
  let f : BorelContainingIndex S → BorelContainingIndex T :=
    fun B => ⟨B.1, B.2.1, fun x hx => centralizer_le_borel_of_solvable hG hS B.2.1 B.2.2 hsolv (hTC hx)⟩
  let := finite_borels_containing_maximalTorus hG hT
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun C : BorelContainingIndex T => C.1) hab

public theorem centralizer_not_solvable_of_infinite_borels (hG : Variety.IsConnected G)
    {S : ClosedSubgroup G} (hS : IsSubtorus S) (hsing : Infinite (BorelContainingIndex S)) :
    ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety) := by
  intro hsolv
  let : Infinite (BorelContainingIndex S) := hsing
  let := finite_borels_containing_subtorus_of_solvable_centralizer hG hS hsolv
  exact not_finite (BorelContainingIndex S)
end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
