module

public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected

/-!
# A Borel of maximal dimension

The finite ambient dimension bounds the dimensions of all Borels, so a nonempty
family has a member of maximal dimension. Every solvable closed subgroup has
dimension at most this maximum: its identity component is connected solvable,
lies in a Borel, and has the same dimension as the original subgroup.

This supplies the stabilizer bound in Borel, *Linear Algebraic Groups*, §11.1,
including the case of disconnected flag stabilizers and disconnected ambient
groups. It does not assert that an orbit with this stabilizer is closed.
-/

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

omit [IsAlgClosed k] in
/-- There is a Borel of maximal dimension among all Borels. -/
public theorem exists_borel_of_maximal_dimension
    (B₀ : ClosedSubgroup G) (hB₀ : IsBorelSubgroup B₀) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧
      ∀ C : ClosedSubgroup G, IsBorelSubgroup C →
        Variety.dimension C.carrierVariety ≤ Variety.dimension B.carrierVariety := by
  let S : Set ℕ := {n | ∃ B : ClosedSubgroup G,
    IsBorelSubgroup B ∧ Cardinal.toNat (Variety.dimension B.carrierVariety) = n}
  have hS : S.Finite := by
    apply (Set.finite_Iic (Cardinal.toNat (Variety.dimension G))).subset
    rintro n ⟨B, _, rfl⟩
    exact Cardinal.toNat_le_toNat
      (closedSubvariety_dimension_le G B.isZariskiClosed) (variety_dimension_lt_aleph0 G)
  obtain ⟨n, ⟨B, hB, rfl⟩, hmax⟩ :=
    Set.exists_max_image S id hS ⟨_, B₀, hB₀, rfl⟩
  refine ⟨B, hB, fun C hC => ?_⟩
  exact (Cardinal.toNat_le_iff_le_of_lt_aleph0
    (variety_dimension_lt_aleph0 C.carrierVariety)
    (variety_dimension_lt_aleph0 B.carrierVariety)).mp
      (hmax _ ⟨C, hC, rfl⟩)

omit [IsAlgClosed k] in
private theorem solvable_of_le
    (K H : ClosedSubgroup G) (hKH : K ≤ H)
    (hH : Group.IsSolvable (Variety.Point H.carrierVariety)) :
    Group.IsSolvable (Variety.Point K.carrierVariety) := by
  let eH : Variety.Point H.carrierVariety ≃* H.toSubgroup := Equiv.mulEquiv H.pointEquiv
  let eK : Variety.Point K.carrierVariety ≃* K.toSubgroup := Equiv.mulEquiv K.pointEquiv
  let f : Variety.Point K.carrierVariety →* Variety.Point H.carrierVariety :=
    eH.symm.toMonoidHom.comp ((Subgroup.inclusion hKH).comp eK.toMonoidHom)
  let := hH
  exact Group.isSolvable_of_isSolvable_injective
    (f := f) (eH.symm.injective.comp ((Subgroup.inclusion_injective hKH).comp eK.injective))

/-- The dimension of a possibly disconnected solvable closed subgroup is bounded
by a maximal-dimensional Borel: apply Borel containment to its identity component. -/
public theorem solvable_dimension_le_of_borel_maximal_dimension
    (B : ClosedSubgroup G)
    (hmax : ∀ C : ClosedSubgroup G, IsBorelSubgroup C →
      Variety.dimension C.carrierVariety ≤ Variety.dimension B.carrierVariety)
    (H : ClosedSubgroup G)
    (hH : Group.IsSolvable (Variety.Point H.carrierVariety)) :
    Variety.dimension H.carrierVariety ≤ Variety.dimension B.carrierVariety := by
  have hH₀ := solvable_of_le H.identityComponentAmbient H
    H.identityComponentAmbient_le hH
  obtain ⟨C, hC, hHC⟩ := exists_borelSubgroup_containing_connected_solvable
    H.identityComponentAmbient H.identityComponentAmbient_isConnected hH₀
  rw [← H.dimension_identityComponentAmbient]
  exact (connected_closedSubgroup_dimension_le_of_le H.identityComponentAmbient C
    H.identityComponentAmbient_isConnected hHC).trans (hmax C hC)

end Theory.AlgebraicGroup.BorelGeometricConjugacy
