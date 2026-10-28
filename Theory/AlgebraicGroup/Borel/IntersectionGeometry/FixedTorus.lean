module

public import Theory.AlgebraicGroup.RootSubgroups.FixedTorusConnectedGeneration
public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs
public import Theory.AlgebraicGroup.Borel.Conjugation.theorem_1_6_2_b
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.Transport

/-!
The final reductions for Borel intersections at a fixed maximal torus.

The common-root formula identifies an intersection with the subgroup generated
by the torus and the common positive-root groups. Connected generation then
proves connectedness. For opposite positive systems there are no common roots,
so the same formula identifies the intersection with the fixed torus itself.

Sources: GLS3, Theorems 1.11.2 and 1.11.4, and Borel, *Linear Algebraic
Groups*, §§14.1 and 14.4–14.5. The constructions of compatible Borel/root
witnesses and the common-root intersection formula remain explicit inputs to
the assembly theorem here. This module does not yet prove the unconditional
fixed-torus source statements.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The common-root decomposition implies connectedness, because its factors
are a torus and connected one-parameter root groups. -/
public theorem inter_isConnected_of_root_decomposition
    (B C T : ClosedSubgroup G) (hT : IsSubtorus T)
    (D : RootGroupData G T) (hD : D.IsRealization) (A : Set D.Root)
    (hinter : (B.inter C).toSubgroup =
      T.toSubgroup ⊔ RootSubgroupGenerated D A) :
    _root_.IsConnected (B.inter C : Set (Variety.Point G)) := by
  have hconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  change _root_.IsConnected ((B.inter C).toSubgroup : Set (Variety.Point G))
  rw [hinter]
  exact isConnected_sup_rootSubgroupGenerated T hconn D hD A

omit [IsAlgClosed k] in
/-- Opposite positive systems have no common roots; their common-root
decomposition therefore reduces to the torus. -/
public theorem inter_eq_torus_of_opposite_root_decomposition
    (B C T : ClosedSubgroup G) (D : RootGroupData G T)
    (P : Set D.Root) (hP : IsPositiveSystem D P)
    (hinter : (B.inter C).toSubgroup =
      T.toSubgroup ⊔ RootSubgroupGenerated D (P ∩ D.neg ⁻¹' P)) :
    B.inter C = T := by
  have heq : (B.inter C).toSubgroup = T.toSubgroup := by
    simpa only [hP.1, RootSubgroupGenerated_empty, sup_bot_eq] using hinter
  exact SetLike.coe_injective
    (congrArg (fun H : Subgroup (Variety.Point G) => (H : Set (Variety.Point G))) heq)

/-- Conditional assembly of the two fixed-torus conclusions. The three
geometric inputs are positive-root witnesses for Borels containing `T`, an
opposite witness for the chosen positive system, and the common-root formula.
They must be constructed from reductivity in the unconditional source proof. -/
public theorem fixedTorus_geometry_of_root_witnesses
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (D : RootGroupData G T) (hD : D.IsRealization)
    (P : Set D.Root) (hP : IsPositiveSystem D P)
    (hBP : IsBorelOfPositiveSystem D P B)
    (hclassify : ∀ C : ClosedSubgroup G, IsBorelSubgroup C → T ≤ C →
      ∃ Q : Set D.Root, IsPositiveSystem D Q ∧
        Nonempty (IsBorelOfPositiveSystem D Q C))
    (hopposite : ∃ C : ClosedSubgroup G,
      IsPositiveSystem D (D.neg ⁻¹' P) ∧
        Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' P) C))
    (hinter : ∀ (C : ClosedSubgroup G) (Q : Set D.Root),
      IsPositiveSystem D Q → IsBorelOfPositiveSystem D Q C →
      IsPositiveSystem D P → IsBorelOfPositiveSystem D P B →
      (B.inter C).toSubgroup =
        T.toSubgroup ⊔ RootSubgroupGenerated D (P ∩ Q)) :
    (∀ n : Variety.Point G, n ∈ T.normalizer.toSubgroup →
      _root_.IsConnected (B.inter (B.conjugate n) : Set (Variety.Point G))) ∧
    (∃ C : ClosedSubgroup G, IsBorelSubgroup C ∧ B.inter C = T) := by
  constructor
  · intro n hn
    have hTn : T.conjugate n = T :=
      ClosedSubgroup.conjugate_eq_self_of_mem_normalizer n hn
    have hTC : T ≤ B.conjugate n := by
      simpa only [hTn] using conjugate_le hTB n
    obtain ⟨Q, hQ, ⟨hCQ⟩⟩ := hclassify (B.conjugate n) (hB.conjugate n) hTC
    exact inter_isConnected_of_root_decomposition B (B.conjugate n) T hT.1
      D hD (P ∩ Q) (hinter _ Q hQ hCQ hP hBP)
  · obtain ⟨C, hQ, ⟨hCQ⟩⟩ := hopposite
    exact ⟨C, hCQ.borel, inter_eq_torus_of_opposite_root_decomposition
      B C T D P hP (hinter C _ hQ hCQ hP hBP)⟩

end Theory.AlgebraicGroup.BorelIntersectionGeometry
