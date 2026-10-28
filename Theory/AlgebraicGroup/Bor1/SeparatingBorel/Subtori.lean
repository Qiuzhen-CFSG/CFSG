module
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Cocharacters

/-!
# Separation on the literal codimension-one subtori

A nontrivial character trivial on a codimension-one subtorus has precisely
that subtorus as its ambient connected kernel. Connectedness supplies
containment in the connected kernel; equal dimensions then give equality.
Consequently characters trivial on distinct codimension-one subtori are
separated by an actual cocharacter, avoiding finitely many other characters.

Source: Borel, *Linear Algebraic Groups*, IV, 13.12, character-kernel step.
The orientation characters themselves and their Borel restriction criterion
belong to 13.11(3) and are not assumed proved by this module.
-/
public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

private theorem torus_connected (S : ClosedSubgroup G) (hS : IsSubtorus S) :
    _root_.IsConnected (S : Set (Variety.Point G)) := by
  let : ConnectedSpace (Variety.Point S.carrierVariety) := connectedSpace_iff_univ.mpr hS.isConnected
  change _root_.IsConnected (S.toSubgroup : Set (Variety.Point G))
  rw [← S.range_inclusion]
  exact isConnected_range S.inclusion.toVariety.continuous

theorem subtorus_le_ambientConnectedKernel
    (T S : ClosedSubgroup G) (hS : IsSubtorus S) (hST : S ≤ T)
    (χ : TorusWeight T)
    (hkill : ∀ x : Variety.Point T.carrierVariety,
      T.inclusion.onPoints x ∈ S → χ.onPoints x = 1) : S ≤ χ.ambientConnectedKernel T := by
  let : AlgebraicGroup χ.connectedKernel.carrierVariety := χ.connectedKernel.carrierAlgebraicGroup
  let j := S.inclusion.codRestrictClosedSubgroup T
    (fun x => hST (S.pointEquiv x).property)
  have hj : j.imageClosedSubgroup ≤ χ.kernelClosedSubgroup := by
    rintro x ⟨s,rfl⟩
    apply hkill
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact (S.pointEquiv s).property
  have hjK : j.imageClosedSubgroup ≤ χ.connectedKernel :=
    connected_closedSubgroup_le_identityComponentAmbient _ _
      (j.imageClosedSubgroup_isConnected hS.isConnected) hj
  intro s hs
  let y := S.pointEquiv.symm ⟨s,hs⟩
  have hy : j.onPoints y ∈ χ.connectedKernel := hjK ⟨y,rfl⟩
  let z := χ.connectedKernel.pointEquiv.symm ⟨j.onPoints y,hy⟩
  change ∃ z : Variety.Point χ.connectedKernel.carrierVariety,
    T.inclusion.onPoints (χ.connectedKernel.inclusion.onPoints z) = s
  refine ⟨z, ?_⟩
  change T.inclusion.onPoints (j.onPoints y) = s
  rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
  rfl

theorem ambientConnectedKernel_eq_of_codimension_one
    (T S : ClosedSubgroup G) (hT : IsSubtorus T) (hS : IsSubtorus S) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (χ : TorusWeight T) (hχ : χ ≠ 1)
    (hkill : ∀ x : Variety.Point T.carrierVariety,
      T.inclusion.onPoints x ∈ S → χ.onPoints x = 1) : χ.ambientConnectedKernel T = S := by
  have hdata := χ.connectedKernel_codimension_one T hT hχ
  have hle := subtorus_le_ambientConnectedKernel T S hS hST χ hkill
  have hdim : Variety.dimension S.carrierVariety =
      Variety.dimension (χ.ambientConnectedKernel T).carrierVariety := by
    apply (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.one_lt_aleph0).mp
    exact hcodim.trans hdata.ambientConnectedKernel_dimension_add_one.symm
  by_contra hne
  have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne S
    (χ.ambientConnectedKernel T) hle (Ne.symm hne) (torus_connected S hS)
    hdata.ambientConnectedKernel_connected
  exact (ne_of_lt hlt) hdim

theorem exists_cocharacter_separating_codimension_one_subtori
    (T S Q : ClosedSubgroup G) (hT : IsSubtorus T)
    (hS : IsSubtorus S) (hQ : IsSubtorus Q) (hST : S ≤ T) (hQT : Q ≤ T)
    (hScodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hQcodim : Variety.dimension Q.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hSQ : S ≠ Q) (α β : TorusWeight T) (hα : α ≠ 1) (hβ : β ≠ 1)
    (hαS : ∀ x : Variety.Point T.carrierVariety,
      T.inclusion.onPoints x ∈ S → α.onPoints x = 1)
    (hβQ : ∀ x : Variety.Point T.carrierVariety,
      T.inclusion.onPoints x ∈ Q → β.onPoints x = 1)
    (s : Finset (TorusWeight T)) (hs : ∀ χ ∈ s, χ ≠ 1) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      0 < characterCocharacterPairing T c (Additive.ofMul α) ∧
      characterCocharacterPairing T c (Additive.ofMul β) < 0 ∧
      ∀ χ ∈ s, characterCocharacterPairing T c (Additive.ofMul χ) ≠ 0 := by
  exact exists_cocharacter_of_distinct_connectedKernels T hT S Q α β hα hβ
    (ambientConnectedKernel_eq_of_codimension_one T S hT hS hST hScodim α hα hαS)
    (ambientConnectedKernel_eq_of_codimension_one T Q hT hQ hQT hQcodim β hβ hβQ)
    hSQ s hs
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
