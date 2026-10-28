module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.GraphField.Pinning
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels

/-!
# Native Frobenius and triality preserve the Spin D4 positive Borel

The published root formulas carry each positive root group to a positive root
group. The actual positive Borel is the supremum of those groups and the
coroot torus, so its preservation follows on the original Clifford carrier.
For triality, positivity follows by addition induction from its permutation
of the chosen simple roots; the inverse is the square of the same map.

The Frobenius torus formula uses the genuine coroot-coordinate isomorphism,
and the triality coroot formula retains its forward numbered arm cycle.
These are the native clauses used by `OrdinaryFrobenius` and `PinnedTriality`;
no abstract geometric witness or Borel preservation premise is assumed.
Source: GLS3, 1.15.2--4 and 2.1--2.3
(`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`).
-/

public section

open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
noncomputable section
namespace Triality.SimplyConnected.Pinning.ChevalleySource.Endomorphisms
open OppositeBorels
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Every ordinary Frobenius iterate is the corresponding power on the native torus. -/
theorem frobenius_torus_formula_iterate (n : ℕ)
    (t : Variety.Point (CorootTorus.closedSubgroup k).carrierVariety) :
    (regularFrobeniusLift k n).onPoints ((CorootTorus.closedSubgroup k).includePoint t) =
      (CorootTorus.closedSubgroup k).includePoint (t ^ (2 ^ n)) := by
  change (regularFrobeniusLift k n).onPoints
    ((CorootTorus.closedSubgroup k).inclusion.onPoints t) =
      (CorootTorus.closedSubgroup k).inclusion.onPoints (t ^ (2 ^ n))
  rw [map_pow]
  obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
  change (regularFrobeniusLift k n).onPoints
    ((CorootTorus.closedSubgroup k).inclusion.onPoints
      ((CorootTorus.coordinateIso k).hom.onPoints x)) =
    ((CorootTorus.closedSubgroup k).inclusion.onPoints
      ((CorootTorus.coordinateIso k).hom.onPoints x)) ^ (2 ^ n)
  rw [CorootTorus.coordinateIso_inclusion, regularFrobeniusLift_onPoints]
  change frobeniusPointAut k n (CorootTorus.parameter k (dPointEquiv 4 x)) =
    CorootTorus.parameter k (dPointEquiv 4 x) ^ (2 ^ n)
  rw [GraphField.frobenius_parameter]
  exact map_pow (CorootTorus.pointHom k) (dPointEquiv 4 x) (2 ^ n)

/-- Ordinary Frobenius squares every point of the actual coroot torus. -/
theorem frobenius_torus_formula
    (t : Variety.Point (CorootTorus.closedSubgroup k).carrierVariety) :
    (regularFrobeniusLift k 1).onPoints ((CorootTorus.closedSubgroup k).includePoint t) =
      (CorootTorus.closedSubgroup k).includePoint (t ^ 2) := by
  simpa only [pow_one] using frobenius_torus_formula_iterate k 1 t

private theorem diagram_positive (r : RootIndex)
    (hr : (typeDRootPairing_base 2).IsPos r) :
    (typeDRootPairing_base 2).IsPos (typeD4DiagramEquiv.indexEquiv r) := by
  have hs (r : RootIndex) (hr : r ∈ (typeDRootPairing_base 2).support) :
      (typeDRootPairing_base 2).IsPos (typeD4DiagramEquiv.indexEquiv r) := by
    apply (typeDRootPairing_base 2).isPos_of_mem_support
    have h := typeD4DiagramEquiv_simple ⟨r, hr⟩
    rw [h]
    exact (typeD4DiagramBasePermutation ⟨r, hr⟩).property
  apply hr.induction_on_add hs
  intro i j l hl hi hj
  apply hi.add (hs j hj)
  rw [← RootPairing.Hom.root_weightMap_apply, hl, map_add,
    RootPairing.Hom.root_weightMap_apply, RootPairing.Hom.root_weightMap_apply]

private theorem positive_rootPoint_mem (r : RootIndex)
    (hr : (typeDRootPairing_base 2).IsPos r) (a : k) :
    rootPoint k r a ∈ (bigCell k).data.B := by
  apply rootGenerated_le_torusRootGenerated k (positiveRoots k)
  apply rootSubgroup_le_RootSubgroupGenerated (pinnedRootData k)
    (α := pinnedRootIndex k r) hr
  exact (mem_rootClosedSubgroup_iff k r _).mpr ⟨a, rfl⟩

private theorem positive_borel_stable_of_rootPoints (f : Points k →* Points k)
    (ht : ∀ x, x ∈ CorootTorus.closedSubgroup k → f x ∈ CorootTorus.closedSubgroup k)
    (hr : ∀ r : RootIndex, (typeDRootPairing_base 2).IsPos r →
      ∀ a : k, f (rootPoint k r a) ∈ (bigCell k).data.B)
    (x : Points k) (hx : x ∈ (bigCell k).data.B) : f x ∈ (bigCell k).data.B := by
  have hle : ((bigCell k).data.B).toSubgroup ≤
      ((bigCell k).data.B).toSubgroup.comap f := by
    change (CorootTorus.closedSubgroup k).toSubgroup ⊔
      RootSubgroupGenerated (pinnedRootData k) (positiveRoots k) ≤ _
    apply sup_le
    · intro t ht'
      exact torus_le_torusRootGenerated k (positiveRoots k) (ht t ht')
    · apply RootSubgroupGenerated_le_of_rootSubgroup_le
      intro r hr' x hx'
      obtain ⟨a, rfl⟩ := (mem_rootClosedSubgroup_iff k r.down x).mp hx'
      exact hr r.down hr' a
  exact hle hx

/-- Ordinary Frobenius preserves the native closed torus. -/
theorem frobenius_torus_stable (n : ℕ) (x : Points k)
    (hx : x ∈ CorootTorus.closedSubgroup k) :
    (regularFrobeniusLift k n).onPoints x ∈ CorootTorus.closedSubgroup k := by
  obtain ⟨t, rfl⟩ := (CorootTorus.mem_iff_parameter k x).mp hx
  rw [regularFrobeniusLift_onPoints, GraphField.frobenius_parameter]
  exact CorootTorus.parameter_mem k _

/-- Every ordinary Frobenius iterate preserves the literal positive Borel. -/
theorem frobenius_borel_stable_iterate (n : ℕ) (b : Points k)
    (hb : b ∈ (bigCell k).data.B) :
    (regularFrobeniusLift k n).onPoints b ∈ (bigCell k).data.B := by
  apply positive_borel_stable_of_rootPoints k (regularFrobeniusLift k n).onPoints
    (frobenius_torus_stable k n) ?_ b hb
  intro r hr a
  rw [regularFrobeniusLift_onPoints, GraphField.frobenius_rootPoint]
  exact positive_rootPoint_mem k r hr _

/-- The Borel clause for the ordinary Frobenius used by the tensor geometry. -/
theorem frobenius_borel_stable (b : Points k) (hb : b ∈ (bigCell k).data.B) :
    (regularFrobeniusLift k 1).onPoints b ∈ (bigCell k).data.B :=
  frobenius_borel_stable_iterate k 1 b hb

/-- The actual pinned triality sends each simple coroot by the forward arm cycle. -/
theorem diagram_coroot_formula (i : Fin 4) (t : Variety.Point (KMult k)) :
    (Diagram.pinnedIso k).hom.onPoints
      ((CorootTorus.closedSubgroup k).includePoint
        (((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints t)) =
    (CorootTorus.closedSubgroup k).includePoint
      (((pinnedRootData k).rootCocharacter
        (pinnedRootIndex k (simpleRoot (typeD4DiagramPermutation i)))).onPoints t) := by
  exact congrArg (fun f => f.onPoints t) (Diagram.pinnedIso_simpleCoroot k i)

/-- The native pinned triality preserves the actual closed torus. -/
theorem diagram_torus_stable (t : Points k) (ht : t ∈ CorootTorus.closedSubgroup k) :
    (Diagram.pinnedIso k).hom.onPoints t ∈ CorootTorus.closedSubgroup k :=
  (Diagram.pinnedAut_torus_mem_iff k t).mpr ht

/-- The inverse native triality preserves that same closed torus. -/
theorem diagram_torus_inverse_stable (t : Points k) (ht : t ∈ CorootTorus.closedSubgroup k) :
    (Diagram.pinnedIso k).inv.onPoints t ∈ CorootTorus.closedSubgroup k := by
  rw [Diagram.pinnedIso_inv]
  exact diagram_torus_stable k _ (diagram_torus_stable k t ht)

/-- The pinned diagram map preserves the actual positive Borel. -/
theorem diagram_borel_stable (b : Points k) (hb : b ∈ (bigCell k).data.B) :
    (Diagram.pinnedIso k).hom.onPoints b ∈ (bigCell k).data.B := by
  apply positive_borel_stable_of_rootPoints k (Diagram.pinnedIso k).hom.onPoints
    (diagram_torus_stable k) ?_ b hb
  intro r hr a
  change Diagram.pinnedAut k (rootPoint k r a) ∈ _
  rw [GraphField.diagram_rootPoint]
  exact positive_rootPoint_mem k _ (diagram_positive r hr) a

/-- Its inverse preserves the same positive Borel. -/
theorem diagram_borel_inverse_stable (b : Points k) (hb : b ∈ (bigCell k).data.B) :
    (Diagram.pinnedIso k).inv.onPoints b ∈ (bigCell k).data.B := by
  rw [Diagram.pinnedIso_inv]
  exact diagram_borel_stable k _ (diagram_borel_stable k b hb)

end Triality.SimplyConnected.Pinning.ChevalleySource.Endomorphisms
