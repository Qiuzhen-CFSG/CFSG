module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Faithful actions on connected components

The setwise stabilizer of a connected component acts on its induced graph.
An element taking one vertex of the component to another preserves the whole
component, since graph automorphisms preserve reachability. Thus the component
action retains the original point stabilizers and transitivity properties.
Factoring out its pointwise kernel gives the literal faithful quotient action.

Source: the component and kernel passage in Goldschmidt, *Automorphisms of
trivalent graphs* (1980), §5.2. No finiteness of the ambient group is required.
-/

@[expose] public section
open SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped Pointwise

namespace Theory.GroupAction.CubicTree.ComponentAction

variable {X L : Type*} [Group L] [MulAction L X] {Δ : SimpleGraph X}

/-- The literal setwise stabilizer of a connected component. -/
abbrev stabilizer (L : Type*) [Group L] [MulAction L X]
    (C : Δ.ConnectedComponent) : Subgroup L :=
  MulAction.stabilizer L (C : Set X)

variable (C : Δ.ConnectedComponent)

/-- The existing set-stabilizer action, exposed at the component subtype. -/
instance componentMulAction : MulAction (stabilizer L C) C :=
  inferInstanceAs (MulAction (MulAction.stabilizer L (C : Set X)) (C : Set X))

@[simp] theorem smul_val (a : stabilizer L C) (x : C) :
    ((a • x : C) : X) = (a : L) • (x : X) := rfl

private theorem smul_mem_of_smul_mem (hact : GraphAction Δ L)
    {a : L} {x : X} (hx : x ∈ C.supp) (hax : a • x ∈ C.supp)
    {z : X} (hz : z ∈ C.supp) : a • z ∈ C.supp := by
  have hr := (C.reachable_of_mem_supp hx hz).map (hact.hom a)
  exact (C.mem_supp_iff _).mpr
    ((ConnectedComponent.sound hr).symm.trans ((C.mem_supp_iff _).mp hax))

/-- Sending one point into its component forces preservation of that component. -/
theorem mem_stabilizer_of_smul_mem (hact : GraphAction Δ L)
    {a : L} {x : X} (hx : x ∈ C.supp) (hax : a • x ∈ C.supp) :
    a ∈ stabilizer L C := by
  apply MulAction.mem_stabilizer_iff.mpr
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact smul_mem_of_smul_mem C hact hx hax hz
  · intro z hz
    refine ⟨a⁻¹ • z, ?_, smul_inv_smul a z⟩
    apply smul_mem_of_smul_mem C hact hax _ hz
    simpa only [inv_smul_smul] using hx

/-- The component inherits adjacency preservation under the existing set action. -/
theorem graphAction (hact : GraphAction Δ L) :
    GraphAction C.toSimpleGraph (stabilizer L C) :=
  ⟨fun a _ _ h => hact.map_adj (a : L) h⟩

/-- The entire ambient vertex stabilizer already preserves the component. -/
theorem stabilizer_le (hact : GraphAction Δ L) (x : C) :
    MulAction.stabilizer L (x : X) ≤ stabilizer L C := by
  intro a ha
  apply mem_stabilizer_of_smul_mem C hact x.property
  rw [MulAction.mem_stabilizer_iff.mp ha]
  exact x.property

/-- Mapping the component point stabilizer into the original group gives equality. -/
theorem map_stabilizer_eq (hact : GraphAction Δ L) (x : C) :
    (MulAction.stabilizer (stabilizer L C) x).map (stabilizer L C).subtype =
      MulAction.stabilizer L (x : X) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hb)
  · intro ha
    refine ⟨⟨a, stabilizer_le C hact x ha⟩, ?_, rfl⟩
    exact Subtype.ext (MulAction.mem_stabilizer_iff.mp ha)

/-- Finite ambient point stabilizers give finite component point stabilizers. -/
theorem finite_stabilizer (x : C) [Finite (MulAction.stabilizer L (x : X))] :
    Finite (MulAction.stabilizer (stabilizer L C) x) := by
  let f : MulAction.stabilizer (stabilizer L C) x →
      MulAction.stabilizer L (x : X) := fun a =>
    ⟨a.val.val, congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp a.property)⟩
  exact Finite.of_injective f (fun _ _ h => Subtype.ext (Subtype.ext
    (congrArg (fun a : MulAction.stabilizer L (x : X) => (a : L)) h)))

/-- Vertex transitivity restricts to every connected component. -/
theorem transitive (hact : GraphAction Δ L)
    (htrans : ∀ x y : X, ∃ a : L, a • x = y) :
    ∀ x y : C, ∃ a : stabilizer L C, a • x = y := by
  intro x y
  obtain ⟨a, ha⟩ := htrans x y
  refine ⟨⟨a, mem_stabilizer_of_smul_mem C hact x.property ?_⟩, Subtype.ext ha⟩
  rw [ha]
  exact y.property

/-- Local transitivity restricts with the original point-fixing elements. -/
theorem locally_transitive (hact : GraphAction Δ L)
    (hlocal : ∀ x y z : X, Δ.Adj x y → Δ.Adj x z →
      ∃ a : L, a • x = x ∧ a • y = z) :
    ∀ x y z : C, C.toSimpleGraph.Adj x y → C.toSimpleGraph.Adj x z →
      ∃ a : stabilizer L C, a • x = x ∧ a • y = z := by
  intro x y z hxy hxz
  obtain ⟨a, hax, hay⟩ := hlocal x y z hxy hxz
  refine ⟨⟨a, stabilizer_le C hact x hax⟩, Subtype.ext hax, Subtype.ext hay⟩

/-- The given pointwise kernel is the kernel of the component permutation action. -/
theorem kernel_eq (Q : Subgroup L)
    (hkernel : Q = fixingSubgroup L C.supp) :
    (MulAction.toPermHom (stabilizer L C) C).ker = Q.subgroupOf (stabilizer L C) := by
  ext a
  rw [hkernel]
  change MulAction.toPermHom (stabilizer L C) C a = 1 ↔
    (a : L) ∈ fixingSubgroup L C.supp
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro ha x hx
    exact congrArg Subtype.val (Equiv.congr_fun ha ⟨x, hx⟩)
  · intro ha
    apply Equiv.ext
    intro x
    exact Subtype.ext (ha x x.property)

/-- Normality needed for the literal quotient follows from the kernel identity. -/
theorem kernel_normal (Q : Subgroup L)
    (hkernel : Q = fixingSubgroup L C.supp) :
    (Q.subgroupOf (stabilizer L C)).Normal := by
  rw [← kernel_eq C Q hkernel]
  infer_instance

section Quotient
variable (Q : Subgroup L) [(Q.subgroupOf (stabilizer L C)).Normal]
  (hkernel : Q = fixingSubgroup L C.supp)

/-- The faithful permutation homomorphism from the specified kernel quotient. -/
def quotientHom : (stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C) →* Equiv.Perm C :=
  QuotientGroup.lift _ (MulAction.toPermHom (stabilizer L C) C)
    (kernel_eq C Q hkernel).ge

/-- The component action descends to the literal quotient by Q. -/
abbrev quotientAction :
    MulAction ((stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C)) C :=
  MulAction.compHom C (quotientHom C Q hkernel)

theorem quotient_faithful :
    letI := quotientAction C Q hkernel
    FaithfulSMul ((stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C)) C := by
  let := quotientAction C Q hkernel
  refine ⟨fun h => ?_⟩
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr
    (kernel_eq C Q hkernel).symm (Equiv.ext h)

@[simp] theorem quotient_mk_smul (a : stabilizer L C) (x : C) :
    letI := quotientAction C Q hkernel
    QuotientGroup.mk' (Q.subgroupOf (stabilizer L C)) a • x = a • x := rfl

/-- The quotient preserves the induced component graph. -/
theorem quotient_graphAction (hact : GraphAction Δ L) :
    letI := quotientAction C Q hkernel
    GraphAction C.toSimpleGraph
      ((stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C)) := by
  let := quotientAction C Q hkernel
  constructor
  intro a x y hxy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf (stabilizer L C)) a
  exact (graphAction C hact).map_adj a hxy

/-- The quotient point stabilizer is the image of the original component stabilizer. -/
theorem quotient_map_stabilizer (x : C) :
    letI := quotientAction C Q hkernel
    (MulAction.stabilizer (stabilizer L C) x).map
      (QuotientGroup.mk' (Q.subgroupOf (stabilizer L C))) =
    MulAction.stabilizer ((stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C)) x := by
  let := quotientAction C Q hkernel
  let q := QuotientGroup.mk' (Q.subgroupOf (stabilizer L C))
  let S := MulAction.stabilizer ((stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C)) x
  have he : S.comap q = MulAction.stabilizer (stabilizer L C) x := by
    ext a
    rfl
  rw [← he]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) S

/-- Finite point stabilizers survive the passage to the faithful quotient. -/
theorem quotient_finite_stabilizer (x : C) [Finite (MulAction.stabilizer L (x : X))] :
    letI := quotientAction C Q hkernel
    Finite (MulAction.stabilizer
      ((stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C)) x) := by
  let := quotientAction C Q hkernel
  have := finite_stabilizer (L := L) C x
  rw [← quotient_map_stabilizer C Q hkernel x]
  change Finite ((QuotientGroup.mk' (Q.subgroupOf (stabilizer L C))) ''
    (MulAction.stabilizer (stabilizer L C) x : Set (stabilizer L C)))
  infer_instance

/-- Vertex transitivity is retained by the faithful quotient. -/
theorem quotient_transitive (hact : GraphAction Δ L)
    (htrans : ∀ x y : X, ∃ a : L, a • x = y) :
    letI := quotientAction C Q hkernel
    ∀ x y : C, ∃ a : (stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C), a • x = y := by
  let := quotientAction C Q hkernel
  intro x y
  obtain ⟨a, ha⟩ := transitive C hact htrans x y
  exact ⟨QuotientGroup.mk' _ a, ha⟩

/-- Local transitivity is retained with the literal projected stabilizer elements. -/
theorem quotient_locally_transitive (hact : GraphAction Δ L)
    (hlocal : ∀ x y z : X, Δ.Adj x y → Δ.Adj x z →
      ∃ a : L, a • x = x ∧ a • y = z) :
    letI := quotientAction C Q hkernel
    ∀ x y z : C, C.toSimpleGraph.Adj x y → C.toSimpleGraph.Adj x z →
      ∃ a : (stabilizer L C) ⧸ Q.subgroupOf (stabilizer L C),
        a • x = x ∧ a • y = z := by
  let := quotientAction C Q hkernel
  intro x y z hxy hxz
  obtain ⟨a, hax, hay⟩ := locally_transitive C hact hlocal x y z hxy hxz
  exact ⟨QuotientGroup.mk' _ a, hax, hay⟩

end Quotient
end Theory.GroupAction.CubicTree.ComponentAction
