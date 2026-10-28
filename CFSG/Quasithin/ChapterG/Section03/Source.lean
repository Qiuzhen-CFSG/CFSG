module

public import Theory.Representation.BinaryTransvectionGroups.Basic
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.SupIndep

/-!
# Source interface for G.3.1

The source uses points of a binary vector space acted on by a finite group. Here each point is
represented by its unique nonzero vector; `mem_centerLine_iff` verifies this
convention. `Hypotheses` records the orbit and the rank of the actual image
of `A(X)` in `G/O₂(G)`. The two-core is intrinsic to `G`.

The blocks are exactly the orbits of the generated subgroup on the given
orbit, indexed by their underlying sets to avoid any choice of representatives.
The output predicates separate the recognition argument, the internal
space/group decompositions, and the local rank calculation. They are contracts,
not assumed source theorems. The section owner must construct all of them.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma G.3.1, printed pp. 337--338 (PDF pp. 348--349).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03

open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The image `A(X)O₂(G)/O₂(G)` in the intrinsic quotient of `G`. -/
def rootQuotientImage (G : Subgroup (GL V)) (x : V) : Subgroup (G ⧸ pCore 2 G) :=
  ((rootGroup G x).subgroupOf G).map (QuotientGroup.mk' (pCore 2 G))

/-- The genuine inputs of G.3.1. No recognition or decomposition is included. -/
structure Hypotheses (G : Subgroup (GL V)) [Finite G] (Δ : Set V) : Prop where
  nonzero : ∀ x ∈ Δ, x ≠ 0
  orbit : ∃ x : V, Δ = MulAction.orbit G x
  rank_gt_one : ∀ x ∈ Δ, 1 < Group.rank (rootQuotientImage G x)

/-- The canonical `G₀`-orbits contained in `Δ₀`. -/
def OrbitBlock (G : Subgroup (GL V)) (Δ : Set V) :=
  {Γ : Set V // ∃ x ∈ Δ, Γ = MulAction.orbit (generated G Δ) x}

def blockSpace (G : Subgroup (GL V)) (Δ : Set V) (i : OrbitBlock G Δ) :
    Submodule (ZMod 2) V := Submodule.span (ZMod 2) i.val

def blockGroup (G : Subgroup (GL V)) (Δ : Set V) (i : OrbitBlock G Δ) :
    Subgroup (GL V) := generated G i.val

/-- The hard recognition conclusion, before the internal decomposition is assembled. -/
structure FullAction (G : Subgroup (GL V)) (Δ : Set V) : Prop where
  surjective : ∀ i : OrbitBlock G Δ, Function.Surjective (spanAction G i.val)
  dimension_ge_two : ∀ i : OrbitBlock G Δ, 2 ≤ Module.finrank (ZMod 2) (blockSpace G Δ i)

/-- The identity outside one prescribed factor. -/
noncomputable def singleGroupElement {G : Subgroup (GL V)} {Δ : Set V}
    (i : OrbitBlock G Δ) (g : blockGroup G Δ i) : ∀ j, blockGroup G Δ j := by
  classical
  exact Pi.mulSingle i g

/-- The zero vector outside one prescribed summand. -/
noncomputable def singleSpaceElement {G : Subgroup (GL V)} {Δ : Set V}
    (i : OrbitBlock G Δ) (v : blockSpace G Δ i) : ∀ j, blockSpace G Δ j := by
  classical
  exact Pi.single i v

/-- The internal decompositions, including isomorphisms preserving the inclusions. -/
structure Decomposition (G : Subgroup (GL V)) (Δ : Set V) : Prop where
  space_span : (⨆ i : OrbitBlock G Δ, blockSpace G Δ i) = Submodule.span (ZMod 2) Δ
  space_independent : iSupIndep (blockSpace G Δ)
  group_join : (⨆ i : OrbitBlock G Δ, blockGroup G Δ i) = generated G Δ
  group_independent : iSupIndep (blockGroup G Δ)
  cross_fix : ∀ i j : OrbitBlock G Δ, i ≠ j →
    ∀ g ∈ blockGroup G Δ i, ∀ v ∈ blockSpace G Δ j, g v = v
  groups_commute : ∀ i j : OrbitBlock G Δ, i ≠ j →
    ∀ g ∈ blockGroup G Δ i, ∀ h ∈ blockGroup G Δ j, Commute g h
  groups_conjugate : ∀ i j : OrbitBlock G Δ, ∃ g ∈ G,
    (blockGroup G Δ i).map (MulAut.conj g).toMonoidHom = blockGroup G Δ j
  spaces_conjugate : ∀ i j : OrbitBlock G Δ, ∃ g ∈ G,
    (blockSpace G Δ i).map g.toLinearMap = blockSpace G Δ j
  group_equiv : ∃ e : (∀ i : OrbitBlock G Δ, blockGroup G Δ i) ≃* generated G Δ,
    ∀ i g, (e (singleGroupElement i g) : GL V) = (g : GL V)
  space_equiv : ∃ e : (∀ i : OrbitBlock G Δ, blockSpace G Δ i) ≃ₗ[ZMod 2]
      Submodule.span (ZMod 2) Δ,
    ∀ i v, (e (singleSpaceElement i v) : V) = (v : V)

/-- The remaining local assertions in G.3.1(2), and the bound in G.3.1(3). -/
structure LocalStructure (G : Subgroup (GL V)) [Finite G] (Δ : Set V) : Prop where
  dimension_ge_three : ∀ i : OrbitBlock G Δ, 3 ≤ Module.finrank (ZMod 2) (blockSpace G Δ i)
  all_points : ∀ i : OrbitBlock G Δ, i.val = {v | v ∈ blockSpace G Δ i ∧ v ≠ 0}
  kernel_elementary : ∀ i : OrbitBlock G Δ,
    IsElementaryAbelian 2 (fixingKernel (blockGroup G Δ i) (blockSpace G Δ i))
  rank_formula : ∀ i : OrbitBlock G Δ, ∀ x ∈ i.val,
    Group.rank (rootGroup G x) = Module.finrank (ZMod 2) (blockSpace G Δ i) - 1 +
      Group.rank (fixingKernel (rootGroup G x) (blockSpace G Δ i))

/-- The quotient-rank input concerns an actual elementary abelian group. -/
theorem rootQuotientImage_elementaryAbelian (G : Subgroup (GL V)) (x : V) :
    IsElementaryAbelian 2 (rootQuotientImage G x) := by
  let := rootGroup_elementaryAbelian G x
  let := IsElementaryAbelian.subgroupOf (p := 2) (rootGroup_le G x)
  exact IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 G))

theorem Hypotheses.stable {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) : ∀ g ∈ G, ∀ x ∈ Δ, g x ∈ Δ := by
  obtain ⟨a, ha⟩ := h.orbit
  rw [ha]
  intro g hg x hx
  obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  exact MulAction.mem_orbit_iff.mpr ⟨(⟨g, hg⟩ : G) * k, rfl⟩

theorem block_subset {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (i : OrbitBlock G Δ) : i.val ⊆ Δ := by
  obtain ⟨x, hx, hi⟩ := i.property
  intro v hv
  rw [hi] at hv
  obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hv
  exact h.stable k.val (generated_le G Δ k.property) x hx

theorem blockGroup_le_generated {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (i : OrbitBlock G Δ) : blockGroup G Δ i ≤ generated G Δ :=
  iSup_le fun _x => iSup_le fun hx => rootGroup_le_generated G (block_subset h i hx)

/-- The elementary-kernel clause of G.3.1(2), without a recognition assumption. -/
theorem block_kernel_elementaryAbelian (G : Subgroup (GL V)) (Δ : Set V)
    (i : OrbitBlock G Δ) :
    IsElementaryAbelian 2 (fixingKernel (blockGroup G Δ i) (blockSpace G Δ i)) :=
  generated_fixingKernel_elementaryAbelian G i.val

end CFSG.Quasithin.ChapterG.Section03
