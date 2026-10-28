module
public import Theory.Representation.SL3FourNaturalDual.Actors

/-!
# Transporting the SL₃(4) critical-line obstructions

The markings use homomorphisms from the actual determinant-one matrix group
and equivariant binary linear equivalences. They retain both root parameters,
the independent root, and the single interchange operator. Transport maps the
literal commutator line and preserves quotient dimension.

`CriticalShapes` states the matrix alternatives still to be obtained from the
quadratic actor classification. `critical_obstruction` proves the resulting
linear contradiction for both source coranks. It does not assume that an
arbitrary quadratic actor has these markings.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (combined manuscript
of 1 March 2004), using F.9.13(6) and F.9.16(2).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual
variable {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]

/-- An actual equivariant identification of the restricted SL₃(4) action. -/
structure LinearMarking (ρ : Representation (ZMod 2) J U) where
  actor : SL →* J
  coordinates : U ≃ₗ[ZMod 2] V
  equivariant : ∀ g u, coordinates (ρ (actor g) u) = representation g (coordinates u)

lemma corank_map (e : U ≃ₗ[ZMod 2] V) (D : Submodule (ZMod 2) U) :
    Module.finrank (ZMod 2) (V ⧸ D.map e.toLinearMap) =
      Module.finrank (ZMod 2) (U ⧸ D) :=
  (Submodule.Quotient.equiv D (D.map e.toLinearMap) e rfl).finrank_eq.symm

lemma line_map (e : U ≃ₗ[ZMod 2] V) (s u : U)
    (h : u ∈ Submodule.span (ZMod 2) {s}) :
    e u ∈ Submodule.span (ZMod 2) {e s} := by
  rcases (mem_binary_line s u).mp h with rfl | rfl
  · simp
  · exact Submodule.subset_span (Set.mem_singleton _)

lemma LinearMarking.root_obstruction (ρ : Representation (ZMod 2) J U)
    (m : LinearMarking ρ) (A : Subgroup J) (D : Submodule (ZMod 2) U) (s : U)
    (hroot : ∀ a : F, m.actor (root a) ∈ A)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ 2)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ Submodule.span (ZMod 2) {s}) : False := by
  apply no_root_critical_line_of_corank_two (D.map m.coordinates.toLinearMap) (m.coordinates s)
    (by rw [corank_map]; exact hD)
  intro a d hd
  obtain ⟨u, hu, rfl⟩ := hd
  have h := line_map m.coordinates s _ (hcomm (m.actor (root a)) (hroot a) u hu)
  change representation (root a) (m.coordinates u) - m.coordinates u ∈ _
  rw [← m.equivariant, ← map_sub]
  exact h

lemma LinearMarking.plane_obstruction (ρ : Representation (ZMod 2) J U)
    (m : LinearMarking ρ) (A : Subgroup J) (D : Submodule (ZMod 2) U) (s : U)
    (hroot : ∀ a : F, m.actor (root a) ∈ A)
    (hsecond : m.actor (secondRoot 1) ∈ A)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ 4)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ Submodule.span (ZMod 2) {s}) : False := by
  apply no_root_plane_critical_line (D.map m.coordinates.toLinearMap) (m.coordinates s)
    (by rw [corank_map]; exact hD)
  · intro a d hd
    obtain ⟨u, hu, rfl⟩ := hd
    change representation (root a) (m.coordinates u) - m.coordinates u ∈ _
    rw [← m.equivariant, ← map_sub]
    exact line_map m.coordinates s _ (hcomm _ (hroot a) u hu)
  · intro d hd
    obtain ⟨u, hu, rfl⟩ := hd
    change representation (secondRoot 1) (m.coordinates u) - m.coordinates u ∈ _
    rw [← m.equivariant, ← map_sub]
    exact line_map m.coordinates s _ (hcomm _ hsecond u hu)

/-- An actual linear conjugacy of one actor to the interchange involution.
The name describes the displayed linear operator; an automorphism normal-form
theorem must prove that a specified group actor has this marking. -/
structure SwapMarking (ρ : Representation (ZMod 2) J U) (A : Subgroup J) where
  actor : J
  mem : actor ∈ A
  coordinates : U ≃ₗ[ZMod 2] V
  equivariant : ∀ u, coordinates (ρ actor u) = graphSwap (coordinates u)

lemma SwapMarking.obstruction (ρ : Representation (ZMod 2) J U) (A : Subgroup J)
    (m : SwapMarking ρ A) (D : Submodule (ZMod 2) U) (s : U)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ 4)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ Submodule.span (ZMod 2) {s}) : False := by
  apply no_graph_critical_line (D.map m.coordinates.toLinearMap) (m.coordinates s)
    (by rw [corank_map]; exact hD)
  intro d hd
  obtain ⟨u, hu, rfl⟩ := hd
  change graphSwap (m.coordinates u) - m.coordinates u ∈ _
  rw [← m.equivariant, ← map_sub]
  exact line_map m.coordinates s _ (hcomm _ m.mem u hu)

/-- The complete matrix markings needed by the critical-subspace argument.
The classification producing this disjunction is a separate obligation.
Every alternative refers to actual matrices and equivariant linear maps. -/
def CriticalShapes (ρ : Representation (ZMod 2) J U) (A : Subgroup J) : Prop :=
  (BinaryOffender.rank A = 2 ∧ BinaryOffender.fixedCodim ρ A = 4 ∧
    ∃ m : LinearMarking ρ, ∀ a : F, m.actor (root a) ∈ A) ∨
  (3 ≤ BinaryOffender.rank A ∧ BinaryOffender.rank A ≤ 4 ∧
    BinaryOffender.fixedCodim ρ A = 6 ∧
    ((∃ m : LinearMarking ρ,
      (∀ a : F, m.actor (root a) ∈ A) ∧ m.actor (secondRoot 1) ∈ A) ∨
      Nonempty (SwapMarking ρ A)))

/-- Both source corank cases are impossible once their actual actor markings
are constructed. The single binary commutator line is indispensable. -/
lemma critical_obstruction (ρ : Representation (ZMod 2) J U) (A : Subgroup J)
    (hshape : CriticalShapes ρ A) (D : Submodule (ZMod 2) U) (s : U)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ BinaryOffender.rank A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ Submodule.span (ZMod 2) {s}) : False := by
  rcases hshape with ⟨hr, _, m, hm⟩ | ⟨_, hr, _, hm | hm⟩
  · exact m.root_obstruction ρ A D s hm (by simpa only [hr] using hD) hcomm
  · obtain ⟨m, hm, hs⟩ := hm
    exact m.plane_obstruction ρ A D s hm hs (hD.trans hr) hcomm
  · obtain ⟨m⟩ := hm
    exact m.obstruction ρ A D s (hD.trans hr) hcomm

end Representation.SL3FourNaturalDual
