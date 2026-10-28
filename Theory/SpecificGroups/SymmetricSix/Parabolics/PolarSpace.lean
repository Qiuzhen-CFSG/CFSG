module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
/-!
# The duad–syntheme quadrangle as a binary polar space

The table in `Parabolics` identifies the fifteen duads with all nonzero vectors
of the four-dimensional binary module. Its disjointness relation is exactly
orthogonality for the standard symplectic matrix `Matrix.J`. The three vectors
of a syntheme, together with zero, form an isotropic plane. Conversely, two
basis vectors of any isotropic plane determine a syntheme, and dimension two
then gives equality. This proves an incidence isomorphism with the polar space,
using actual submodules rather than an assumed recognition property.

The finite table identities are checked by kernel reduction. The module also
records the unique-line and point-line axioms of the generalized quadrangle.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.4 and
I.5.9, printed pp. 420–422.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The standard alternating form, on the same coordinates as `Matrix.symplecticGroup`. -/
def polarForm : LinearMap.BilinForm (ZMod 2) NaturalModule :=
  (Matrix.J (Fin 2) (ZMod 2)).toBilin'
theorem polarForm_alt : polarForm.IsAlt := by
  change ∀ v : NaturalModule, polarForm v v = 0
  decide
theorem polarForm_nondegenerate : polarForm.Nondegenerate := by
  constructor
  · change ∀ v : NaturalModule, (∀ w, polarForm v w = 0) → v = 0
    decide
  · change ∀ v : NaturalModule, (∀ w, polarForm w v = 0) → v = 0
    decide
theorem polarVector_injective : Function.Injective polarVector := by decide
theorem polarVector_bijective : Function.Bijective polarVector :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨polarVector_injective, duad_card.trans binary_point_card.symm⟩
/-- Duads are the nonzero vectors (equivalently, binary projective points). -/
noncomputable def duadPolarEquiv : Duad ≃ BinaryPoint :=
  Equiv.ofBijective polarVector polarVector_bijective

theorem polarVector_orthogonal (d e : Duad) :
    polarForm (polarVector d).val (polarVector e).val = 0 ↔
      d = e ∨ duadCollinear d e := by decide +revert

/-- Zero together with the three vectors labeled by a syntheme. -/
def polarLineSet (s : Syntheme) : Finset NaturalModule :=
  insert 0 ((synthemeDuads s).image (fun d => (polarVector d).val))
private theorem polarLineSet_add (s : Syntheme) (v w : NaturalModule)
    (hv : v ∈ polarLineSet s) (hw : w ∈ polarLineSet s) : v + w ∈ polarLineSet s := by
  decide +revert
private theorem polarLineSet_smul (s : Syntheme) (c : ZMod 2) (v : NaturalModule)
    (hv : v ∈ polarLineSet s) : c • v ∈ polarLineSet s := by
  decide +revert

/-- The actual vector subspace represented by a syntheme. -/
def polarLine (s : Syntheme) : Submodule (ZMod 2) NaturalModule where
  carrier := ↑(polarLineSet s)
  zero_mem' := Finset.mem_insert_self _ _
  add_mem' := by exact polarLineSet_add s _ _
  smul_mem' := by exact polarLineSet_smul s

instance (s : Syntheme) : Fintype (polarLine s) :=
  Fintype.subtype (polarLineSet s) (by intro v; rfl)

theorem polarLine_card (s : Syntheme) : Nat.card (polarLine s) = 4 := by
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_of_subtype (polarLineSet s) (by intro v; rfl)]
  decide +revert

theorem polarLine_finrank (s : Syntheme) : Module.finrank (ZMod 2) (polarLine s) = 2 := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := polarLine s)
  rw [polarLine_card] at h
  norm_num at h ⊢
  exact h.symm

theorem polarLine_isotropic (s : Syntheme) (v w : NaturalModule)
    (hv : v ∈ polarLine s) (hw : w ∈ polarLine s) : polarForm v w = 0 := by
  change v ∈ polarLineSet s at hv
  change w ∈ polarLineSet s at hw
  decide +revert

theorem incident_iff_mem_polarLine (d : Duad) (s : Syntheme) :
    incident d s ↔ (polarVector d).val ∈ polarLine s := by
  change incident d s ↔ (polarVector d).val ∈ polarLineSet s
  decide +revert

theorem duad_collinear_iff_common_syntheme (d e : Duad) :
    duadCollinear d e ↔ d ≠ e ∧ ∃ s, incident d s ∧ incident e s := by
  decide +revert

private theorem polarLineSet_of_pair (s : Syntheme) (d e : Duad)
    (hd : incident d s) (he : incident e s) (hne : d ≠ e) :
    polarLineSet s = {0, (polarVector d).val, (polarVector e).val,
      (polarVector d).val + (polarVector e).val} := by decide +revert

theorem polarLine_le_of_pair (s : Syntheme) (d e : Duad)
    (hd : incident d s) (he : incident e s) (hne : d ≠ e)
    (W : Submodule (ZMod 2) NaturalModule)
    (hWd : (polarVector d).val ∈ W) (hWe : (polarVector e).val ∈ W) :
    polarLine s ≤ W := by
  intro v hv
  change v ∈ polarLineSet s at hv
  rw [polarLineSet_of_pair s d e hd he hne] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact W.zero_mem
  · exact hWd
  · exact hWe
  · exact W.add_mem hWd hWe

/-- The isotropic two-dimensional subspaces of the natural binary module. -/
def BinaryLine := {W : Submodule (ZMod 2) NaturalModule //
  Module.finrank (ZMod 2) W = 2 ∧ ∀ v ∈ W, ∀ w ∈ W, polarForm v w = 0}

def synthemePolarLine (s : Syntheme) : BinaryLine :=
  ⟨polarLine s, polarLine_finrank s, fun v hv w hw => polarLine_isotropic s v w hv hw⟩

private theorem synthemeDuads_injective : Function.Injective synthemeDuads := by decide

theorem synthemePolarLine_injective : Function.Injective synthemePolarLine := by
  intro s t h
  apply synthemeDuads_injective
  apply Finset.ext
  intro d
  change incident d s ↔ incident d t
  rw [incident_iff_mem_polarLine, incident_iff_mem_polarLine]
  have hh : polarLine s = polarLine t := congrArg Subtype.val h
  rw [hh]

theorem synthemePolarLine_surjective : Function.Surjective synthemePolarLine := by
  intro ⟨W, hdim, hiso⟩
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hdim
  have hn (i : Fin 2) : (b i).val ≠ 0 := by
    intro hi
    exact b.ne_zero i (Subtype.ext hi)
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨(b 0).val, hn 0⟩
  obtain ⟨e, he⟩ := polarVector_bijective.2 ⟨(b 1).val, hn 1⟩
  have hdv := congrArg Subtype.val hd
  have hev := congrArg Subtype.val he
  have hne : d ≠ e := by
    intro h
    have h' : b 0 = b 1 := Subtype.ext
      (hdv.symm.trans ((congrArg (fun i => (polarVector i).val) h).trans hev))
    have : (0 : Fin 2) = 1 := b.injective h'
    exact (by decide : (0 : Fin 2) ≠ 1) this
  have hc : duadCollinear d e := by
    apply ((polarVector_orthogonal d e).mp ?_).resolve_left hne
    rw [hdv, hev]
    exact hiso _ (b 0).property _ (b 1).property
  obtain ⟨s, hs, ht⟩ := ((duad_collinear_iff_common_syntheme d e).mp hc).2
  refine ⟨s, Subtype.ext ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · exact polarLine_le_of_pair s d e hs ht hne W
      (hdv.symm ▸ (b 0).property) (hev.symm ▸ (b 1).property)
  · exact (polarLine_finrank s).trans hdim.symm

/-- Every isotropic plane occurs exactly once in the syntheme table. -/
noncomputable def synthemePolarEquiv : Syntheme ≃ BinaryLine :=
  Equiv.ofBijective synthemePolarLine
    ⟨synthemePolarLine_injective, synthemePolarLine_surjective⟩

theorem binaryLine_card : Nat.card BinaryLine = 15 := by
  rw [← Nat.card_congr synthemePolarEquiv, Nat.card_eq_fintype_card]
  exact syntheme_card


theorem naturalModule_finrank : Module.finrank (ZMod 2) NaturalModule = 4 := by
  simp [NaturalModule]

/-- Incidence is ordinary containment of a nonzero vector in an isotropic plane. -/
theorem polar_incidence_equivalence (d : Duad) (s : Syntheme) :
    incident d s ↔ (duadPolarEquiv d).val ∈ (synthemePolarEquiv s).val :=
  incident_iff_mem_polarLine d s

theorem duad_common_syntheme_unique {d e : Duad} (h : duadCollinear d e) :
    ∃! s, incident d s ∧ incident e s := by
  unfold ExistsUnique
  decide +revert

theorem syntheme_collinear_iff_common_duad (s t : Syntheme) :
    synthemeCollinear s t ↔ s ≠ t ∧ ∃ d, incident d s ∧ incident d t := by
  decide +revert

theorem syntheme_common_duad_unique {s t : Syntheme} (h : synthemeCollinear s t) :
    ∃! d, incident d s ∧ incident d t := by
  unfold ExistsUnique
  decide +revert

/-- The point-line axiom of a generalized quadrangle. -/
theorem quadrangle_unique_collinear (d : Duad) (s : Syntheme) (h : ¬incident d s) :
    ∃! e, incident e s ∧ duadCollinear d e := by
  unfold ExistsUnique
  decide +revert

/-- The dual point-line axiom. -/
theorem quadrangle_unique_collinear_dual (d : Duad) (s : Syntheme) (h : ¬incident d s) :
    ∃! t, incident d t ∧ synthemeCollinear s t := by
  unfold ExistsUnique
  decide +revert

end Theory.SpecificGroups.SymmetricSix
