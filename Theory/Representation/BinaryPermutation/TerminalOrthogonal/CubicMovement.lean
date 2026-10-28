module
public import Theory.Representation.BinaryPermutation.EightGeometry
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockResidual
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
/-!
# Cubic movement in the eight-letter point hyperplane

A nonidentity cubic in the literal A4 × A4 embedding moves a pair word
inside one four-point block to a pair sharing exactly one coordinate.
The displacement has weight two, hence is nonsingular for the half-weight
form. The initial pair lies in the perpendicular of the marked four-word.
The small certificate ranges over 144 actor pairs and 64 coordinate pairs;
it checks word arithmetic, not subgroups or quotient representatives.

A cubic fixing the marked point lies in this literal four-block residual:
fixation modulo constants preserves the coordinate equality relation, and
the prime-to-three residual gives its actual block coordinates. This also
constructs the marking after a simultaneous change of point coordinates.

Source: Aschbacher--Smith, the nonsingular vectors used in the proof of
12.6.33, printed p.838. The half-weight form and its original quotient map
are reused from the attributed ATLAS port through `EightGeometry`.
The literal conjugation application is in
`Chapter12/Section06/LocalAlternatives/NonTensor`.
-/

public section
namespace BinaryPermutation.TerminalOrthogonal.CubicMovement
open BinaryPermutation BinaryPermutation.TerminalOrthogonal.Eight
open BinaryPermutation.TerminalOrthogonal.FourBlockResidual
open scoped BigOperators

private def pair (i j : Fin 8) : core (Fin 8) :=
  ⟨Pi.single i 1 + Pi.single j 1, by simp [mem_core, Finset.sum_add_distrib]⟩
private def pointWord : core (Fin 8) := ⟨![1,1,1,1,0,0,0,0],by change (∑ i : Fin 8, (![1,1,1,1,0,0,0,0] : Fin 8 → ZMod 2) i) = 0; decide⟩
/-- The singular point represented by the first four coordinates. -/
noncomputable def point : natural (Fin 8) := coreToNatural (Fin 8) pointWord

/-- The four-coordinate point is a nonzero vector in the natural quotient. -/
theorem point_ne_zero : point ≠ 0 := by
  intro h
  rw [point] at h
  rcases (EightGeometry.coreToNatural_eq_zero _).mp h with h | h
  · have h0 := congrArg (fun f : Fin 8 → ZMod 2 => f ⟨0, by decide⟩) h
    change (1 : ZMod 2) = 0 at h0
    exact one_ne_zero h0
  · have h4 := congrArg (fun f : Fin 8 → ZMod 2 => f ⟨4, by decide⟩) h
    change (0 : ZMod 2) = 1 at h4
    exact zero_ne_one h4

/-- The four-coordinate point is singular for the half-weight form. -/
theorem point_singular : Eight.form point = 0 := by
  rw [point, EightGeometry.form_coreToNatural]
  decide

private theorem polar_pair (i j : Fin 8) (h : i.val / 4 = j.val / 4) :
    form.polarBilin point (coreToNatural (Fin 8) (pair i j)) = 0 := by
  change form (point + coreToNatural (Fin 8) (pair i j)) - form point -
    form (coreToNatural (Fin 8) (pair i j)) = 0
  rw [point, ←map_add]
  simp only [EightGeometry.form_coreToNatural]
  exact (by decide : ∀ i j : Fin 8, i.val / 4 = j.val / 4 →
    Atlas.Order20160A8.HalfWeight.binaryHalfWeight (pointWord + pair i j).val -
      Atlas.Order20160A8.HalfWeight.binaryHalfWeight pointWord.val -
      Atlas.Order20160A8.HalfWeight.binaryHalfWeight (pair i j).val = 0) i j h

local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance (g : Equiv.Perm (Fin 4)) : Decidable (g ∈ A4) :=
  inferInstanceAs (Decidable (g.sign = 1))
local instance : Fintype A4 := Subtype.fintype _
private theorem cubic_test : ∀ a : Product,
    a ^ 3 = 1 → a ≠ 1 → ∃ i j : Fin 8,
      i.val / 4 = j.val / 4 ∧
      Atlas.Order20160A8.HalfWeight.binaryHalfWeight
        (fun k => (pair i j).val ((blockHom a).symm k) - (pair i j).val k) = 1 := by
  decide +kernel

/-- Every nonidentity cubic in the actual four-block residual moves a
nonsingular vector in the perpendicular of the marked point. -/
theorem cubic_moved_nonsingular (a : Product) (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    ∃ v : natural (Fin 8), form.polarBilin point v = 0 ∧
      form (naturalRepresentation (Fin 8) (blockHom a) v - v) = 1 := by
  obtain ⟨i,j,hij,hq⟩ := cubic_test a ha hne
  refine ⟨coreToNatural (Fin 8) (pair i j),polar_pair i j hij,?_⟩
  rw [←coreToNatural_equivariant,←map_sub,EightGeometry.form_coreToNatural]
  exact hq

/-- The same calculation in arbitrary marked four-block coordinates, with
both the point and the actor conjugated by the same permutation. -/
theorem conjugate_cubic_moved_nonsingular (r : Equiv.Perm (Fin 8))
    (a : Product) (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    ∃ v : natural (Fin 8),
      form.polarBilin (naturalRepresentation (Fin 8) r point) v = 0 ∧
      form (naturalRepresentation (Fin 8) (r * blockHom a * r⁻¹) v - v) = 1 := by
  obtain ⟨v,hv,hq⟩ := cubic_moved_nonsingular a ha hne
  refine ⟨naturalRepresentation (Fin 8) r v,?_,?_⟩
  · simpa only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      ←map_add,form_invariant] using hv
  · have he : naturalRepresentation (Fin 8) (r * blockHom a * r⁻¹)
        (naturalRepresentation (Fin 8) r v) =
        naturalRepresentation (Fin 8) r (naturalRepresentation (Fin 8) (blockHom a) v) := by
      simp only [←Module.End.mul_apply,←map_mul]
      simp only [mul_assoc,inv_mul_cancel,mul_one]
    rw [he,←map_sub,form_invariant]
    exact hq
open BinaryPermutation.TerminalOrthogonal.FourBlockResidual Subgroup

private theorem point_fixed_mem (g : Equiv.Perm (Fin 8))
    (h : naturalRepresentation (Fin 8) g point = point) : g ∈ H := by
  have hd := congrArg Subtype.val h
  change deletedRepresentation (Fin 8) g ((constants (Fin 8)).mkQ pointWord.val) =
    (constants (Fin 8)).mkQ pointWord.val at hd
  obtain ⟨c,hc⟩ := (deleted_fixed_iff g pointWord.val).mp hd
  have hrel : ∀ i j : Fin 8,
      pointWord.val i = pointWord.val j ↔ i.val / 4 = j.val / 4 := by decide
  change ∀ i j : Fin 8, (g i).val / 4 = (g j).val / 4 ↔ i.val / 4 = j.val / 4
  intro i j
  rw [←hrel,←hrel]
  have hi := hc (g i)
  have hj := hc (g j)
  simp only [Equiv.symm_apply_apply] at hi hj
  have hr : ∀ a b c d : ZMod 2, a - c = b - d → (c = d ↔ a = b) := by decide
  exact hr _ _ _ _ (hi.trans hj.symm)

/-- A cubic fixing the marked point belongs to the literal four-block
residual, with the original permutation recovered by its block embedding. -/
theorem cubic_marking_of_fixed (g : Equiv.Perm (Fin 8))
    (hg : g ^ 3 = 1) (hne : g ≠ 1)
    (hfix : naturalRepresentation (Fin 8) g point = point) :
    ∃ a : Product, a ^ 3 = 1 ∧ a ≠ 1 ∧ blockHom a = g := by
  have hm : (⟨g,point_fixed_mem g hfix⟩ : H) ∈ primeToResidual 3 H :=
    mem_primeToResidual_of_pow (n := 1) (by apply Subtype.ext; exact hg)
  have hgR : g ∈ R := H_residual ▸ mem_map_of_mem H.subtype hm
  rw [←blockHom_range] at hgR
  obtain ⟨a,ha⟩ := hgR
  refine ⟨a,?_,?_,ha⟩
  · apply blockHom_injective
    rw [map_pow,map_one,ha,hg]
  · intro he
    apply hne
    rw [←ha,he,map_one]

/-- Point fixation and cubic order construct the block marking after any
simultaneous change of point coordinates. -/
theorem conjugate_cubic_marking_of_fixed (r g : Equiv.Perm (Fin 8))
    (hg : g ^ 3 = 1) (hne : g ≠ 1)
    (hfix : naturalRepresentation (Fin 8) g (naturalRepresentation (Fin 8) r point) =
      naturalRepresentation (Fin 8) r point) :
    ∃ a : Product, a ^ 3 = 1 ∧ a ≠ 1 ∧ g = r * blockHom a * r⁻¹ := by
  let k : Equiv.Perm (Fin 8) := r⁻¹ * g * r
  have hk : k ^ 3 = 1 := by
    change (MulAut.conj r⁻¹ g) ^ 3 = 1
    rw [←map_pow,hg,map_one]
  have hkn : k ≠ 1 := by
    intro he
    apply hne
    apply (MulAut.conj r⁻¹).injective
    exact he.trans (map_one (MulAut.conj r⁻¹)).symm
  have hkf : naturalRepresentation (Fin 8) k point = point := by
    change naturalRepresentation (Fin 8) (r⁻¹ * g * r) point = point
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hfix]
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  obtain ⟨a,ha,han,he⟩ := cubic_marking_of_fixed k hk hkn hkf
  refine ⟨a,ha,han,?_⟩
  rw [he]
  simp only [k,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]

end BinaryPermutation.TerminalOrthogonal.CubicMovement

