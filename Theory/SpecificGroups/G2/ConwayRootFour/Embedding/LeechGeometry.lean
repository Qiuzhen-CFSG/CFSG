module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LocalGeometry
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Coordinates

/-!
# Extending the local Leech coordinate formulas to the generated group

A concrete `LocalCoordinates` witness places all generators in C_G(I) and
identifies their action on V = C_(Λ/2Λ)(U) with the specified six-dimensional
matrices. Closure induction extends these formulas to every element of the
literal generated subgroup. Injectivity of the coordinate map makes the
induced linear map unique, so these maps form a homomorphism.

The independent assertion `CentralizerFaithful` then proves that this entire
generated action is faithful. `toCoordinateGeometry` supplies exactly the
input of `Embedding.CoordinateGeometry.exists_marked_embedding`.
Both the local-coordinate construction and the fixed-space kernel assertion
remain explicit hypotheses; no unconditional geometry is claimed here.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
used by Aschbacher–Smith I.2.2(5), printed p.411/PDF422. The actual Leech
and octonion carriers come from the existing attributed ATLAS ports.
-/

public noncomputable section

open Matrix Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
open OctonionLocals

namespace LocalCoordinates
variable (D : LocalCoordinates)

theorem localGroup_le_centralizerI : localGroup D.long D.short D.swap ≤ centralizerI := by
  apply (Subgroup.closure_le centralizerI).mpr
  rintro _ ⟨((A | a) | i), rfl⟩
  · exact D.long_mem A
  · exact D.short_mem a
  · exact D.swap_mem

private def Intertwines (g : LeechCentralQuotient) (a : LinearGroup) : Prop :=
  ∀ v, quotientModTwoRepresentation g (D.coordinates v) = D.coordinates (a v)

private theorem intertwines_one : D.Intertwines 1 1 := by
  intro v
  rw [map_one]
  rfl

private theorem intertwines_mul {g h : LeechCentralQuotient} {a b : LinearGroup}
    (hg : D.Intertwines g a) (hh : D.Intertwines h b) :
    D.Intertwines (g * h) (a * b) := by
  intro v
  rw [map_mul]
  change quotientModTwoRepresentation g (quotientModTwoRepresentation h (D.coordinates v)) = _
  rw [hh, hg]
  rfl

private theorem intertwines_inv {g : LeechCentralQuotient} {a : LinearGroup}
    (hg : D.Intertwines g a) : D.Intertwines g⁻¹ a⁻¹ := by
  intro v
  apply (quotientModTwoRepresentation g).injective
  rw [map_inv]
  change quotientModTwoRepresentation g ((quotientModTwoRepresentation g).symm
    (D.coordinates v)) = quotientModTwoRepresentation g (D.coordinates (a.symm v))
  rw [LinearEquiv.apply_symm_apply, hg, LinearEquiv.apply_symm_apply]

private theorem exists_intertwines (g : localGroup D.long D.short D.swap) :
    ∃ a, D.Intertwines g a := by
  obtain ⟨g, hg⟩ := g
  change ∃ a, D.Intertwines g a
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨action (generator i), D.on_generators i⟩
  | one => exact ⟨1, D.intertwines_one⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, D.intertwines_mul ha hb⟩
  | inv x hx ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨a⁻¹, D.intertwines_inv ha⟩

private theorem intertwines_unique {g : LeechCentralQuotient} {a b : LinearGroup}
    (ha : D.Intertwines g a) (hb : D.Intertwines g b) : a = b := by
  apply LinearEquiv.ext
  intro v
  exact D.coordinates_injective ((ha v).symm.trans (hb v))

/-- The generator formulas extend to a linear action of the entire generated group. -/
def representation : localGroup D.long D.short D.swap →* LinearGroup where
  toFun g := (D.exists_intertwines g).choose
  map_one' := D.intertwines_unique (D.exists_intertwines 1).choose_spec D.intertwines_one
  map_mul' g h := D.intertwines_unique (D.exists_intertwines (g * h)).choose_spec
    (D.intertwines_mul (D.exists_intertwines g).choose_spec (D.exists_intertwines h).choose_spec)

theorem representation_equivariant (g : localGroup D.long D.short D.swap) (v : Six F) :
    quotientModTwoRepresentation g.val (D.coordinates v) =
      D.coordinates (D.representation g v) :=
  (D.exists_intertwines g).choose_spec v

theorem representation_on_generators (i : Generator F) :
    D.representation (localGeneratorIn D.long D.short D.swap i) = action (generator i) :=
  D.intertwines_unique (D.exists_intertwines _).choose_spec (D.on_generators i)

theorem representation_injective (hfaith : CentralizerFaithful) :
    Function.Injective D.representation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  apply Subtype.ext
  apply hfaith g.val (D.localGroup_le_centralizerI g.property)
  intro v hv
  obtain ⟨w, rfl⟩ := (D.coordinates_range v).mp hv
  rw [D.representation_equivariant, MonoidHom.mem_ker.mp hg]
  rfl

/-- Conditional final assembly. The two independent Leech construction
obligations must both be proved before this yields an inhabitant. -/
def toCoordinateGeometry (hfaith : CentralizerFaithful) : CoordinateGeometry where
  long := D.long
  short := D.short
  swap := D.swap
  representation := D.representation
  faithful := D.representation_injective hfaith
  on_generators := D.representation_on_generators
  marked := D.marked

end LocalCoordinates
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
