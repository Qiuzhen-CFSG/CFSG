module
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.SubspaceQuotient

/-!
# Quotients of literal binary conjugation sections

An invariant subspace of a marked section pulls back to its actual denominator.
Composing the original coordinate map with the linear quotient gives the
quotient action on the same original numerator, with precisely that kernel.
The actor also normalizes the original denominator, and the relative group
index equals the coordinate-space order.

The nonblock elementary-core argument uses this construction after selecting
an irreducible subquotient, retaining both subgroup endpoints and conjugation.
Source: the submodule--quotient construction for group representations.
-/

@[expose] public section
noncomputable section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H A B : Subgroup G} {ρ : Representation (ZMod 2) H W}
  (d : BinaryConjugationSection H A B ρ)

include d

/-- The original actor preserves the denominator of its marked section. -/
theorem kernel_normalized : H ≤ normalizer (B : Set G) := by
  apply le_normalizer_iff.mpr
  intro h hh b hb
  have hbA : b ∈ A := d.kernel_le hb
  apply (d.coordinates_eq_one_iff ⟨h*b*h⁻¹,
    (mem_normalizer_iff.mp (d.normalized hh) b).mp hbA⟩).mp
  apply Multiplicative.toAdd.injective
  rw [d.equivariant ⟨h,hh⟩ ⟨b,hbA⟩,
    (d.coordinates_eq_one_iff _).mpr hb]
  exact map_zero _

/-- The original relative index is the order of the coordinate space. -/
theorem relIndex_eq_card : B.relIndex A = Nat.card W := by
  let := d.kernel_normal
  change (B.subgroupOf A).index = _
  rw [Subgroup.index_eq_card,Nat.card_congr d.quotientEquiv.toEquiv]
  rfl

/-- Compose the given coordinates with the literal linear quotient. -/
def quotientCoordinates (N : Subrepresentation ρ) :
    A →* Multiplicative (W ⧸ N.toSubmodule) :=
  N.toSubmodule.mkQ.toAddMonoidHom.toMultiplicative.comp d.coordinates

/-- The quotient retains its original numerator, preimage kernel and action. -/
def quotientSection (N : Subrepresentation ρ) :
    BinaryConjugationSection H A (d.invariantPreimage N) N.quotientRepresentation where
  section_le := d.section_le
  kernel_le := d.invariantPreimage_le N
  normalized := d.normalized
  coordinates := d.quotientCoordinates N
  onto := N.toSubmodule.mkQ_surjective.comp d.onto
  kernel_eq := by
    ext a
    change N.toSubmodule.mkQ (d.coordinates a).toAdd = 0 ↔ (a : G) ∈ d.invariantPreimage N
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,d.mem_invariantPreimage]
    exact ⟨fun h => ⟨a.property,h⟩,fun ⟨_,h⟩ => h⟩
  equivariant h a := by
    change N.toSubmodule.mkQ (d.coordinates _).toAdd =
      N.toSubmodule.mkQ (ρ h (d.coordinates a).toAdd)
    rw [d.equivariant]
end Representation.BinaryConjugationSection
