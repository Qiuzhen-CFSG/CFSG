module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.Levi

/-!
# The marked local groups for even SU₄ double covers

The determinant-one plane local contains the same Sylow two-subgroup as the
full plane stabilizer. Its restriction to SL₂ has the literal block diagonal
Levi section, and its kernel is the Hermitian radical. We retain the maps to
the original standard SU₄ group when taking preimages in a central cover.

These interfaces support the double-cover calculation for the vanishing
unitary rows of Aschbacher–Smith I.1.3–4, printed pp.407–408 of
`refs/quasithin.pdf`, and
GLS3 §6.1. No splitting of a lifted radical is asserted here.
-/

@[expose] public noncomputable section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary PerfectCentralCovering

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure
namespace DoubleSplitting

universe u
variable {F : Type u} [Field F] [Finite F]

/-- The determinant-one factor of the actual plane parabolic. -/
abbrev Local (J : HermitianForm 4 F) : Subgroup (Standard J) :=
  UnitaryFourPlaneLocal.localFactor F (UnitaryFourFormTransport.standardForm J)

/-- Restriction to the marked plane, with its SL₂ codomain. -/
abbrev restriction (J : HermitianForm 4 F) :
    Local J →* Matrix.SpecialLinearGroup (Fin 2) F :=
  UnitaryFourPlaneLocal.factorRestriction F (UnitaryFourFormTransport.standardForm J)

/-- The intrinsic Hermitian radical in the determinant-one local group. -/
abbrev Radical (J : HermitianForm 4 F) : Subgroup (Local J) :=
  (restriction J).ker

/-- Embed the radical into the original standard SU₄ group. -/
def radicalInclusion (J : HermitianForm 4 F) : Radical J →* Standard J :=
  (Local J).subtype.comp (Radical J).subtype

/-- The embedded radical, with no abstract identification of the base group. -/
def ambientRadical (J : HermitianForm 4 F) : Subgroup (Standard J) :=
  (Radical J).map (Local J).subtype

/-- The full inverse image of the radical under the specified covering map. -/
def liftedRadical (J : HermitianForm 4 F) {E : Type u} [Group E]
    (d : Cover E (Standard J)) : Subgroup E :=
  (ambientRadical J).comap d.toMonoidHom

variable [CharP F 2]

/-- The existing literal SL₂ block diagonal section. -/
abbrev levi (J : HermitianForm 4 F) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Local J :=
  UnitaryFourPlaneRadical.levi F J.conj J.conj_involutive

/-- The same Levi map with its original SU₄ codomain. -/
def leviInclusion (J : HermitianForm 4 F) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Standard J :=
  (Local J).subtype.comp (levi J)

@[simp] theorem restriction_levi (J : HermitianForm 4 F)
    (A : Matrix.SpecialLinearGroup (Fin 2) F) : restriction J (levi J A) = A :=
  UnitaryFourPlaneRadical.factorRestriction_levi F J.conj J.conj_involutive A

theorem leviInclusion_injective (J : HermitianForm 4 F) :
    Function.Injective (leviInclusion J) :=
  Subtype.val_injective.comp
    (UnitaryFourPlaneRadical.levi_injective F J.conj J.conj_involutive)

/-- The determinant-one local still contains the constructed Sylow subgroup. -/
theorem local_index_odd (J : HermitianForm 4 F) : ¬ 2 ∣ (Local J).index := by
  let S := UnitaryFourSylow.sylow F J.conj J.conj_involutive
  have hSP : (S : Subgroup (Standard J)) ≤ Plane J :=
    (UnitaryFourSylow.upper_le_borel F J.conj J.conj_involutive).trans inf_le_right
  have hSL : (S : Subgroup (Standard J)) ≤ Local J :=
    UnitaryFourPlaneLocal.two_subgroup_le_localFactor F _ _ S.isPGroup' hSP
  exact fun h => S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hSL))

/-- Central transfer already applies to the determinant-one plane local. -/
theorem not_two_kernel_of_local_section (J : HermitianForm 4 F)
    {E : Type u} [Group E] [Finite E] (d : Cover E (Standard J))
    (s : Local J →* E) (hs : d.toMonoidHom.comp s = (Local J).subtype) :
    Nat.card d.toMonoidHom.ker ≠ 2 := by
  intro hd
  exact not_dvd_card_kernel_of_section d (Local J) (local_index_odd J) s hs
    (hd ▸ dvd_rfl)

end DoubleSplitting
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure
