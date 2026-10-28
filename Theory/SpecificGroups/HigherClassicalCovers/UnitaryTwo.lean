module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.Model
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
public import Theory.GroupTheory.UniversalCoverKernelTransport

/-!
# Transporting the ternary symplectic universal double cover

An actual isomorphism with PSp₄(3) transports the proved universal covering
Sp₄(3) → Sp₄(3)/Z(Sp₄(3)). The projection equation retains that literal
quotient map. Restricting a commuting square identifies its kernel with C₂;
comparison of universal covers gives the same group for the canonical kernel.
The construction permits different universes for the original group and model.

The final application combines this with the arbitrary-field and arbitrary-form
unitary comparison from `Model`. Its one remaining explicit input is a genuine
isomorphism `StandardPSU ≃* PSpThree`. Until that exceptional isomorphism is
constructed, this is a conditional reduction of Aschbacher–Smith I.1.4(1),
printed p.408, `refs/quasithin.pdf`, and does not prove the U₄(2) source row.
The symplectic universal property has no remaining premise.
-/

public section
noncomputable section

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour.CentralCovers

universe u v

abbrev SpThree := OddPrime.Sp (ZMod 3)
abbrev PSpThree := OddPrime.PSp (ZMod 3)

local instance ternaryLarge : Fact (2 < Nat.card (ZMod 3)) := ⟨by simp⟩

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- The actual comparison supplies quasisimplicity; no recognition premise is added. -/
theorem quasisimpleOfEquiv (e : G ≃* PSpThree) : IsQuasisimple G :=
  IsQuasisimple.of_mulEquiv e.symm

/-- The literal symplectic quotient followed by the specified inverse comparison. -/
@[expose] def coverOfEquiv (e : G ≃* PSpThree) :
    let : IsQuasisimple G := quasisimpleOfEquiv e
    Covering SpThree G := by
  let : IsQuasisimple G := quasisimpleOfEquiv e
  exact (Covering.ofMulEquiv e.symm).comp (OddPrime.quotientCover (ZMod 3))

theorem coverOfEquiv_toMonoidHom (e : G ≃* PSpThree) :
    let : IsQuasisimple G := quasisimpleOfEquiv e
    (coverOfEquiv e).toMonoidHom =
      e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SpThree)) := by
  let : IsQuasisimple G := quasisimpleOfEquiv e
  rfl

/-- The covering commutes with the literal quotient map. -/
theorem coverOfEquiv_projection (e : G ≃* PSpThree) (x : SpThree) :
    e (coverOfEquiv e x) = QuotientGroup.mk' (Subgroup.center SpThree) x :=
  e.apply_symm_apply _

/-- The transported double cover is universal in every target universe. -/
theorem coverOfEquiv_isUniversal (e : G ≃* PSpThree) :
    let : IsQuasisimple G := quasisimpleOfEquiv e
    Covering.IsUniversal.{u, 0, v} (coverOfEquiv e) := by
  let : IsQuasisimple G := quasisimpleOfEquiv e
  exact (OddPrime.quotientCover_isUniversal (p := 3) (by decide)
    (by simp : Nat.card (ZMod 3) = 3)).comp_ofMulEquiv e.symm

/-- Identify the full group structure of the kernel of the explicit covering. -/
def coverKernelEquivTwo (e : G ≃* PSpThree) :
    let : IsQuasisimple G := quasisimpleOfEquiv e
    (coverOfEquiv e).toMonoidHom.ker ≃* Multiplicative (ZMod 2) := by
  let : IsQuasisimple G := quasisimpleOfEquiv e
  exact (Covering.kerMulEquivOfSquare (coverOfEquiv e).toMonoidHom
    (OddPrime.quotientCover (ZMod 3)).toMonoidHom (MulEquiv.refl SpThree) e
    (fun x => (coverOfEquiv_projection e x).symm)).trans
      (OddPrime.kernelEquivC2 (by decide))

/-- Identify the canonical universal-projection kernel across model universes. -/
def canonicalKernelEquivTwo (e : G ≃* PSpThree) :
    let : IsQuasisimple G := quasisimpleOfEquiv e
    (PerfectCentralCovering.universalProjection G).ker ≃* Multiplicative (ZMod 2) := by
  let : IsQuasisimple G := quasisimpleOfEquiv e
  exact (PerfectCentralCovering.schurMultiplierEquivOfUniversal e
    (OddPrime.quotientCover (ZMod 3))
    (OddPrime.quotientCover_isUniversal (p := 3) (by decide) (by simp))).trans
      (OddPrime.kernelEquivC2 (by decide))

variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 4 F)

local instance projectiveFinite : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective (project J) (project_surjective J)

/-- Extend a concrete exceptional isomorphism to every allowed unitary form. -/
def projectiveEquivPSpOfStandard (hF : Nat.card F = 4)
    (hc : ∀ x, J.conj x = x ^ 2) (e : StandardPSU ≃* PSpThree) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃* PSpThree :=
  (projectiveEquivStandard J hF hc).trans e

/-- The literal U₄(2) cover and multiplier calculation, conditional only on the
concrete exceptional isomorphism. Final source assembly must construct `e`. -/
theorem universal_double_cover_of_standardEquiv (hF : Nat.card F = 4)
    (hc : ∀ x, J.conj x = x ^ 2) (e : StandardPSU ≃* PSpThree) :
    let c := projectiveEquivPSpOfStandard J hF hc e
    let : IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) := quasisimpleOfEquiv c
    Covering.IsUniversal.{u, 0, v} (coverOfEquiv c) ∧
      Nonempty ((coverOfEquiv c).toMonoidHom.ker ≃* Multiplicative (ZMod 2)) ∧
      Nonempty ((PerfectCentralCovering.universalProjection
        (ProjectiveSpecialUnitaryMatrixGroup J)).ker ≃* Multiplicative (ZMod 2)) := by
  let c := projectiveEquivPSpOfStandard J hF hc e
  let : IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J) := quasisimpleOfEquiv c
  exact ⟨coverOfEquiv_isUniversal c, ⟨coverKernelEquivTwo c⟩, ⟨canonicalKernelEquivTwo c⟩⟩


end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
