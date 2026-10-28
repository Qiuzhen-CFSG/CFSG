module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BinaryPlanes.Recognition
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BinaryPlanes.CommutatorImages

/-!
# The two local binary-plane recognition tools

Commutator generation of D passes to action-difference generation of its
actual image in the elementary section B/Z. When that image is a plane and
the actual actor image has the specified S₃ quotient by its two-core,
recognition supplies irreducibility, the exact action kernel, and an
equivariant equivalence with the three-point core through that same quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.6(4), printed p.948 (PDF p.965). The chapter assembly retains the source
dimension, commutator and quotient-identification obligations.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

variable {G A : Type*} [Group G] [Group A]
variable (B Z : Subgroup G) [(Z.subgroupOf B).Normal]
  [IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B)]
variable (P : Subgroup G) (π : P →* A)
  (hPB : P ≤ normalizer (B : Set G))
  (ρ : Representation (ZMod 2) A (Additive (B ⧸ Z.subgroupOf B)))
  (hρ : SectionConjugationAlong P B Z π hPB ρ)
variable (R D : Subgroup G) (hRD : R ≤ normalizer (D : Set G))

local notation "Q" => Subgroup.map π (Subgroup.subgroupOf R P)
local notation "S" => localImage B Z P π hPB ρ hρ R D hRD

/-- Recognition for the literal local image and its actual actor subgroup.
Only the section is assumed elementary abelian. -/
theorem localImage_recognition [Finite G] (hRP : R ≤ P) (hDB : D ≤ B) (hgen : D = ⁅D, R⁆)
    (hd : Module.finrank (ZMod 2) (S).toSubmodule = 2)
    (e : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) :
    (S).toRepresentation.IsIrreducible ∧ (S).toRepresentation.ker = pCore 2 Q ∧
      Nonempty ((S).toRepresentation.Equiv ((BinaryPermutation.coreRepresentation (Fin 3)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Q))))) := by
  let : Finite Q := Finite.of_surjective (π.subgroupMap (R.subgroupOf P))
    (π.subgroupMap_surjective (R.subgroupOf P))
  exact BinaryPlaneRecognition.recognize (S).toRepresentation hd
    (localImage_coinvariants_eq_top B Z P π hPB ρ hρ R D hRD hRP hDB hgen) e

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors
