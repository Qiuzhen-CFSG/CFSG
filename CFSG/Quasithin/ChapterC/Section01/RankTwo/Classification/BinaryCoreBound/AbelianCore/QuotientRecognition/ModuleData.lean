module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Coordinates for a homogeneous natural fixed-space quotient

The data specify a surjective linear map onto copies of the natural binary
SL₃ module, with kernel exactly the full fixed space. One automorphism of the
actual matrix group marks all summands together, allowing the graph twist.
No existence or semisimplicity theorem is asserted by this definition.

This is the module-theoretic interface for the binary specialization of
Aschbacher–Smith B.5.1(1)(i),(ii), printed pp.99–103 of the combined manuscript
of 1 March 2004, used in the abelian alternatives of C.1.34, pp.136–137.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open Representation Representation.BinaryOffender
universe v

abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
/-- Explicit natural coordinates for the quotient by fixed vectors. -/
structure ModuleQuotient (ρ : Representation (ZMod 2) SL V) (m : ℕ) where
  marking : SL ≃* SL
  projection : V →ₗ[ZMod 2] (Fin m → Fin 3 → ZMod 2)
  surjective : Function.Surjective projection
  kernel : projection.ker = fixedSpace ρ ⊤
  equivariant : ∀ (g : SL) (v : V) (i : Fin m),
    projection (ρ g v) i = Representation.specialLinearNatural 3 (marking g) (projection v i)

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
