module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Defs

/-!
# The geometric inverter seed in J.2.7(5)

The first paragraph on printed p.436 chooses an involution in an L-conjugate
of U outside Q, then conjugates it inside H to invert the specified B₅.
The two conjugators must both be retained: after the H-conjugation the
element need not belong to an L-conjugate of U with the original V fixed.

This record specifies that intermediate construction, without assuming
noncentral action or quaternion fusion. Elementary abelianness and J.2.6
will supply the involution and z-class assertions from its literal U-image.

Source: Aschbacher–Smith, J.2.7(5), printed p.436 (PDF p.447).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

/-- The actual two-conjugator seed, before the noncentral-action argument. -/
structure FiveInverterSeed (B5 : Sylow 5 d.toTypeRuSetup.H) where
  i : G
  l : d.L
  h : d.toTypeRuSetup.H
  mem_conjugate : i ∈ d.toTypeRuSetup.U.map
    (MulAut.conj ((h : G) * (l : G))).toMonoidHom
  not_mem_Q : i ∉ d.toTypeRuSetup.Q
  inverts : ∀ x ∈ B5Image B5, i * x * i⁻¹ = x⁻¹

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
