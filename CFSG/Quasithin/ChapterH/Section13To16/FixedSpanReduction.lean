module

public import CFSG.Quasithin.ChapterH.Section13To16.Defs

/-!
# The dimension and transport steps in H.16.8

Two fixed spaces of dimension seven with intersection of dimension four
span a ten-dimensional space. Thus, in the eleven-dimensional Mathieu
code, any subgroup containing the two nonidentity actors has fixed-space
span of codimension at most one. If all its element fixed spaces lie in a
given ten-dimensional subspace, that span is exactly the subspace.

The final theorem here transports a bound on the native M₂₃ representation
to any actual M₂₃ code module. The native subgroup geometry and fixed-space
dimensions are still explicit inputs: these reductions do not yet establish
the unconditional source H.16.8.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.16.8, printed p.405; its use in 7.5.4, printed p.700.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section13To16

open Representation.BinaryOffender Sporadic.Mathieu

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The final dimension calculation, retaining each of the three local dimensions. -/
theorem fixedSpan_codim_le_one_of_pair [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 11)
    {A : Subgroup G} {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1)
    (hfa : Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) = 7)
    (hfb : Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers b)) = 7)
    (hab : Module.finrank (ZMod 2)
      ↥(fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers b)) = 4) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) ≤ 1 := by
  apply fixedSpaceSpan_codim_le_of_pair ρ ha ha1 hb hb1 1
  rw [hV, hfa, hfb, hab]

/-- The stronger quintet-branch conclusion, once its local containment is supplied. -/
theorem fixedSpan_eq_tenSpace_of_pair [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 10)
    (hle : ∀ c ∈ A, c ≠ 1 → fixedSpace ρ (Subgroup.zpowers c) ≤ U)
    (hfa : Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) = 7)
    (hfb : Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers b)) = 7)
    (hab : Module.finrank (ZMod 2)
      ↥(fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers b)) = 4) :
    fixedSpaceSpan ρ A = U := by
  apply fixedSpaceSpan_eq_of_pair ρ ha ha1 hb hb1 U hle
  rw [hU, hfa, hfb, hab]

/-- The source conclusion transports from the literal native representation.
The native theorem remains an explicit earlier input until the geometric
and module calculations are assembled. No finite-dimensionality hypothesis
is needed for this transport, since the marking is a linear equivalence. -/
theorem m23Code_fixedSpan_bound_of_native (hρ : MathieuCode.IsM23Code ρ)
    (hnative : ∀ A : Subgroup M23, IsElementaryAbelian 2 A → Nat.card A = 16 →
      Module.finrank (ZMod 2)
        (MathieuCode.Code ⧸ fixedSpaceSpan MathieuCode.m23CodeRepresentation A) ≤ 1)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) ≤ 1 := by
  obtain ⟨e, E, hE⟩ := hρ
  rw [fixedSpaceSpan_codim_map_equivariant ρ MathieuCode.m23CodeRepresentation
    e.toMonoidHom e.injective E hE A]
  let : IsElementaryAbelian 2 A := hA
  apply hnative _ (IsElementaryAbelian.map e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective, hcard]

end CFSG.Quasithin.ChapterH.Section13To16
