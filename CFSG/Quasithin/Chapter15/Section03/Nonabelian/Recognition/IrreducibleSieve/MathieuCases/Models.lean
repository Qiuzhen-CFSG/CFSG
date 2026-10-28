module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules

/-!
# The Mathieu alternatives of G.9.3

These alternatives specify the actual component representations: the
twelve-point permutation heart for M₁₂, and the native code and cocode for
M₂₂ and M₂₄. The ambient extension in case (2) has a genuine perfect triple
cover as kernel and a splitting outer involution. Its quotient map and
central-quotient identification retain both layers of the source notation
`Z₂ / M̂₂₂`. No identification of its twelve-dimensional module is assumed.

The predicates are independent of the local restrictions in `SourceData`.
Here the source's `G,H` are our ambient actor and component join respectively.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.9.3(0)–(2),
printed pp.353–357; G.7.3 and its proof, p.348; H.11–H.13, pp.392–395.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases

open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterH.Section10To12

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- An exact extension by an involutory outer automorphism of a genuine
perfect triple cover of M₂₂. In particular this is not `MulAut` of the cover,
whose inner automorphisms lose its central subgroup of order three. -/
structure TripleExtension (H : Type*) [Group H] where
  projection : H →* Multiplicative (ZMod 2)
  surjective : Function.Surjective projection
  cover : IsTripleM22 projection.ker
  lift : H
  lift_square : lift ^ 2 = 1
  lift_image : projection lift = Multiplicative.ofAdd 1
  outer : ¬ ∃ k : projection.ker,
    MulAut.conjNormal (H := projection.ker) lift = MulAut.conj k

/-- The literal G.9.3 Mathieu alternatives, including their distinct actor
bounds, degrees, and actual component-module identifications. -/
inductive Alternative (ρ : Representation (ZMod 2) H W) (K : Subgroup H)
    (m : ℕ) : Prop
  | m12 (rank : m = 4) (degree : Module.finrank (ZMod 2) W = 10)
      (action : Quasiequivalent (ρ.comp K.subtype) m12HeartRepresentation) :
      Alternative ρ K m
  | m22 (rank : 4 ≤ m) (degree : Module.finrank (ZMod 2) W = 10)
      (action : Quasiequivalent (ρ.comp K.subtype) MathieuCode.m22CodeRepresentation ∨
        Quasiequivalent (ρ.comp K.subtype) MathieuCode.m22CocodeRepresentation) :
      Alternative ρ K m
  | m24 (rank : 5 ≤ m) (degree : Module.finrank (ZMod 2) W = 11)
      (action : Quasiequivalent (ρ.comp K.subtype) MathieuCode.codeRepresentation ∨
        Quasiequivalent (ρ.comp K.subtype) MathieuCode.cocodeRepresentation) :
      Alternative ρ K m
  | triple (rank : m = 5) (degree : Module.finrank (ZMod 2) W = 12)
      (extension : Nonempty (TripleExtension H)) : Alternative ρ K m

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases
