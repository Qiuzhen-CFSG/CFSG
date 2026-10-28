module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction
public import Theory.Representation.PSL3Two.SingerRestriction.FiveSpace

/-!
# The source five-space restriction in groups of type Ru

The published Singer and cubic images use the original common Ru1 quotient
map. Their proved orders and normalization instantiate the concrete Steinberg
restriction theorem. The centralizer subspace A and its dimension, Singer
invariance and fixed-plane containment remain explicit for the parent proof.

Source: Aschbacher–Smith, J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

public section

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- J.2.3's five-space restriction for the literal Singer and cubic images under
the original Ru1 quotient map. The construction of the centralizer subspace A
is separate; no decomposition or cubic-invariance hypothesis is imposed here. -/
theorem SingerChoice.fiveSpace (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (hB : Nat.card (cubicSubgroup d B) = 3)
    (A : Submodule (ZMod 2) BinaryLinearThree.Steinberg)
    (hA5 : Module.finrank (ZMod 2) A = 5)
    (hFA : fixedSpace BinaryLinearThree.S (singerImage d B c) ≤ A)
    (hA : ∀ h ∈ singerImage d B c, ∀ a ∈ A, BinaryLinearThree.S h a ∈ A) :
    let H := singerImage d B c
    let M := displacementSpan BinaryLinearThree.S H A
    Module.finrank (ZMod 2) M = 3 ∧
    A = fixedSpace BinaryLinearThree.S H ⊔ M ∧
    fixedSpace BinaryLinearThree.S H ⊓ M = ⊥ ∧
    (∀ g ∈ cubicImage d B,
      A.map (BinaryLinearThree.S g) = A ∧ M.map (BinaryLinearThree.S g) = M) ∧
    (∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 →
      ∃ h ∈ H, BinaryLinearThree.S h v = w) :=
  BinaryLinearThree.SingerRestriction.FiveSpace.restriction
    (singerImage d B c) (cubicImage d B) (singerImage_card d B c)
    (cubicImage_card d B hB) (cubicImage_normalizes_singerImage d B c)
    A hA5 hFA hA
end CFSG.Quasithin.ChapterJ.SpecialCore
