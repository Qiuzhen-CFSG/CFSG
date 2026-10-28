module
public import Theory.Representation.PermutationBasisHyperplane
public import Theory.Representation.BinaryPermutation.FivePairSylowBasis
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Normalizer
public import CFSG.Quasithin.ChapterE.Section04.Basic

/-!
# The fixed-space parameter of the two wreath modules

A faithful Sylow permutation basis gives a hyperplane with strictly larger
fixed space for every nontrivial elementary subgroup. Thus the next
fixed-space family is empty. Both literal wreath actions, including factor
exchange, have parameter at most one.

Source: Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Model
open ChapterE

theorem moduleA_le_one_of_sylow_permutedBasis
    {X V ι : Type*} [Group X] [Finite X] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite ι] (ρ : Representation (ZMod 2) X V) (hρ : Function.Injective ρ)
    (P : Sylow 2 X) [MulAction P ι]
    (b : Module.Basis ι (ZMod 2) V) (hb : ∀ g : P, ∀ i, ρ g (b i) = b (g • i)) :
    moduleA ρ ≤ 1 := by
  apply (moduleA_le_iff_next_family_empty ρ 1).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1.2
  obtain ⟨B, hBA, hB, hfix⟩ := hyperplane_witness_of_sylow_permutedBasis ρ hρ P b hb A
    (IsElementaryAbelian.isPGroup 2 A) hA.2.1.1
  exact hfix.ne (hA.2.2 B hBA (by rw [hB]; decide))

open BinaryPermutation BinaryPermutation.FiveTensorSquare

theorem tensor_moduleA_le_one : moduleA tensorWreathAction ≤ 1 := by
  let e : Small.sylow ≃* Small.P := (MonoidHom.ofInjective Small.embed_injective).symm
  let : MulAction Small.sylow Small.Point := MulAction.compHom Small.Point e.toMonoidHom
  apply moduleA_le_one_of_sylow_permutedBasis tensorWreathAction tensorWreathAction_injective
    Small.sylow Small.tensorBasis
  intro g i
  have he : Small.embed (e g) = (g : Wreath) := MonoidHom.apply_ofInjective_symm _ g
  rw [← he]
  exact Small.tensorBasis_permuted (e g) i

theorem pair_moduleA_le_one : moduleA FivePair.wreathRepresentation ≤ 1 := by
  let e : Small.sylow ≃* Small.P := (MonoidHom.ofInjective Small.embed_injective).symm
  let : MulAction Small.sylow Small.PairPoint := MulAction.compHom Small.PairPoint e.toMonoidHom
  apply moduleA_le_one_of_sylow_permutedBasis FivePair.wreathRepresentation
    FivePair.wreathRepresentation_injective Small.sylow Small.pairBasis
  intro g i
  have he : Small.embed (e g) = (g : Wreath) := MonoidHom.apply_ofInjective_symm _ g
  rw [← he]
  exact Small.pairBasis_permuted (e g) i

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Model
