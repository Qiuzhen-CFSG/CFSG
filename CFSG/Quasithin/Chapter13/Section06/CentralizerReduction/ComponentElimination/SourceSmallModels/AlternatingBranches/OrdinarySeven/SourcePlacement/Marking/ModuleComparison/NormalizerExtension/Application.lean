module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.NormalizerExtension
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.Application

/-!
# Apply the extended ordinary-seven summand to fixed spaces

The normalizer extension discharges full-plus equivariance in the existing
fixed-codimension and fixed-centralizer arguments. The only module input is
the splitting for the actual component image, with binary complementary
kernel of dimension at most one. Its construction stays with the source
assembly owner; no codimension or centralizer conclusion is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.3.3(1),
printed p.84, and the ordinary A₇ branch of 13.6.22, printed p.932.
-/

public section
open Subgroup Equiv
open Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
variable {G : Type*} [Group G] [Finite G]
  (K L T : Subgroup G) (z v : G)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G))
  (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
  [IsElementaryAbelian 2 (WK K L T z v)]
  (hWT : WK K L T z v ≤ Tv T v)
  (φ : Gplus K L T z v hL hz →* Perm (Fin 7))
  (hφB : (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7))
  (d : NaturalSummand ((representation K L T z v hL hz hWT).comp
    (plusImage K L T z v hL hz K).subtype)
    (φ.comp (plusImage K L T z v hL hz K).subtype))
  (hd : Module.finrank (ZMod 2) d.projection.ker ≤ 1)

include hn hLv hφB d hd in
/-- Fixed codimensions for every subgroup of the full plus actor, from the
component splitting alone. -/
theorem extended_fixedCodim_eq (A : Subgroup (Gplus K L T z v hL hz)) :
    fixedCodim (representation K L T z v hL hz hWT) A =
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ) :=
  (extend_plus K L T z v hL hz hn hLv hWT φ hφB d hd).fixedCodim_eq A

include hn hLv hφB d hd in
/-- The same extension supplies the full actor's fixed-vector detector. -/
theorem extended_fixed_centralizer_le_thompson (hφ : Function.Injective φ)
    (g : Perm (Fin 7))
    (hg : ((plusImage K L T z v hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv T v))).map φ).map
        (MulAut.conj g).toMonoidHom = threeTranspositions) :
    plusImage K L T z v hL hz
      (Tv T v ⊓ centralizer
        (WK K L T z v ⊓ centralizer
          (Stellmacher.elementaryAbelianMaxJ (Tv T v) : Set G) : Set G)) ≤
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) :=
  fixed_centralizer_le_thompson K L T z v hL hz hWT φ hφ
    (extend_plus K L T z v hL hz hn hLv hWT φ hφB d hd) g hg
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
