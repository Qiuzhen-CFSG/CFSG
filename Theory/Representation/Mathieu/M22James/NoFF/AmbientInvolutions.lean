module
public import Theory.Representation.Mathieu.M22James.NoFF.Involutions
public import Theory.Representation.Mathieu.M22James.Ambient
public import Theory.Representation.SymplecticConjugatePair.Ambient.Semilinear
/-!
# Outer involutions in the actual triple Mathieu extension

Every outer actor inverts the central cubic scalar and is therefore semilinear
for the nontrivial automorphism of F4. For such an involution the displacement
space equals the fixed space. Rank-nullity gives binary fixed codimension six.
Source: Aschbacher--Smith H.12.1(11), printed pp.393--395.
-/
public section
noncomputable section
open Sporadic.Mathieu Theory.GroupTheory
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
namespace Sporadic.Mathieu.M22TripleCover.NoFF
open Representation.SL2FourNatural Representation Representation.BinaryOffender
open Sporadic.Mathieu.M22TripleCover.Unitary
lemma outer_binaryCodim (g : actionGroup) (hg : orderOf g = 2)
    (ho : g ∉ coverSubgroup) :
    fixedCodim Ambient.binaryAction (Subgroup.zpowers g) = 6 := by
  have he := fixedCodim_map_equivariant Ambient.binaryAction Ambient.tripleFieldAction
    (MonoidHom.id _) binaryCoordinates (fun a v => by
      change binaryCoordinates (Ambient.binaryAction a v) =
        binaryCoordinates (Ambient.binaryAction a (binaryCoordinates.symm (binaryCoordinates v)))
      rw [binaryCoordinates.symm_apply_apply]) (Subgroup.zpowers g)
  simp only [Subgroup.map_id] at he
  have hd := SymplecticConjugatePair.Ambient.semilinear_involution_twice_codim
    Ambient.tripleFieldAction g (by simpa only [hg] using pow_orderOf_eq_one g)
    fieldFrobenius fieldFrobenius_involutive (by
      intro hh
      have h := congrArg (fun f : F ≃+* F => f QuadraticAlgebra.omega) hh
      revert h
      decide +kernel)
    (Ambient.tripleFieldAction_outer_semilinear g ho)
  have hv : Module.finrank (ZMod 2) Vector = 12 :=
    binaryCoordinates.finrank_eq.symm.trans binarySpace_finrank
  rw [hv, ← he] at hd
  omega
end Sporadic.Mathieu.M22TripleCover.NoFF
