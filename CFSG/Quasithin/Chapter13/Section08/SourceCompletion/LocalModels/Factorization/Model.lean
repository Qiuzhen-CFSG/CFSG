module

public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.PointStabilizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.SourceMarking.ModelCommutator.CentralExtension


/-!
# The factorization in the marked triple-cover point stabilizer

For every actual natural point, the hexacode-cover stabilizer maps onto S₄
with its cubic center as kernel. Its two-residual is therefore the join of
its derived subgroup and this center. The derived subgroup is precisely
the residual of the commutator with the marked Sylow two-subgroup.

Source: Aschbacher–Smith, Lemma 13.2.2(3), printed p.877.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CoverFactorization
open Representation.Hexacode
open Representation.Hexacode.CubicLocalModel
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

private theorem symmetric_center_trivial (g : Equiv.Perm (Fin 4))
    (h : ∀ y, y*g=g*y) : g=1 := by
  revert g
  decide +kernel

theorem center_le_stabilizer (W : Submodule (ZMod 2) Natural) :
    center H ≤ stabilizer W := by
  intro g hg
  rw [← even_kernel_eq_center] at hg
  change ∀ w, naturalAction g w ∈ W ↔ w ∈ W
  change ∀ w, BinaryPermutation.naturalRepresentation (Fin 6)
    (Atlas.Codes.hexEvenCoordinate g).val w ∈ W ↔ w ∈ W
  rw [show Atlas.Codes.hexEvenCoordinate g = 1 from hg]
  simp

theorem symmetric_kernel_image (W : Submodule (ZMod 2) Natural)
    (hd : Module.finrank (ZMod 2) W=1) :
    (Orders.symmetricFourMap W hd).ker.map (stabilizer W).subtype = center H := by
  let f := Orders.symmetricFourMap W hd
  have hf := Orders.symmetricFourMap_surjective W hd
  have hz : center H ≤ f.ker.map (stabilizer W).subtype := by
    intro g hg
    let x : stabilizer W := ⟨g,center_le_stabilizer W hg⟩
    refine ⟨x,?_,rfl⟩
    apply symmetric_center_trivial
    intro y
    obtain ⟨a,rfl⟩ := hf y
    rw [← map_mul, ← map_mul]
    apply congrArg f
    apply Subtype.ext
    exact mem_center_iff.mp hg a.val
  apply le_antisymm _ hz
  exact (eq_of_le_of_card_ge hz (by
    rw [card_map_of_injective (stabilizer W).subtype_injective,
      Orders.symmetricFourMap_kernel_card, even_center_card])).ge

theorem model_factorization (W : Submodule (ZMod 2) Natural)
    (hd : Module.finrank (ZMod 2) W=1) (U : Sylow 2 H)
    (hU : (U:Subgroup H) ≤ stabilizer W) :
    pointResidual W = commutatorResidual W U ⊔ center H := by
  let f := Orders.symmetricFourMap W hd
  have hf := Orders.symmetricFourMap_surjective W hd
  have hk := Orders.symmetricFourMap_kernel_central W hd
  have he := Theory.SpecificGroups.SymmetricFourResidual.residual_eq_derived_sup_kernel
    f hf (by rw [Orders.symmetricFourMap_kernel_card]; decide)
  have hc := ModelCommutator.central_symmetric_residual_commutator f hf hk (U.subtype hU)
  have hh : (⁅pResidual 2 (stabilizer W), (U.subtype hU:Subgroup (stabilizer W))⁆).map
      (stabilizer W).subtype = ⁅pointResidual W,(U:Subgroup H)⁆ := by
    rw [map_commutator, Sylow.coe_subtype, map_subgroupOf_eq_of_le hU]
    rfl
  have hcm := congrArg (fun A : Subgroup (stabilizer W) => A.map (stabilizer W).subtype) hc
  rw [map_embedded_pResidual,hh] at hcm
  change commutatorResidual W U = (commutator (stabilizer W)).map (stabilizer W).subtype at hcm
  change (pResidual 2 (stabilizer W)).map (stabilizer W).subtype = _
  rw [he,Subgroup.map_sup,←hcm,symmetric_kernel_image]
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CoverFactorization

end
