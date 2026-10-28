module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.FinalCentralizers
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Displacement on the actual sections of H_C/V_H

The intersection calculation in the last paragraph of Aschbacher–Smith
13.8.28 bounds the image of Uγ ∩ H_C modulo V_H by two. For every binary
section S/E with V_H ≤ E ≤ S ≤ H_C, its literal coordinate homomorphism
therefore sends the commutators with Uγ into a subspace of dimension at
most one. This works even when H_C/V_H itself is nonabelian.

The kernel, subgroup inclusions and H-conjugation action remain those of
`BinaryConjugationSection`. Normality is relative to H and S. The source
consumer in `SourceApplication` supplies the commutator containment using
`final_centralizer_chain` and applies G.6.4 to a faithful irreducible section.
The source geometric and chief-factor hypotheses remain explicit there.

Source: *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), printed pp.965–966, proof of 13.8.28.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

variable {G : Type*} [Group G] [Finite G]
  {H S E : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W}

/-- The source order and intersection bounds control displacement on every
actual binary section above V_H and inside H_C. -/
theorem section_displacement_le_one
    (d : BinaryConjugationSection H S E ρ)
    (U C V Q : Subgroup G) (hVE : V ≤ E) (hSC : S ≤ C)
    (hCQ : C ≤ Q) (hU : Nat.card U = 32) (hstar : Q.relIndex U = 2)
    (hintersection : 8 ≤ Nat.card (U ⊓ V : Subgroup G))
    (hcomm : ⁅C, U⁆ ≤ C ⊓ U) (hUH : U ≤ H) (u : H) (hu : (u : G) ∈ U) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ u - LinearMap.id)) ≤ 1 := by
  let : Finite W := Finite.of_surjective
    (fun s : S => (d.coordinates s).toAdd) (fun w => d.onto (Multiplicative.ofAdd w))
  have hVC : V ≤ C := hVE.trans (d.kernel_le.trans hSC)
  have hindex := intersection_section_index_le_two U C V Q hVC hCQ hU hstar hintersection
  let D := (U ⊓ C) ⊓ S
  have hDC : D ≤ U ⊓ C := inf_le_left
  have hDS : D ≤ S := inf_le_right
  have hnzero (A B : Subgroup G) : A.relIndex B ≠ 0 :=
    (A.subgroupOf B).index_ne_zero_of_finite
  have hcard : Nat.card (d.imageSpace D) ≤ 2 := by
    change Nat.card ((D.subgroupOf S).map d.coordinates) ≤ 2
    rw [← relIndex_ker, d.kernel_eq, relIndex_subgroupOf hDS]
    exact (relIndex_le_of_le_left hVE (hnzero _ _)).trans
      ((relIndex_le_of_le_right hDC (hnzero _ _)).trans hindex)
  have hdim : Module.finrank (ZMod 2) (d.imageSpace D) ≤ 1 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcard
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show 2 ≤ Module.finrank (ZMod 2) (d.imageSpace D) by omega)
    omega
  have hbound : ⁅U, S⁆ ≤ (U ⊓ C) := by
    have hb := (commutator_mono hSC le_rfl).trans hcomm
    rw [commutator_comm S U, inf_comm C U] at hb
    exact hb
  have hUS : ⁅U, S⁆ ≤ D := by
    apply le_inf hbound
    exact le_normalizer_iff_commutator_le_right.mp (hUH.trans d.normalized)
  exact (Submodule.finrank_mono
    (d.displacement_range_le_imageSpace_of_commutator_le U D hUS u hu)).trans hdim

end CFSG.Quasithin.Chapter13.Section08.LinearFour
