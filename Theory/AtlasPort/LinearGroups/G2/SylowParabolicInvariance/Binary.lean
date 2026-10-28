module

public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Intrinsic
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedSylowCenter

/-!
# Intrinsic root subgroups in the derived binary Sylow subgroup

The actual intersection of the positive-root group with G₂(2)′ has coordinate
condition t₂ + t₃ + t₅ = 0. Its central involutions give the highest-root group.
Its involutions in the second center give the two-long-root group: it suffices
to test the commutator with D(1)F(1) against E(1), together with the square
and intersection equations. The finite parameter test is kernel checked.

This treats the proper derived subgroup in the invariant-parabolic argument
of Aschbacher–Smith 2.3.9(7), printed p.526. The binary coordinate calculations
come from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open scoped commutatorElement
namespace Atlas.G2.SylowParabolicInvariance
open BinaryParabolicPair

private theorem binary_longRoot_le_derived :
    longRootLocal (F := ZMod 2) ≤ commutator (Model (ZMod 2)) := by
  rw [commutator_eq_longRootClosure]
  exact Subgroup.subset_normalClosure

private theorem binary_highestRoot_le_longRoot :
    highestRoot (F := ZMod 2) ≤ longRootLocal := by
  rintro _ ⟨a,rfl⟩
  exact rootA_mem_longRootLocal a.toAdd

theorem binary_highestRoot_iff (g : Model (ZMod 2)) :
    g ∈ highestRoot ↔ CentralInvolution derivedSylowAmbient g := by
  constructor
  · intro hg
    obtain ⟨hU,hs,hc⟩ := (highestRoot_iff_centralInvolution g).mp hg
    exact ⟨⟨hU, binary_longRoot_le_derived (binary_highestRoot_le_longRoot hg)⟩,
      hs, fun y hy => hc y hy.1⟩
  · rintro ⟨hg,hs,hc⟩
    have hz := derivedSylowAmbient_central_involution_mem hg hs
      (fun y hy => (hc y hy).eq.symm)
    exact (Subgroup.zpowers_le.mpr
      (show BinaryCore.z ∈ highestRoot (F := ZMod 2) from
        ⟨Multiplicative.ofAdd 1,rfl⟩)) hz

private theorem binary_unipotent_mem_derived (t : Fin 6 → ZMod 2) :
    unipotentProduct t ∈ commutator (Model (ZMod 2)) ↔ t 2 + t 3 + t 5 = 0 := by
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (unipotentProduct t) = 1 ↔ _
  simp only [unipotentProduct, map_mul, BinaryException.project_A,
    BinaryException.project_B, BinaryException.project_E, one_mul, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F]
  rw [← map_mul, ← map_mul, rootF_add, rootF_add]
  have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hb (t 2 + t 3 + t 5) with h | h
  · simp [h, rootF_zero]
  · rw [h]
    exact iff_of_false quotientBit_ne_one (by decide)

private def commutatorParameters (t u : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  unipotentProductParameters
    (unipotentProductParameters (unipotentProductParameters t u)
      (unipotentInverseParameters t)) (unipotentInverseParameters u)

private theorem unipotent_commutator (t u : Fin 6 → ZMod 2) :
    ⁅unipotentProduct t, unipotentProduct u⁆ =
      unipotentProduct (commutatorParameters t u) := by
  rw [commutatorElement_def, unipotentProduct_inv, unipotentProduct_inv,
    unipotentProduct_mul, unipotentProduct_mul, unipotentProduct_mul]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem binary_secondCentral_parameters : ∀ t : Fin 6 → ZMod 2,
    t 2 + t 3 + t 5 = 0 → unipotentProductParameters t t = 0 →
    unipotentProductParameters (commutatorParameters t ![0,0,0,1,0,1]) ![0,0,0,0,1,0] =
      unipotentProductParameters ![0,0,0,0,1,0] (commutatorParameters t ![0,0,0,1,0,1]) →
    t = ![t 0,t 1,0,0,0,0] := by
  decide +kernel

theorem binary_longRootLocal_iff (g : Model (ZMod 2)) :
    g ∈ longRootLocal ↔ SecondCentralInvolution derivedSylowAmbient g := by
  constructor
  · intro hg
    obtain ⟨hU,hs,hc⟩ := (longRootLocal_iff_secondCentralInvolution g).mp hg
    exact ⟨⟨hU, binary_longRoot_le_derived hg⟩, hs,
      fun y hy z hz => hc y hy.1 z hz.1⟩
  · intro h
    have hg := h.1.1
    rw [unipotent_eq_range] at hg
    obtain ⟨t,rfl⟩ := hg
    have ht := (binary_unipotent_mem_derived t).mp h.1.2
    have hs : unipotentProductParameters t t = 0 := by
      apply unipotentProduct_injective
      rw [← unipotentProduct_mul, ← pow_two, h.2.1, unipotentProduct_zero]
    have hu : unipotentProduct ![0,0,0,1,0,1] ∈ derivedSylowAmbient :=
      ⟨unipotentProduct_mem _, (binary_unipotent_mem_derived _).mpr (by decide)⟩
    have hv : unipotentProduct ![0,0,0,0,1,0] ∈ derivedSylowAmbient :=
      ⟨unipotentProduct_mem _, (binary_unipotent_mem_derived _).mpr (by decide)⟩
    have hc := (h.2.2 _ hu _ hv).eq
    rw [unipotent_commutator, unipotentProduct_mul, unipotentProduct_mul] at hc
    have hp := binary_secondCentral_parameters t ht hs (unipotentProduct_injective hc)
    rw [hp]
    refine ⟨Multiplicative.ofAdd (t 0,t 1), ?_⟩
    simp [longRootHom,unipotentProduct]

end Atlas.G2.SylowParabolicInvariance

end
