module

public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.GroupTheory.CentralPChiefCore
public import Theory.GroupTheory.CentralPResidualCommutator

/-!
# B.7.2(1): the stabilizer in the reduced module

In the reduced setup V = I + Iᵃ, distinct Irr⁺ members have disjoint images
in V/C_V(X). A stabilizing element b of A preserves both images and fixes
their a-diagonal, hence acts trivially on the quotient. Its commutators
with X therefore lie in the actual quotient-action kernel, which is in O₂(X).

Central p-chief factors and O²(X) = X imply O₂(X) ≤ Z(X). The central
commutator homomorphism X → O₂(X) is then trivial by residuality, so b
centralizes X. Its displacement into C_V(X) now implies that b fixes
[V,X] = V, and faithfulness gives b = 1.

This proves the local stabilizer step, retaining the source's nontriviality
and finite-dimensional hypotheses. Both Irr⁺ memberships and the spanning
condition remain explicit for the moved-space reduction to supply. This
module does not assert the full irreducible-section invariance theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2(1), printed p.119 (PDF p.130).
-/

public section

namespace CFSG.Quasithin.ChapterB
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- In the reduced B.7.2 setup, the stabilizer in A of the moved Irr⁺ member is trivial. -/
theorem irreducible_stabilizer_eq_bot
    [Finite G] [FiniteDimensional (ZMod 2) V] (hf : Function.Injective ρ)
    {A X : Subgroup G} {I : Submodule (ZMod 2) V} {a : G}
    (hA : IsElementaryTwo A) (_hXne : X ≠ ⊥) (hr : pResidual 2 X = ⊤)
    (hXA : ⁅X, A⁆ = X) (hc : HasCentralPChiefFactors 2 X)
    (ha : a ∈ A) (hquad : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hsup : I ⊔ I.map (ρ a) = ⊤) :
    A ⊓ subspaceStabilizer ρ I = ⊥ := by
  apply bot_unique
  rintro b ⟨hbA, hbI⟩
  let _ : IsElementaryAbelian 2 A := hA.2
  have hab : Commute a b := setLike_mul_comm ha hbA
  have hAN : A ≤ normalizer (X : Set G) := by
    simpa only [hXA] using normalizer_commutator_ge_right X A
  have hd := displacement_fixed_of_stabilizes_irrPlus ρ hI hIa hne hsup
    (hAN ha) (hAN hbA) hab hbI (hquad b hbA)
  have hcomm (x : X) : ⁅(x : G), b⁆ ∈ (pCore 2 X).map X.subtype := by
    have hX : ⁅(x : G), b⁆ ∈ X :=
      hXA.le (commutator_mem_commutator x.property hbA)
    refine ⟨⟨⁅(x : G), b⁆, hX⟩, ?_, rfl⟩
    apply fixedQuotient_ker_le_pCore ρ hf X
    apply (mem_fixedQuotient_ker_iff ρ X _).mpr
    exact commutator_displacement_fixed ρ hd x
  have hbX := Subgroup.commute_of_central_p_commutator_of_isPPerfect X (pCore 2 X)
    ((pResidual_eq_top_iff 2 X).mp hr) pCore_isPGroup
    (pCore_le_center_of_centralPChiefFactors 2 hr hc) b hcomm
  have hfull : subspaceCommutator ρ ⊤ X = ⊤ := by
    apply top_unique
    calc
      ⊤ = I ⊔ I.map (ρ a) := hsup.symm
      _ ≤ subspaceCommutator ρ ⊤ X := ?_
    apply sup_le
    · conv_lhs => rw [← hI.choose_spec.1]
      exact Submodule.span_mono (by rintro _ ⟨x, hx, v, hv, rfl⟩; exact ⟨x, hx, v, Submodule.mem_top, rfl⟩)
    · conv_lhs => rw [← hIa.choose_spec.1]
      exact Submodule.span_mono (by rintro _ ⟨x, hx, v, hv, rfl⟩; exact ⟨x, hx, v, Submodule.mem_top, rfl⟩)
  apply Subgroup.mem_bot.mpr
  apply hf
  ext v
  simp only [map_one, Module.End.one_apply]
  apply fixes_commutatorSubspace_of_commutes_of_displacement_fixed ρ hbX hd
  rw [hfull]
  trivial
end CFSG.Quasithin.ChapterB
