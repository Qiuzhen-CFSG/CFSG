module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes.Reduction
public import Theory.Representation.BinaryGroupAction
public import Theory.GroupAction.CommutingFixedKernel
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer


/-!
# Thompson's fixed-space kernel for the original Fitting commutator

With O₂(G)=1, the Fitting subgroup and F_A=[F(G),A] have odd order.
The relative centralizer B=C_A(F_A) is a two-group. On the elementary
abelian additive group of the binary module, the commuting fixed-kernel
 theorem makes C_{F_A}(C_V(B)) a two-group. Its odd order makes it trivial.
Thus F_A acts faithfully on the original C_V(B), without assuming a
normal three-subgroup or solvability of G. Commutation also proves
[C_V(B),F_A] ≤ C_V(B), the literal fixed-space containment in the reduction.

The proof adapts the private commuting-kernel argument in
`SolvableStructure/ThreeConjugates/FixedSpace.lean`, using the shared
binary-action bridge. Its order-three assumption is replaced here by the
proved oddness of F_A.
Source: Aschbacher–Smith, B.1.9 proof, first paragraph,
printed p.71 (PDF p.82), combined 1 March 2004 manuscript.
-/

public section

namespace CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
open Subgroup Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem commuting_fixed_kernel_isTwoGroup [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (Q E : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQE : ⁅Q, E⁆ = ⊥) :
    IsPGroup 2 (subspaceKernel ρ (fixedSpace ρ Q) E) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let f := MulDistribMulAction.toMulAut G (Multiplicative V)
  have hf' : Function.Injective f := by
    intro g h he
    apply hf
    ext v
    exact congrArg (fun a : MulAut (Multiplicative V) =>
      (a (Multiplicative.ofAdd v)).toAdd) he
  let K := subspaceKernel ρ (fixedSpace ρ Q) E
  have hc : ⁅Q.map f, K.map f⁆ = ⊥ := by
    rw [← map_commutator]
    have hb : ⁅Q, K⁆ = ⊥ := le_bot_iff.mp
      ((commutator_mono le_rfl (subspaceKernel_le ρ _ E)).trans hQE.le)
    rw [hb, Subgroup.map_bot]
  have hfix : K.map f ≤ fixingSubgroup (MulAut (Multiplicative V))
      (FixedPoints.subgroup (Q.map f) (Multiplicative V) : Set (Multiplicative V)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hv' : v.toAdd ∈ fixedSpace ρ Q := by
      intro q
      exact congrArg Multiplicative.toAdd (hv ⟨f q, mem_map_of_mem f q.property⟩)
    exact congrArg Multiplicative.ofAdd (hb.2 v.toAdd hv')
  have hp := isPGroup_of_commuting_fixes_fixed (Q.map f) (K.map f) (hQ.map f) hc hfix
  exact hp.of_injective (f.subgroupMap K)
    (fun x y h => Subtype.ext (hf' (congrArg Subtype.val h)))

/-- The ambient trivial two-core forces every Fitting commutator to be odd. -/
theorem oddPart_odd [Finite G] (hcore : pCore 2 G = ⊥) (A : Subgroup G) :
    Odd (Nat.card (oddPart A)) := by
  have hle : oddPart A ≤ pPrimeCore 2 G :=
    (commutator_le_left _ _).trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)
  exact (Nat.Coprime.of_dvd_right (card_dvd_of_le hle)
    (pPrimeCore_coprime_card (p := 2) (G := G))).odd_of_left

/-- Thompson A × B faithfulness on C_V(B), for the literal B=C_A(F_A). -/
theorem fitting_fixed_kernel_eq_bot [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsElementaryTwo A) :
    subspaceKernel ρ (fixedSpace ρ (kernelActor A)) (oddPart A) = ⊥ := by
  have hQ : IsPGroup 2 (kernelActor A) := by
    let := hA.2
    exact (IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left
  have hc : ⁅kernelActor A, oddPart A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hp := commuting_fixed_kernel_isTwoGroup ρ hf (kernelActor A) (oddPart A) hQ hc
  have ho : Odd (Nat.card (subspaceKernel ρ (fixedSpace ρ (kernelActor A)) (oddPart A))) :=
    (oddPart_odd hcore A).of_dvd_nat (card_dvd_of_le (subspaceKernel_le ρ _ _))
  exact card_eq_one.mp (hp.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat)

/-- A nontrivial Fitting commutator moves the B-fixed space nontrivially. -/
theorem testSpace_ne_bot [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hne : oddPart A ≠ ⊥) :
    testSpace ρ A ≠ ⊥ := by
  intro hz
  have hfix := (subspaceCommutator_eq_bot_iff ρ
    (fixedSpace ρ (kernelActor A)) (oddPart A)).mp hz
  have he : subspaceKernel ρ (fixedSpace ρ (kernelActor A)) (oddPart A) = oddPart A := by
    apply le_antisymm (subspaceKernel_le ρ _ _)
    intro a ha
    exact ⟨ha, fun w hw => hfix hw ⟨a, ha⟩⟩
  exact hne (he.symm.trans (fitting_fixed_kernel_eq_bot ρ hf hcore hA))

/-- The centralizer B fixes the source test space pointwise. -/
theorem testSpace_le_fixed (A : Subgroup G) :
    testSpace ρ A ≤ fixedSpace ρ (kernelActor A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, v, hv, rfl⟩
  intro b
  have hcomm : x * (b : G) = (b : G) * x :=
    mem_centralizer_iff.mp b.property.2 x hx
  have hact : ρ (b : G) (ρ x v) = ρ x (ρ (b : G) v) := by
    simpa only [map_mul, Module.End.mul_apply] using
      congrArg (fun g => ρ g v) hcomm.symm
  change ρ (b : G) (ρ x v - v) = ρ x v - v
  rw [map_sub, hact, show ρ (b : G) v = v from hv b]

end CFSG.Quasithin.ChapterB.FittingStructure.MinimalPlanes
