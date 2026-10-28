module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.SylowLocalCentralizerCriterion
public import Theory.Mathieu.M22.Properties.EvenLocalGeometry
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry

/-!
# Even characteristic of the concrete Mathieu group M₂₂

Every involution fixes an actual hexad. Its pointwise kernel is a two-group
normal in the involution centralizer and self-centralizing in M₂₂. Thus
every involution centralizer has a self-centralizing intrinsic two-core.

For a two-local M containing a Sylow two-subgroup T, the nontrivial two-core
of M meets Z(T) in an involution z. The group C_M(z) contains the full
Sylow subgroup T of C_M₂₂(z), so inherits characteristic two. Since it
contains C_M(O₂(M)), the core-centralizer criterion proves characteristic
two in M. This covers every maximal two-local required by condition (E).

The conditional fixed-point reduction below also identifies the maximal
two-locals with pair or hexad stabilizers under its explicit geometric
premises. The unconditional even-characteristic theorem uses the
involution-centralizer argument.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed pp.3–4, repeated as
Theorem 0.1.1(5) on pp.481–482; the hexad geometry is 2.3.9(7)(f),
printed pp.525–526.
-/

namespace CFSG.Quasithin.MainConverse
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22ValueBound.Concrete
open Sporadic.Mathieu.M22EvenGeometry

private theorem maximalTwoLocal_eq_of_le_normalizing_twoGroup
    {G : Type*} [Group G] {M P Q : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hMP : M ≤ P)
    (hQ : Q ≠ ⊥) (hp : IsPGroup 2 Q) (hPN : P ≤ normalizer (Q : Set G)) :
    M = P :=
  le_antisymm hMP (hPN.trans (hM.2 ⟨Q, hQ, hp, rfl⟩ (hMP.trans hPN)))

/-- A fixed-point dichotomy gives exhaustive equality of maximal two-local
overgroups of the common Sylow with the pair or hexad stabilizer. -/
public theorem m22_maximalTwoLocal_eq_of_fixedPoints
    (hfixed : ∀ R : Subgroup sylow, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      commonFixedPoints (R.map (sylow : Subgroup M22).subtype) = m22Pair12 ∨
      commonFixedPoints (R.map (sylow : Subgroup M22).subtype) = m22Hexad123)
    {M : Subgroup M22} (hM : IsMaximalTwoLocal M)
    (hSM : (sylow : Subgroup M22) ≤ M) :
    M = first ∨ M = m22HexadStabilizer := by
  obtain ⟨R, hR, hn, he, hMR⟩ :=
    Theory.GroupTheory.exists_normal_elementary_normalizer_of_sylow_le sylow hM hSM
  have hle := normalizer_le_fixedPoints_stabilizer (R.map (sylow : Subgroup M22).subtype)
  rw [← hMR] at hle
  rcases hfixed R hR hn he with hpair | hhexad
  · have hMP : M ≤ first := by
      simpa only [hpair, first, m22PairStabilizer] using hle
    exact Or.inl (maximalTwoLocal_eq_of_le_normalizing_twoGroup hM hMP
      pairKernel_ne_bot pairKernel_isTwoGroup first_le_pairKernel_normalizer)
  · have hMP : M ≤ m22HexadStabilizer := by
      simpa only [hhexad, m22HexadStabilizer] using hle
    have hQ : m22HexadPointwiseKernel m22Hexad123 ≠ ⊥ := by
      intro hbot
      have hc := m22HexadPointwiseKernel_card m22Hexad123_mem
      rw [hbot, card_bot] at hc
      norm_num at hc
    have hPN : m22HexadStabilizer ≤
        normalizer (m22HexadPointwiseKernel m22Hexad123 : Set M22) := by
      rw [m22HexadPointwiseKernel_normalizer m22Hexad123_mem]
      exact le_rfl
    exact Or.inr (maximalTwoLocal_eq_of_le_normalizing_twoGroup hM hMP hQ
      (m22HexadPointwiseKernel_isTwoGroup m22Hexad123_mem) hPN)

/-- Conditional assembly from the finite Sylow fixed-point calculation and
the ambient centralizer bound for the actual pair kernel. -/
public theorem m22_evenCharacteristic_of_fixedPoints_and_pairKernel
    (hfixed : ∀ R : Subgroup sylow, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      commonFixedPoints (R.map (sylow : Subgroup M22).subtype) = m22Pair12 ∨
      commonFixedPoints (R.map (sylow : Subgroup M22).subtype) = m22Hexad123)
    (hpair : centralizer (pairKernel : Set M22) ≤ pairKernel) :
    IsEvenCharacteristic M22 := by
  apply IsEvenCharacteristicAt.all (T := sylow)
  intro M hM hSM
  rcases m22_maximalTwoLocal_eq_of_fixedPoints hfixed hM hSM with rfl | rfl
  · exact centralizer_pCore_le_of_normalized 2 pairKernel first pairKernel_isTwoGroup
      pairKernel_le first_le_pairKernel_normalizer hpair
  · exact m22Hexad_stabilizer_core_selfCentralizing m22Hexad123_mem

/-- Every involution centralizer in the actual M₂₂ has a self-centralizing
two-core, using the pointwise kernel of its fixed hexad. -/
public theorem m22_involutionCentralizer_characteristicTwo {u : M22}
    (hu : orderOf u = 2) :
    HasCharacteristicTwo (centralizer ({u} : Set M22)) := by
  have hB := m22FixedPoints_mem_blocks u hu
  apply centralizer_pCore_le_of_normalized 2
    (m22HexadPointwiseKernel (m22FixedPoints u)) (centralizer ({u} : Set M22))
    (m22HexadPointwiseKernel_isTwoGroup hB)
    (m22FixedPoints_kernel_le_centralizer u hu) ?_
    (m22HexadPointwiseKernel_selfCentralizing hB)
  rw [m22HexadPointwiseKernel_normalizer hB]
  exact m22_centralizer_le_fixedPoints_stabilizer u

/-- Every two-local containing a full Sylow two-subgroup of M₂₂ has its
intrinsic two-core self-centralizing. -/
public theorem m22_twoLocal_characteristicTwo (T : Sylow 2 M22) (M : Subgroup M22)
    (hM : IsTwoLocal M) (hTM : (T : Subgroup M22) ≤ M) :
    HasCharacteristicTwo M := by
  obtain ⟨Q, hne, hp, rfl⟩ := hM
  apply normalizer_core_selfCentralizing_of_sylow_centralizers T Q hp hne hTM
  intro z _ hz
  exact m22_involutionCentralizer_characteristicTwo ((orderOf_coe z).trans hz)

/-- Condition (E) of the quasithin classification for the concrete M₂₂. -/
public theorem m22_evenCharacteristic : IsEvenCharacteristic M22 := by
  intro T M hM hTM
  exact m22_twoLocal_characteristicTwo T M hM.1 hTM

end CFSG.Quasithin.MainConverse
