module

public import Theory.GroupAction.SylowCentralizer
public import BenderSuzuki.External.Huppert.XI.theorem_11_15
public import Glauberman.SuzukiCharacterization.RootTransitivity

/-!
# Suzuki recognition from the Sylow action

Centralizer containment makes the action on Sylow two-subgroups faithful
and makes the chosen Sylow subgroup act freely away from itself. If that
subgroup is also transitive away from itself, the ambient action is doubly
transitive and no nonidentity element fixes three points. A trivial odd
core excludes regular normal subgroups.

The Frobenius kernel of a point stabilizer has the same order as the chosen
Sylow subgroup. Normality then identifies this kernel with the Sylow
subgroup inside the stabilizer. Its noncommutativity selects Suzuki's
matrix-group recognition theorem directly.

The root-transitivity theorem supplies the geometric input from Suzuki,
*Finite groups with nilpotent centralizers* (1961), Theorem 1.5, p. 434,
as cited in Glauberman, *A Characterization of the Suzuki Groups* (1968),
Corollary 5.1, p. 92. The recognition endpoint is Huppert--Blackburn,
*Finite Groups III*, XI.11.15.
-/

namespace Glauberman.SuzukiCharacterization
open BenderSuzuki.External

/-- Root transitivity is sufficient for Suzuki recognition under the local
centralizer and nonabelian-Sylow hypotheses. -/
public theorem exists_suzuki_equiv_of_sylow_transitive
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcore : pPrimeCore 2 G = ⊥)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcomm : ¬ IsMulCommutative P)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (htrans : ∀ Q R : Sylow 2 G, Q ≠ P → R ≠ P →
      ∃ x : P, (x : G) • Q = R) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  classical
  have hfixed := P.at_most_two_fixed_of_centralizer_le_of_transitive hcent htrans
  let : Fintype (Sylow 2 G) := Fintype.ofFinite _
  let : FaithfulSMul G (Sylow 2 G) := ⟨by
    intro g h he
    apply P.toPermHom_injective_of_centralizer_le hn hcent
    exact Equiv.ext he⟩
  let H := MulAction.stabilizer G P
  let X := SubMulAction.ofStabilizer G P
  have hPH : (P : Subgroup G) ≤ H := by
    change (P : Subgroup G) ≤ MulAction.stabilizer G P
    rw [Sylow.stabilizer_eq_normalizer]
    exact Subgroup.le_normalizer
  let PS : Sylow 2 H := P.subtype hPH
  let e : PS ≃* P := Subgroup.subgroupOfEquivOfLe hPH
  have htwo : MulAction.IsMultiplyPretransitive G (Sylow 2 G) 2 := by
    apply (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := P)).mpr
    apply MulAction.is_one_pretransitive_iff.mpr
    refine ⟨fun Q R => ?_⟩
    obtain ⟨x, hx⟩ := htrans Q R Q.property R.property
    exact ⟨⟨x, hPH x.property⟩, Subtype.ext hx⟩
  obtain ⟨Q, hQ⟩ := P.exists_ne_of_not_normal hn
  let b : X := ⟨Q, hQ⟩
  let f : P → X := fun x => (⟨x, hPH x.property⟩ : H) • b
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hxy' : (x : G) • Q = (y : G) • Q := congrArg Subtype.val hxy
      have he : y⁻¹ * x = 1 :=
        P.eq_one_of_smul_eq_of_centralizer_le Q hcent hQ (y⁻¹ * x) (by
          change ((y : G)⁻¹ * (x : G)) • Q = Q
          rw [mul_smul, hxy', inv_smul_smul])
      exact (inv_mul_eq_one.mp he).symm
    · intro R
      obtain ⟨x, hx⟩ := htrans Q R hQ R.property
      exact ⟨x, Subtype.ext hx⟩
  have hPcard : Nat.card P = Nat.card X := Nat.card_congr (Equiv.ofBijective f hf)
  have hno := Sylow.no_regular_normal_of_pPrimeCore_eq_bot hcore
  obtain ⟨F, hFrob⟩ := huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
    htwo hfixed hno P Q hQ.symm
  obtain ⟨eF, _⟩ := huppert_blackburn_XI_pointStabilizer_exists_kernelPointEquiv
    htwo P Q hQ.symm F hFrob
  have hFcard : Nat.card F = Nat.card P := (Nat.card_congr eF).trans hPcard.symm
  obtain ⟨n, hncard⟩ := P.isPGroup'.exists_card_eq
  have hFtwo : IsPGroup 2 F := IsPGroup.of_card (hFcard.trans hncard)
  let : F.Normal := hFrob.normal
  have hFle : F ≤ (PS : Subgroup H) := hFtwo.le_sylow_of_normal PS
  have hFeq : F = (PS : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hFle (by rw [Nat.card_congr e.toEquiv, hFcard])
  have hFnoncomm : ¬ IsMulCommutative F := by
    intro hc
    have hcPS : IsMulCommutative PS := hFeq ▸ hc
    apply hcomm
    refine ⟨⟨fun x y => ?_⟩⟩
    apply e.symm.injective
    simpa only [map_mul] using hcPS.is_comm.comm (e.symm x) (e.symm y)
  exact huppert_XI_11_15_suzukiRecognition htwo hfixed hno P Q hQ.symm F hFrob
    hFnoncomm hFtwo

/-- An odd-core-free finite group with a nonnormal, nonabelian Sylow
two-subgroup containing the centralizer of each of its nonidentity elements
is a Suzuki matrix group. This is the recognition step in Corollary 5.1. -/
public theorem exists_suzuki_equiv_of_centralizer_le
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcore : pPrimeCore 2 G = ⊥)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcomm : ¬ IsMulCommutative P)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G)) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  exact exists_suzuki_equiv_of_sylow_transitive P hcore hn hcomm hcent
    (root_transitive_of_centralizer_le P hcore hn hcent)

end Glauberman.SuzukiCharacterization
