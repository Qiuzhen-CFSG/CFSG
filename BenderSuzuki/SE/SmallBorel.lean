module

public import BenderSuzuki.SE.Borel
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.SU3.EvenTwoRank

/-!
# Simple Bender groups with a small Borel

A Borel of order at most 48 forces the simple Bender model to be A5, and
then has order 12. Suzuki and unitary models have Sylow two-subgroups of
order at least 64. In the linear family, the Borel order q(q-1) forces q=4.
The exceptional isomorphism PSL2(4)=A5 supplies the actual group equivalence.

This is the model inspection in Aschbacher–Smith F.4.42 after I.8.5;
the proof uses the concrete root-group and Borel order formulas.
-/

noncomputable section
open Subgroup
open scoped MatrixGroups

namespace BenderSuzuki
open PFAppendixIII _root_.BenderSuzuki.MatrixGroups

private instance {F : Type*} [Field F] [Finite F] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem psl_binary_borel_card {F : Type*} [Field F] [Finite F] [CharP F 2]
    (B : Subgroup PSL(2,F)) (hB : IsBorelSubgroup B) :
    Nat.card B = Nat.card F * (Nat.card F - 1) := by
  obtain ⟨S, hS⟩ := hB.2
  rw [hS]
  change Nat.card (normalizer (S : Set PSL(2,F))) = _
  exact (Nat.card_congr
    (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F S).toEquiv).trans
    (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel F)

public theorem small_borel_alternating_five
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleBenderGroup G) (B : Subgroup G) (hB : IsBorelSubgroup B)
    (hsmall : Nat.card B ≤ 48) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) ∧ Nat.card B = 12 := by
  rcases hG with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixed, ⟨e⟩⟩⟩
  · have hBe := hB.map_mulEquiv e
    have hfield : Nat.card (BinaryGaloisField n) = 2 ^ n :=
      GaloisField.card 2 n (by omega)
    have hcard := psl_binary_borel_card (B.map e.toMonoidHom) hBe
    rw [card_map_of_injective e.injective, hfield] at hcard
    have hn2 : n = 2 := by
      by_contra hne
      have h8 : 8 ≤ 2 ^ n := by
        exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ n)
      have h7 : 7 ≤ 2 ^ n - 1 := by omega
      have h56 : 56 ≤ 2 ^ n * (2 ^ n - 1) := Nat.mul_le_mul h8 h7
      omega
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (hfield.trans (by rw [hn2]; norm_num))
    exact ⟨⟨e.trans a⟩, by simpa [hn2] using hcard⟩
  · exfalso
    obtain ⟨S, hS⟩ := (hB.map_mulEquiv e).2
    have hle : (S : Subgroup (SuzukiMatrixGroup m)) ≤ B.map e.toMonoidHom :=
      hS.symm ▸ (S : Subgroup (SuzukiMatrixGroup m)).le_normalizer
    have hbound := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    rw [card_map_of_injective e.injective,
      suzukiSylow_card (by omega) (MulEquiv.refl _) S] at hbound
    have h8 : 8 ≤ 2 ^ (2 * m + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ 2 * m + 1)
    nlinarith
  · exfalso
    let : Field E := hEfield
    let : Finite E := hEfinite
    obtain ⟨S, hS⟩ := (hB.map_mulEquiv e).2
    have hle : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
        B.map e.toMonoidHom :=
      hS.symm ▸ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).le_normalizer
    have hbound := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    have hcard : Nat.card S = (2 ^ n) ^ 3 := by
      rw [Nat.card_congr (Sylow.equiv S
        (HermitianForm.EvenTwoRank.rootSylow J hJ (by omega) hEcard hfixed)).toEquiv]
      exact HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card
        J hJ _ hEcard hfixed
    rw [card_map_of_injective e.injective, hcard] at hbound
    have h4 : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    have h64 : 64 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h4 3
    omega

end BenderSuzuki
