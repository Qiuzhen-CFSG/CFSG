module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Inputs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Center.ActionImage
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.UnitaryAction.Center.Equiv
public import Theory.SpecificGroups.SU3.BorelTorus.EvenCenterAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.UnitaryThree.SylowOrders

/-!
# The PSU₃ Borel action on its Sylow center

Write q = 2ⁿ. In standard Hermitian coordinates the central root subgroup is
the additive fixed field inside the upper-right matrix entry. It lies in the
root group's center and has order q; the existing Sylow-center order theorem
therefore identifies it with the whole center. The root group is Sylow by its
order q³, and the computed normalizer is its join with the full diagonal torus.

The root group fixes its center pointwise. The torus acts by the inverse norm
from the matrix field of order q² to the fixed field of order q. Surjectivity
of that norm proves irreducibility and identifies the actual induced action
with the cyclic multiplicative fixed field, of order q−1. The projective
scalar kernel is retained in the matrix homomorphisms throughout.

Finally Sylow conjugacy, an actual Hermitian basis change, and the equivalence
stored in `ClassicalGroup.IsPSU` transport the calculation to the supplied
group and Sylow subgroup. No action conclusion is an input to the final theorem.

Source: Huppert II.10.12; Aschbacher–Smith, combined manuscript (1 March
2004), E.6.8(1), printed pp.247–248. This is the intrinsic center-action
calculation; the external V-action remains with the E.6 assembly.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction

/-- The intrinsic center action in standard Hermitian coordinates. The root
is identified with a Sylow subgroup by its order, and its central coordinate
with the whole Sylow center by inclusion and the source center order. -/
theorem standard_centerAction
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : CenterAction S n := by
  let : CharP E 2 := charP_two n hn hcard
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  have hfixed := fixed_card J n hn hcard hconj
  obtain ⟨_, _, S₀, _, _, _, _, _, hS₀, _⟩ :=
    standard_psu_borel_data J n hn hcard hconj hJ
  obtain ⟨_, _, _, _, _, hRcard, hsup, hnormal, _⟩ :=
    standard_projective_matrix_borel J n hn hcard hconj hJ
  let R := projectiveRoot J hJ
  have hRp : IsPGroup 2 R := IsPGroup.of_card
    (show Nat.card R = 2 ^ (n * 3) by simpa only [R, projectiveRoot, pow_mul] using hRcard)
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hPeq : R = (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.eq_of_le_of_card_ge hRP (by
      rw [Nat.card_congr (P.equiv S₀).toEquiv, hS₀]
      exact hRcard.ge)
  have hZ : sylowCenter P = EvenCenterAction.centralImage J hJ := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge
    · change EvenCenterAction.centralImage J hJ ≤
        (center (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map
          (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype
      rw [← hPeq]
      exact EvenCenterAction.centralImage_le_center J hJ
    · rw [EvenCenterAction.centralImage_card J hJ hfixed]
      change Nat.card ((center P).map (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype) ≤ 2 ^ n
      rw [Subgroup.card_map_of_injective (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype_injective,
        BorelActions.UnitaryThree.standard_sylow_center_card J n hn hcard hconj hJ P]
  have hN : normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      projectiveBorel J hJ := by
    change normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
    rw [← hPeq]
    exact hnormal.trans hsup.symm
  apply CenterAction.all_sylows P n ?_ S
  constructor
  · intro A hA hnA
    rw [hZ] at hA ⊢
    apply EvenCenterAction.central_irreducible J hJ hcard hfixed A hA
    apply le_trans (show projectiveTorus J hJ ≤ projectiveBorel J hJ from le_sup_right)
    rwa [hN] at hnA
  · rw [hZ, hN]
    obtain ⟨e⟩ := exists_inducedEquiv_of_torus
      (EvenCenterAction.centralImage J hJ) (projectiveRoot J hJ)
      (projectiveBorel J hJ) (hermitianTorusPSU J hJ) (EvenCenterAction.inverseNorm J)
      (EvenCenterAction.inverseNorm_surjective J hcard hfixed)
      (EvenCenterAction.borel_normalizes J hJ) rfl
      (EvenCenterAction.root_centralizes J hJ) (EvenCenterAction.torus_centralizer_iff J hJ)
    have hc : Nat.card (EvenCenterAction.fixedField J)ˣ = 2 ^ n - 1 := by
      rw [Nat.card_units]
      exact congrArg (fun m => m - 1) hfixed
    have ec := (zmodCyclicMulEquiv (G := (EvenCenterAction.fixedField J)ˣ) inferInstance).symm
    rw [hc] at ec
    exact ⟨e.trans ec⟩

/-- The Borel acts irreducibly on the actual PSU₃ Sylow center, with induced
cyclic group of order q−1. The stored model equivalence and a Hermitian basis
change carry the standard matrix calculation to the supplied group and Sylow. -/
theorem centerAction_of_isPSU
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ n)) (S : Sylow 2 H) : CenterAction S n := by
  obtain ⟨E, _, _, J, hcard, hconj, ⟨e₀⟩⟩ := hmodel
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n (by omega) hcard hconj
  let e := e₀.trans (FormTransport.projectiveEquiv J C hC)
  apply CenterAction.of_equiv S e n
  exact standard_centerAction (FormTransport.standardForm J) n (by omega) hcard hconj rfl _

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.UnitaryAction
