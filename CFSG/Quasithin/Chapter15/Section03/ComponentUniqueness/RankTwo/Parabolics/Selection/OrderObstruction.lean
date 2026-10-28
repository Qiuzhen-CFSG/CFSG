module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Definitions
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction

/-!
# The binary linear-three exclusion in the parabolic selection

The full Frattini shadow gives a quotient of order 36. The quotient of
the ambient group by its component is a two-group, so nine divides the
component order. Transporting an actual PSL₃(2) model to its binary
matrix carrier contradicts the checked determinant-kernel order bound.

The same Sylow supplement also gives the generalized-Fitting equality
of 15.3.41(1), without adding it as an extra input to `Setup`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41
and the first paragraph of the final proof of 15.3.35, pp.1138--1139.
Field transport uses the attributed ATLAS port
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection

variable {G : Type*} [Group G] [Finite G]
variable {L MI Y S : Subgroup G} [L.Normal]

/-- The simple component is all of F*(I/C_I(L)), using the actual Sylow supplement. -/
theorem Setup.generalizedFitting_eq (d : Setup L MI Y S) :
    generalizedFitting (CentralizerQuotient L) = centralizerQuotientComponent L := by
  let := d.quasisimple
  obtain ⟨P, hP⟩ := d.sylow
  have hs : IsPGroup 2 S := hP ▸ P.isPGroup'
  exact centralizerQuotient_generalizedFitting L
    (isPGroup_quotient_of_sup_eq_top L S hs d.generated)

private theorem nine_dvd_of_shadow {X : Type*} [Group X] [Finite X]
    (D Y T : Subgroup X) [D.Normal] (ht : IsPGroup 2 T)
    (hgen : D ⊔ T = ⊤) (hshadow : RankTwoShadow Y T) : 9 ∣ Nat.card D := by
  have h36 : 36 ∣ Nat.card X := by
    obtain ⟨e⟩ := hshadow
    have he : Nat.card ((Y ⊔ T : Subgroup X) ⧸ twoFrattiniCore (Y ⊔ T : Subgroup X)) = 36 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [← he]
    exact (card_quotient_dvd_card _).trans (card_subgroup_dvd_card _)
  obtain ⟨n, hn⟩ := (isPGroup_quotient_of_sup_eq_top D T ht hgen).exists_card_eq
  have hi : D.index = 2 ^ n := hn
  have h9 : 9 ∣ D.index * Nat.card D := by
    rw [D.index_mul_card]
    exact (by decide : 9 ∣ 36).trans h36
  rw [hi] at h9
  exact ((by decide : Nat.Coprime 9 2).pow_right n).dvd_mul_left.mp h9

/-- The rank-two shadow forces a factor of nine in the actual component image. -/
theorem Setup.nine_dvd_component (d : Setup L MI Y S) :
    9 ∣ Nat.card (centralizerQuotientComponent L) := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := d.sylow
  have ht : IsPGroup 2 (S.map q) := (hP ▸ P.isPGroup').map q
  apply nine_dvd_of_shadow D (Y.map q) (S.map q) ht _ d.quotient_local.shadow
  change L.map q ⊔ S.map q = ⊤
  rw [← Subgroup.map_sup, d.generated]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- The PSL₃(2) case is excluded using its concrete matrix carrier. -/
theorem Setup.not_linear_three_two (d : Setup L MI Y S)
    (hm : ClassicalGroup.IsPSL (centralizerQuotientComponent L) 3 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let a : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := e.trans (Atlas.fieldEquivPSL 3 a.symm)
  have h9 := d.nine_dvd_component
  rw [Nat.card_congr f.toEquiv] at h9
  exact (by decide : ¬ 9 ∣ 168) (h9.trans Matrix.PSL3Two.card_PSL_dvd)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
