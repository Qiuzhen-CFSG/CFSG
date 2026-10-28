module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Projective
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import CFSG.Quasithin.ClassicalModels

/-!
# Sylow-center and normalizer orders for PSU₃(2ⁿ)

Huppert II.10.12 gives a root group of order q³ with center of order q,
and its regular action away from its fixed point identifies the normalizer
with the isotropic-point stabilizer. Comparison with the existing Sylow
order proves that this root group is Sylow. Form transport and Sylow
conjugacy give the same center order and normalizer order bound for the
actual Sylow subgroup in any isomorphic source model.

The fixed-field parameter is q = 2^n; the matrix field has order q² and
conjugation is x ↦ x^q. The scalar quotient factor gcd(q+1,3) is retained
in Huppert's order and only removed by divisibility.
Source: Huppert II.10.12; Aschbacher–Smith E.6.8(1), E.6.11,
printed pp.247,249–250.
-/

public section

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open Subgroup
open scoped Matrix

namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions.UnitaryThree

/-- Every standard-model Sylow center has fixed-field order. -/
theorem standard_sylow_center_card
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (center S) = 2 ^ n := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨_, _, S₀, _, _, _, _, _, hS₀, _⟩ :=
    standard_psu_borel_data J n hn hcard hconj hstandard
  obtain ⟨_, _, _, _, _, _,
      ⟨R, _, _, _, _, _, _, _, hRcard, hcomm, hcommcard, _⟩, _⟩ :=
    huppert_II_10_12 J (2 ^ n) hcard (fixed_card J n hn hcard hconj) hstandard
  have hRp : IsPGroup 2 R := IsPGroup.of_card
    (show Nat.card R = 2 ^ (n * 3) by simpa only [pow_mul] using hRcard)
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hPeq : R = (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.eq_of_le_of_card_ge hRP (by
      rw [Nat.card_congr (P.equiv S₀).toEquiv, hS₀, hRcard])
  have hPcenter : Nat.card (center P) = 2 ^ n := by
    rw [← hPeq, ← hcomm]
    exact hcommcard
  exact (Nat.card_congr (centerCongr (S.equiv P)).toEquiv).trans hPcenter

/-- Transport the Sylow-center order through the actual PSU₃ model isomorphism. -/
theorem sylow_center_card
    {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ n)) (hn : 0 < n)
    (S : Sylow 2 H) : Nat.card (center S) = 2 ^ n := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e₀⟩⟩ := hmodel
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let e := e₀.trans (FormTransport.projectiveEquiv J C hC)
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hp := standard_sylow_center_card (FormTransport.standardForm J) n hn hcard hconj rfl P
  exact (Nat.card_congr (centerCongr (e.subgroupMap (S : Subgroup H))).toEquiv).trans hp

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions.UnitaryThree

open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.External
open CFSG.Quasithin.ChapterF.Source.Unitary
open Subgroup
open scoped Matrix

namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions.UnitaryThree

private theorem normalizer_card_eq
    {H : Type*} [Group H] [Finite H] (S P : Sylow 2 H) :
    Nat.card (normalizer ((S : Subgroup H) : Set H)) =
      Nat.card (normalizer ((P : Subgroup H) : Set H)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P S
  have hm : (P : Subgroup H).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • P : Sylow 2 H) : Subgroup H) = _
    rw [hg]
  change Nat.card (normalizer ((S : Subgroup H) : Set H)) = _
  rw [← hm, ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-- Huppert's stabilizer order bounds the actual standard-model Sylow normalizer. -/
theorem standard_sylow_normalizer_card_dvd
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Nat.card (normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∣
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  obtain ⟨_, _, S₀, _, _, _, _, _, hS₀, _⟩ :=
    standard_psu_borel_data J n hn hcard hconj hstandard
  obtain ⟨_, rho, pinf, _, _, hUcard,
      ⟨R, _, hRU, _, hUN, _, _, _, hRcard, _, _, _, hreg, _⟩, _⟩ :=
    huppert_II_10_12 J (2 ^ n) hcard (fixed_card J n hn hcard hconj) hstandard
  have hRp : IsPGroup 2 R := IsPGroup.of_card
    (show Nat.card R = 2 ^ (n * 3) by simpa only [pow_mul] using hRcard)
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hPeq : R = (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.eq_of_le_of_card_ge hRP (by
      rw [Nat.card_congr (P.equiv S₀).toEquiv, hS₀, hRcard])
  have hRne : R ≠ ⊥ := by
    intro he
    have hh : Nat.card R = 1 := by rw [he]; simp
    have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    have hc : 1 < (2 ^ n) ^ 3 := one_lt_pow₀ hq (by decide)
    omega
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
    MulAction.compHom (unitaryIsotropicPoints J) rho
  have hN := normalizer_eq_stabilizer_of_regular_compl R pinf hRU hRne hreg hUN
  rw [normalizer_card_eq S P]
  change Nat.card (normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∣ _
  rw [← hPeq, hN]
  change Nat.card ((MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J)) pinf).comap rho) ∣ _
  rw [hUcard]
  apply Nat.div_dvd_of_dvd
  have hfactor : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
  rw [hfactor]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _) _

/-- The normalizer order bound for any group isomorphic to PSU₃(2ⁿ). -/
theorem sylow_normalizer_card_dvd
    {H : Type*} [Group H] [Finite H] {n : ℕ}
    (hmodel : ClassicalGroup.IsPSU H 3 (2 ^ n)) (hn : 0 < n)
    (S : Sylow 2 H) : Nat.card (normalizer ((S : Subgroup H) : Set H)) ∣
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e₀⟩⟩ := hmodel
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let e := e₀.trans (FormTransport.projectiveEquiv J C hC)
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hp := standard_sylow_normalizer_card_dvd (FormTransport.standardForm J)
    n hn hcard hconj rfl P
  change Nat.card (normalizer (((S : Subgroup H).map e.toMonoidHom) :
    Set (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)))) ∣ _ at hp
  rwa [← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective e.injective] at hp

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions.UnitaryThree
