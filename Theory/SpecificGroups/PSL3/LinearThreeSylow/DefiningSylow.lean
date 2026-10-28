module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.OddSolvableOvergroups
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
/-!
# Defining Sylow subgroups versus the upper Borel in PSL₃

The literal upper unitriangular subgroup has order p³ and prime-to-p index
over a field of prime order p. The Borel has index (p+1)(p²+p+1), which is
even for odd p. Sylow conjugacy and the solvable-overgroup calculation
therefore exclude a solvable subgroup containing both a subgroup of order
p³ and an ambient Sylow two-subgroup. All conjugations use the actual
projective matrix carrier.

Source: Aschbacher–Smith, A.3.15, printed pp.50–51, as used in
Proposition 1.3.4, printed pp.510–511.
-/

public section

open scoped MatrixGroups Pointwise
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace Matrix.PSL3.LinearThree.DefiningSylow
variable (F : Type*) [Field F] [Finite F]

theorem card_borelSL : Nat.card (borelSL F) = Nat.card F ^ 3 * (Nat.card F - 1)^2 := by
  have hc := (BorelQuotient.borelSL_complement F).card_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (unipotentSL_le_borelSL F)).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (BorelQuotient.torusSL_le_borel F)).toEquiv,
    ← Nat.card_congr (BorelQuotient.torusSLEquiv F).toEquiv,
    Nat.card_prod, Nat.card_units, card_unipotentSL, ← pow_two] at hc
  exact hc.symm

theorem card_specialLinear : Nat.card SL(3,F) =
    Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact card_projective_mul_scalar F

theorem index_borel : (borel F).index =
    (Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
  rw [borel, (borelSL F).index_map_eq (projection_surjective F)
    (projection_ker_le_borelSL F)]
  have hc := (borelSL F).card_mul_index
  rw [card_borelSL, card_specialLinear] at hc
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h2 : q^2 - 1 = (q-1)*(q+1) := by
    have hh : q-1+1=q := Nat.sub_add_cancel (by omega)
    have hs := Nat.sub_add_cancel (show 1 ≤ q^2 from Nat.one_le_pow _ _ (by omega))
    nlinarith [sq_nonneg (q-1)]
  have h3 : q^3 - 1 = (q-1)*(q^2+q+1) := by
    have hh := congrArg (fun n : ℕ => n*(q^2+q+1))
      (Nat.sub_add_cancel (show 1 ≤ q by omega))
    have hp : 1 ≤ q^3 := Nat.one_le_pow _ _ (by omega)
    have hs := Nat.sub_add_cancel hp
    nlinarith
  change q^3*(q-1)^2 * _ = q^3*(q^3-1)*(q^2-1) at hc
  rw [h2,h3] at hc
  have hqp : 0 < q := by omega
  have hqm : 0 < q-1 := by omega
  apply Nat.eq_of_mul_eq_mul_left (show 0 < q^3*(q-1)^2 by positivity)
  calc
    q^3*(q-1)^2 * (borelSL F).index = _ := hc
    _ = _ := by ring

theorem even_index_borel (ho : Odd (Nat.card F)) : 2 ∣ (borel F).index := by
  rw [index_borel]
  apply dvd_mul_of_dvd_left
  exact even_iff_two_dvd.mp (ho.add_odd odd_one)

theorem unipotent_prime (p : ℕ) (hF : Nat.card F = p) : IsPGroup p (unipotent F) := by
  apply IsPGroup.of_card (n := 3)
  rw [card_unipotent, hF]

theorem prime_not_dvd_index_unipotent {p : ℕ} (hp : p.Prime) (hF : Nat.card F = p) :
    ¬ p ∣ (unipotent F).index := by
  intro hd
  have hh := dvd_mul_of_dvd_left hd (Nat.gcd 3 (Nat.card F-1))
  rw [index_unipotent_mul_scalar, hF] at hh
  have hn (n : ℕ) (hn : n ≠ 0) : ¬ p ∣ p^n - 1 := by
    intro ht
    have hp' := pow_pos hp.pos n
    have hdiv := dvd_pow_self p hn
    have hsub := Nat.sub_add_cancel (show 1 ≤ p^n by omega)
    have hadd : p ∣ (p^n-1)+1 := by simpa only [hsub] using hdiv
    have : p ∣ 1 := (Nat.dvd_add_iff_left ht).mpr (by simpa only [add_comm] using hadd)
    exact hp.not_dvd_one this
  exact (hp.not_dvd_mul (hn 3 (by decide)) (hn 2 (by decide))) hh

noncomputable def primeSylow {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    Sylow p PSL(3,F) :=
  (unipotent_prime F p hF).toSylow (prime_not_dvd_index_unipotent F Fact.out hF)

/-- A solvable subgroup cannot contain both a full defining Sylow subgroup and
an ambient Sylow two-subgroup when the field has odd prime order. -/
theorem not_solvable_overgroup_of_card_cube {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (ho : Odd p) (hF : Nat.card F = p)
    (B H : Subgroup PSL(3,F)) (hB : IsPGroup p B) (hc : Nat.card B = p^3)
    (hBH : B ≤ H) [Group.IsSolvable H]
    (T : Sylow 2 PSL(3,F)) (hTH : (T : Subgroup PSL(3,F)) ≤ H) : False := by
  let P₀ := primeSylow F hF
  obtain ⟨P,hBP⟩ := hB.exists_le_sylow
  have hcardP : Nat.card (P : Subgroup PSL(3,F)) = p^3 := by
    rw [Nat.card_congr (P.equiv P₀).toEquiv]
    exact (card_unipotent F).trans (congrArg (fun n : ℕ => n^3) hF)
  have hPB : (P : Subgroup PSL(3,F)) = B :=
    (Subgroup.eq_of_le_of_card_ge hBP (by rw [hcardP,hc])).symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) P P₀
  have hmap : B.map (MulAut.conj g).toMonoidHom = unipotent F := by
    rw [← hPB]
    exact congrArg Sylow.toSubgroup hg
  let a := (MulAut.conj g).toMonoidHom
  let H' := H.map a
  let : Group.IsSolvable H' := Group.isSolvable_of_surjective (a.subgroupMap_surjective H)
  have hborel : H' ≤ borel F := OddSolvableOvergroups.solvable_le_borel F
    (by omega) H' (by rw [← hmap]; exact map_mono hBH)
  have ht : (T : Subgroup PSL(3,F)).map a ≤ borel F := (map_mono hTH).trans hborel
  apply T.not_dvd_index
  have hd := (even_index_borel F (hF ▸ ho)).trans (index_dvd_of_le ht)
  rw [Subgroup.index_map_of_bijective (f := a) (MulAut.conj g).bijective] at hd
  exact hd

end Matrix.PSL3.LinearThree.DefiningSylow
