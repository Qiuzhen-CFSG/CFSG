module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage.Intransitive
public import Theory.Mathieu.M22.Properties.OuterCentralizers.SevenExclusion
public import Theory.Mathieu.M22.Properties.NoOrder15
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Mathlib.GroupTheory.Perm.Centralizer
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.TwoQuotient
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage

/-!
# The Cartan restriction for the actual M₂₂ automorphism groups

An abelian subgroup containing a seven-element cannot have order divisible
by eleven: it embeds in the permutation centralizer of cycle type 7³1.
Thus its permuting Sylow overgroup is intransitive on the natural 22 points.
The proved geometric coverage places this overgroup in a hexad or pair
stabilizer; neither stabilizer order is divisible by seven. The native
exclusion of elements of order fifteen removes the remaining exponent.

The genuine design-automorphism identification computes the outer quotient
as a group of order two. Normal-kernel transport therefore covers every
subgroup of the actual automorphism group containing the inner subgroup.

Source: Aschbacher--Smith, Definition E.3.37 and the M₂₂ row in Tables
7.2.1 and 7.3.4, printed pp.239 and 698--699.
-/

public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
open Subgroup MulAction
open scoped Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open Sporadic.Mathieu

private theorem not_eleven_of_abelian_seven (B : Subgroup M22)
    [IsMulCommutative B] (h7 : 7 ∣ Nat.card B) : ¬ 11 ∣ Nat.card B := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := B) 7 h7
  let p : Equiv.Perm (Fin 22) := x.val.val
  have hp : orderOf p = 7 := by
    simpa only [p, Subgroup.orderOf_coe] using hx
  have hfix : p.supportᶜ.card = 1 :=
    M22OuterCentralizers.seven_fixed_card x.val ((Subgroup.orderOf_coe x).trans hx)
  have hsupport : p.support.card = 21 := by
    have hc := Finset.card_compl p.support
    norm_num at hc
    omega
  obtain ⟨n, ht⟩ := Equiv.Perm.cycleType_prime_order (by rw [hp]; norm_num)
  have hn : n = 2 := by
    have hs := p.sum_cycleType
    rw [ht, Multiset.sum_replicate, hp, hsupport] at hs
    norm_num at hs
    omega
  have htype : p.cycleType = {7, 7, 7} := by rw [ht, hn, hp]; rfl
  have hcentral : Nat.card (centralizer ({p} : Set (Equiv.Perm (Fin 22)))) = 2058 := by
    rw [Equiv.Perm.nat_card_centralizer, htype]
    norm_num
  let f : B →* centralizer ({p} : Set (Equiv.Perm (Fin 22))) :=
    (M22.subtype.comp B.subtype).codRestrict _ (by
      intro b
      rw [mem_centralizer_singleton_iff]
      change b.val.val * x.val.val = x.val.val * b.val.val
      exact congrArg (fun a : B => a.val.val) (mul_comm b x))
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))
  have hd : Nat.card B ∣ 2058 := by
    simpa only [hcentral] using card_dvd_of_injective f hf
  exact fun h11 => (by norm_num : ¬ 11 ∣ 2058) (h11.trans hd)

private theorem sylow_card (S : Sylow 2 M22) : Nat.card S = 128 := by
  rw [Sylow.card_eq_multiplicity, m22_order]
  decide +kernel

private theorem pair_card {P : Finset (Fin 22)} (hP : P.card = 2) :
    Nat.card (stabilizer M22 P) = 1920 := by
  classical
  rcases Finset.card_eq_two.mp hP with ⟨x, y, hxy, rfl⟩
  obtain ⟨g, hg1, hg2⟩ := (is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    (by decide : (1 : Fin 22) ≠ 2) hxy
  have hg : g • m22Pair12 = ({x, y} : Finset (Fin 22)) := by
    rw [m22Pair12, Finset.smul_finset_insert, Finset.smul_finset_singleton, ← hg1, ← hg2]
  exact (Nat.card_congr (stabilizerEquivStabilizer hg.symm).toEquiv).symm.trans
    m22PairStabilizer_card

private theorem no_seven {c : ℕ} (w : NPrimeWitness M22 c) :
    ¬ 7 ∣ Nat.card w.abelianGroup := by
  intro h7
  let := w.abelian
  have h11 := not_eleven_of_abelian_seven w.abelianGroup h7
  let H := w.abelianGroup ⊔ (w.sylow : Subgroup M22)
  have hprod : Nat.card H * Nat.card (w.abelianGroup ⊓ (w.sylow : Subgroup M22) : Subgroup M22) =
      Nat.card w.abelianGroup * 128 := by
    have h := card_set_mul_mul_card_inf w.abelianGroup (w.sylow : Subgroup M22)
    rw [← coe_sup_of_set_mul_comm _ _ w.permutes, sylow_card] at h
    exact h
  have hnt : ¬ IsPretransitive H (Fin 22) := by
    intro ht
    let := ht
    have hd : 22 ∣ Nat.card H := by
      have hi := (stabilizer H (0 : Fin 22)).index_dvd_card
      rwa [index_stabilizer_of_transitive, Nat.card_fin] at hi
    have hd11 : 11 ∣ Nat.card w.abelianGroup * 128 := by
      rw [← hprod]
      exact dvd_mul_of_dvd_left ((by decide : 11 ∣ 22).trans hd) _
    exact h11 (((Nat.Prime.dvd_mul (by decide : Nat.Prime 11)).mp hd11).resolve_right
      (by norm_num))
  have h7H := h7.trans (card_dvd_of_le (show w.abelianGroup ≤ H from le_sup_left))
  rcases M22SolvableSylow.coverage_of_not_pretransitive H ⟨w.sylow, le_sup_right⟩ hnt with
    ⟨O, hO, hHO⟩ | ⟨P, hP, hHP⟩
  · have hd := h7H.trans (card_dvd_of_le hHO)
    rw [m22Hexad_stabilizer_card hO] at hd
    norm_num at hd
  · have hd := h7H.trans (card_dvd_of_le hHP)
    rw [pair_card hP] at hd
    norm_num at hd

theorem m22_nPrime_le_two : nPrime M22 ≤ 2 := by
  apply nPrime_le_iff.mpr
  intro c w
  have hcy : 2 ^ c - 1 ∣ 443520 := by
    rw [← w.card, ← m22_order]
    exact w.cyclicGroup.card_subgroup_dvd_card
  have hc : c < 19 := by
    by_contra h
    have hpow : 2 ^ 19 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    have hle := Nat.le_of_dvd (by norm_num : 0 < 443520) hcy
    norm_num at hpow
    omega
  have h7 := no_seven w
  have hno15 : Nat.card w.cyclicGroup ≠ 15 := by
    let := w.cyclic
    obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := w.cyclicGroup)
    exact fun h => m22_orderOf_ne_fifteen x.val ((Subgroup.orderOf_coe x).trans (hx.trans h))
  have h7cy := fun h : 7 ∣ 2 ^ c - 1 =>
    h7 ((show 7 ∣ Nat.card w.cyclicGroup by simpa only [w.card] using h).trans
      (card_dvd_of_le w.cyclic_le))
  have hcard := w.card
  interval_cases c <;> solve
    | omega
    | norm_num at hcy
    | norm_num at h7cy

private noncomputable def inclusion : M22 →* m22DesignAut := {
  toFun := fun g => ⟨g.val, M22_le_hexadDesignAut g.property⟩
  map_one' := rfl
  map_mul' := fun _ _ => rfl }

private theorem inclusion_conj (g : M22) :
    m22DesignAutToAut (inclusion g) = MulAut.conj g := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [m22DesignAutToAut_apply_perm]
  rfl

private theorem conjugation_injective :
    Function.Injective (MulAut.conj : M22 →* MulAut M22) := by
  intro x y h
  have hi : inclusion x = inclusion y := m22DesignAutToAut_injective (by
    rwa [inclusion_conj, inclusion_conj])
  exact Subtype.ext (congrArg (fun z : m22DesignAut => z.val) hi)

private theorem outer_two_group : IsPGroup 2 (MulAut.Outer M22) := by
  have hAut : Nat.card (MulAut M22) = 887040 :=
    (Nat.card_congr (MulEquiv.ofBijective m22DesignAutToAut
      ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩).toEquiv).symm.trans
        m22DesignAut_order
  have hInn : Nat.card (MulAut.innerSubgroup M22) = 443520 :=
    (Nat.card_congr (MonoidHom.ofInjective conjugation_injective).toEquiv).symm.trans m22_order
  have h := (MulAut.innerSubgroup M22).card_mul_index
  rw [hInn, hAut] at h
  have ho : Nat.card (MulAut.Outer M22) = (MulAut.innerSubgroup M22).index :=
    (index_eq_card (MulAut.innerSubgroup M22)).symm
  rw [← ho] at h
  exact IsPGroup.of_card (n := 1) (by change Nat.card (MulAut.Outer M22) = 2; omega)

theorem m22_aut_nPrime_le (A : Subgroup (MulAut M22))
    (hA : MulAut.innerSubgroup M22 ≤ A) : nPrime A ≤ nPrime M22 :=
  automorphism_subgroup_nPrime_le conjugation_injective outer_two_group A hA

/-- The literal inner-containing automorphism-group bound for M₂₂. -/
theorem m22_cartanRestriction (A : Subgroup (MulAut M22))
    (hA : MulAut.innerSubgroup M22 ≤ A) : nPrime A ≤ 2 :=
  (m22_aut_nPrime_le A hA).trans m22_nPrime_le_two

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
