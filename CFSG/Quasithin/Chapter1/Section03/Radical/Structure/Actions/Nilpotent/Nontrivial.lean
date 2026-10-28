module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Nilpotent.Quotient
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Nontriviality of the nilpotent component omega action

Every odd prime dividing the nilpotent radical in A.3.6(4) gives a nontrivial
actual conjugation action on Ω₁(Oₚ(C))/Φ(Ω₁(Oₚ(C))). Perfectness kills the
p-group automorphism kernels, first on the Frattini quotient and then on Ω₁
of an abelian core. Thus trivial quotient action would make Oₚ(C) central.

Put F = F(C) and N = F ∩ Oₚ'(C). The prime-core decomposition of F gives
F ≤ Oₚ(C)N. Hence C/N would be a perfect central extension of C/F whose
kernel has order divisible by p. But C/F is isomorphic to SL₂(5), and its
odd Sylow subgroups are cyclic: its order is 120. The transfer obstruction
for perfect central covers rules this out.

The stronger perfect-group statement records the inputs actually used.
The source wrapper retains the SQTK, two-core and full common hypotheses;
C-component perfectness and the nilpotent alternative suffice here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(4)
and its proof, printed pp.43–45, especially the argument labelled (*).
The SL₂ order calculation uses `Atlas.card_sl_two`, whose original ATLAS
attribution and license are recorded in `Theory.AtlasPort.LinearGroups.SL2Order`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent

section Perfect

variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
variable {p : ℕ} [Fact p.Prime]

private theorem hom_eq_one_of_range_le_pgroup {H : Type*} [Group H]
    (f : K →* H) (N : Subgroup H) (hN : IsPGroup p N) (hf : f.range ≤ N) :
    f = 1 := by
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsNilpotent f.range := (hN.to_le hf).isNilpotent
  have hs : Subsingleton f.range := by
    by_contra h
    let : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isNilpotent f.range inferInstance
  ext x
  exact congrArg Subtype.val (hs.elim (f.rangeRestrict x) 1)

private theorem omega_action_eq_one (h : omegaFrattiniAction p K = 1) :
    omegaCoreAction p K = 1 := by
  apply hom_eq_one_of_range_le_pgroup (omegaCoreAction p K)
    (quotientAut (frattini (omegaCore p K))).ker
    (isPGroup_quotientAut_frattini_kernel omega_isPGroup)
  rintro a ⟨x, rfl⟩
  exact DFunLike.congr_fun h x

private theorem core_central (hnil : A36Nilpotent K)
    (hd : p ∣ Nat.card (fittingSubgroup K)) (h : omegaFrattiniAction p K = 1) :
    pCore p K ≤ center K := by
  have hw := omega_action_eq_one h
  have hfix (g : K) (x : K) (hx : x ∈ omegaCore p K) : g * x * g⁻¹ = x :=
    congrArg (fun f : MulAut (omegaCore p K) => (f ⟨x, hx⟩ : K))
      (DFunLike.congr_fun hw g)
  rcases RadicalStructure.core_shape (Or.inr hnil) hd with ha | he
  · let := ha
    let ρ : K →* MulAut (pCore p K) :=
      (MulAut.characteristic (pCore p K)).comp MulAut.conj
    have hρ : ρ = 1 := by
      apply hom_eq_one_of_range_le_pgroup ρ (OmegaAction.omegaRestriction (pCore p K) p 1).ker
        (OmegaAction.restriction_kernel_isPGroup pCore_isPGroup)
      rintro a ⟨g, rfl⟩
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact hfix g x.val ⟨x.val, x.property, rfl⟩
    intro x hx
    apply mem_center_iff.mpr
    intro g
    have heq : g * x * g⁻¹ = x :=
      congrArg (fun f : MulAut (pCore p K) => (f ⟨x, hx⟩ : K)) (DFunLike.congr_fun hρ g)
    exact mul_inv_eq_iff_eq_mul.mp heq
  · have hW : omegaCore p K = pCore p K := by
      unfold omegaCore
      rw [RadicalStructure.omega_top he, ← MonoidHom.range_eq_map, range_subtype]
    intro x hx
    apply mem_center_iff.mpr
    intro g
    exact mul_inv_eq_iff_eq_mul.mp (hfix g x (hW.symm ▸ hx))

private theorem odd_sylow_cyclic {J : Type*} [Group J] [Finite J]
    (hc : Nat.card J = 120) (ho : Odd p) (P : Sylow p J) : IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  by_cases h0 : n = 0
  · simp [h0]
  have hpn : p ^ n ∣ 120 := by
    rw [← hc, ← hn]
    exact card_subgroup_dvd_card _
  have hp120 : p ∣ 120 := (dvd_pow_self p h0).trans hpn
  have hcases : p = 2 ∨ p = 3 ∨ p = 5 := by
    have hm := Nat.mem_primeFactors.mpr ⟨Fact.out (p := p.Prime), hp120, by decide⟩
    have hprimes : (120 : ℕ).primeFactors = {2, 3, 5} := by
      change (2 ^ 3 * 3 * 5 : ℕ).primeFactors = _
      rw [Nat.primeFactors_mul (by decide) (by decide),
        Nat.primeFactors_mul (by decide) (by decide),
        Nat.primeFactors_prime_pow (by decide) Nat.prime_two]
      norm_num [Nat.prime_three, Nat.prime_five]
    rw [hprimes] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hnot : ¬ p ^ 2 ∣ 120 := by
    rcases hcases with rfl | rfl | rfl
    · norm_num at ho
    · norm_num
    · norm_num
  have hnle : n ≤ 1 := by
    by_contra h
    exact hnot ((pow_dvd_pow p (show 2 ≤ n by omega)).trans hpn)
  simpa only [pow_one] using pow_dvd_pow p hnle

private theorem central_core_impossible (hc : Nat.card (K ⧸ fittingSubgroup K) = 120)
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K))
    (hcentral : pCore p K ≤ center K) : False := by
  let F := fittingSubgroup K
  let N := F ⊓ pPrimeCore p K
  have hNF : N ≤ F := inf_le_left
  have hNcop : Nat.Coprime p (Nat.card N) :=
    Nat.Coprime.of_dvd_right (card_dvd_of_le (show N ≤ pPrimeCore p K from inf_le_right))
      pPrimeCore_coprime_card
  have hsplit : F ≤ pCore p K ⊔ N := by
    dsimp [F]
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun r => ?_
    let : Fact r.val.val.Prime := ⟨Nat.prime_of_mem_primeFactors r.val.property⟩
    by_cases heq : r.val.val = p
    · rw [heq]
      exact le_sup_left
    · apply le_trans (show pCore r.val.val K ≤ N from ?_) le_sup_right
      apply le_inf (pCore_le_fitting K _)
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := r.val.val) (G := K)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes (Fact.out : p.Prime)
        (Fact.out : r.val.val.Prime)).mpr (fun hh => heq hh.symm)).pow_right n
  let q := QuotientGroup.mk' N
  let f : (K ⧸ N) →* (K ⧸ F) := QuotientGroup.lift N (QuotientGroup.mk' F)
    (by simpa only [QuotientGroup.ker_mk'] using hNF)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective F x
    exact ⟨q g, rfl⟩
  have hker : f.ker = F.map q := by
    dsimp [f]
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  have hkercentral : f.ker ≤ center (K ⧸ N) := by
    rw [hker]
    rintro x ⟨a, ha, rfl⟩
    obtain ⟨b, hb, c, hcN, rfl⟩ := mem_sup_of_normal_right.mp (hsplit ha)
    have hqc : q c = 1 := (QuotientGroup.eq_one_iff c).mpr hcN
    rw [map_mul, hqc, mul_one]
    apply mem_center_iff.mpr
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    change q g * q b = q b * q g
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hcentral hb) g]
  have hdker : p ∣ Nat.card f.ker := by
    have hcardN : Nat.card (N.subgroupOf F) = Nat.card N :=
      Nat.card_congr (subgroupOfEquivOfLe hNF).toEquiv
    have hrel : N.relIndex F = Nat.card (F.map q) := by
      simpa only [q, QuotientGroup.ker_mk'] using relIndex_ker F q
    have hmul := (N.subgroupOf F).card_mul_index
    change Nat.card (N.subgroupOf F) * N.relIndex F = Nat.card F at hmul
    rw [hcardN, hrel, ← hker] at hmul
    have hdiv : p ∣ Nat.card N * Nat.card f.ker := by rw [hmul]; exact hd
    exact ((Fact.out : p.Prime).dvd_mul.mp hdiv).resolve_left
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hNcop)
  exact PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow
    f hsurj hkercentral (odd_sylow_cyclic hc ho) hdker

/-- In the nilpotent alternative, perfection forces every relevant odd
omega–Frattini action to be nontrivial. -/
theorem omegaFrattiniAction_ne_one_of_perfect (hnil : A36Nilpotent K) (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup K)) : omegaFrattiniAction p K ≠ 1 := by
  intro ht
  have hc : Nat.card (K ⧸ fittingSubgroup K) = 120 := by
    have heq := Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hnil.1).toEquiv
    rw [← heq]
    obtain ⟨𝔽, _, _, h𝔽, ⟨e⟩⟩ := hnil.2.2.1
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, h𝔽]
    rfl
  exact central_core_impossible hc ho hd (core_central hnil hd ht)

end Perfect

universe u

/-- Nontriviality of the actual omega–Frattini action under the full A.3.6
nilpotent C-component hypotheses. -/
theorem omegaFrattiniAction_ne_one
    {E : Type u} [Group E] [Finite E] {𝒦 : GroupClass.{u}}
    (_hE : IsSQTK 𝒦 E) (_hO : pCore 2 E = ⊥)
    (C : Subgroup E) (hC : C.IsCComponent)
    (hnil : A36Nilpotent C) (_hcommon : A36Common C)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup C)) : omegaFrattiniAction p C ≠ 1 := by
  let : Group.IsPerfect C := hC.perfect
  exact omegaFrattiniAction_ne_one_of_perfect hnil ho hd

end CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent
