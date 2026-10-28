module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.SourceData
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The earlier action input to Lemma 12.9

Let `A = ⟨Z ∩ M⟩`, `L = residualGenerated M z t`, and let `D` be the
actual two-point stabilizer. Lemma 12.2 supplies `A ≤ L`, `D ≤ N_G(L)`,
normality of `A` in `M`, and `Z ∩ M = A \ {1}`. The free `A`-orbit
through `tM` lies in the local Borel orbit. If its points together with `M`
exhausted the ambient action, correction by `A` would give `M = AD` and
`G = LD = N_G(L)`, contradicting simplicity and the properness of `L`.

The Section 3 conjugacy orbit identifies the source parameter with
`m = |A| - 1 = |K|`. For every prime dividing `m`, a Sylow subgroup of
`D` admits a distinguished swapping involution with inverted-set size `m_p`.
A third fixed coset would make it a Proposition 5.2 candidate. Enlarge to
a maximal candidate: its distinguished involution fixes a coset fixed by
the candidate subgroup. Normality and the two-power order of `A` force
this involution to centralize that odd subgroup. Its inverted set would
then have size one, contradicting `p ∣ m`. Thus the Sylow subgroup fixes
exactly two actual cosets, and the p-group orbit equation gives the desired
congruence for `|G/M|`.

All local structure comes from the proper residual model theorem. No later
centralizer count, field-action centralization, or ambient strong embedding
is assumed. The final theorem fills the exact arithmetic input consumed by
`proper_residualGenerated_centralizes_of_numerics` and the uniform cases.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Proposition 3.6, Proposition 5.2(a),
Corollary 7.12, Lemma 12.2(b,f), and the first case of Lemma 12.9.
-/

namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem degree_bound
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1}) :
    Nat.card (closure (Z ∩ (M : Set G))) + 1 < Nat.card (G ⧸ M) := by
  classical
  let A := closure (Z ∩ (M : Set G))
  let L := residualGenerated M z t
  let N := normalizer (L : Set G)
  let alpha : G ⧸ M := QuotientGroup.mk 1
  let beta : G ⧸ M := QuotientGroup.mk t
  have hAM : A ≤ M := (closure_le _).mpr (fun _ hx => hx.2)
  have htL : t ∈ L := (show zpowers t ≤ L from le_sup_right.trans le_sup_left) (mem_zpowers t)
  have hba : beta ≠ alpha := by
    intro he
    exact htM (by simpa [beta, alpha] using M.inv_mem (QuotientGroup.eq.mp he))
  have hfix (a : G) (ha : a ∈ M) : a • alpha = alpha := by
    exact MulAction.mem_stabilizer_iff.mp (by rwa [baseCoset_stabilizer])
  have hmove (a : G) (ha : a ∈ M) : a • beta ≠ alpha := by
    intro he
    exact hba (MulAction.injective a (he.trans (hfix a ha).symm))
  have hinj : Function.Injective (fun a : A => (a : G) • beta) := by
    intro a b he
    have hcA : (b : G)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem b.property) a.property
    have hc : (b : G)⁻¹ * a = 1 := by
      by_contra hc
      have hcz : (b : G)⁻¹ * a ∈ Z ∩ (M : Set G) := by
        rw [hZA]
        exact ⟨hcA, hc⟩
      apply hba
      apply action_fixedPoint_eq_base h hcz.1 hcz.2
      simp only [mul_smul, he, inv_smul_smul]
    exact Subtype.ext ((inv_mul_eq_one.mp hc).symm)
  let f : Option A → G ⧸ M := fun x => match x with
    | none => alpha
    | some a => (a : G) • beta
  have hf : Function.Injective f := by
    intro x y he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b => exact (hmove b (hAM b.property) he.symm).elim
    | some a =>
      cases y with
      | none => exact (hmove a (hAM a.property) he).elim
      | some b => exact congrArg some (hinj he)
  have hle : Nat.card A + 1 ≤ Nat.card (G ⧸ M) := by
    simpa only [Finite.card_option] using Nat.card_le_card_of_injective f hf
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hs : Function.Surjective f := ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, by simpa only [Finite.card_option] using heq⟩).2
  have hMN : M ≤ N := by
    intro m hm
    obtain ⟨a, ha⟩ := hs (m • beta)
    cases a with
    | none => exact (hmove m hm ha.symm).elim
    | some a =>
      have hd : (a : G)⁻¹ * m ∈ residualPairStabilizer M t := by
        have hdM : (a : G)⁻¹ * m ∈ M := M.mul_mem (M.inv_mem (hAM a.property)) hm
        have hdb : (a : G)⁻¹ * m ∈ MulAction.stabilizer G beta := by
          change ((a : G)⁻¹ * m) • beta = beta
          change (a : G) • beta = m • beta at ha
          rw [mul_smul, ← ha, inv_smul_smul]
        have hstab : MulAction.stabilizer G beta = rightConjugate M t := by
          rw [conjugateCoset_stabilizer, (h.involutions t ht).inv_eq_self]
        exact ⟨hdM, hstab ▸ hdb⟩
      have hh := N.mul_mem (L.le_normalizer (hAL a.property)) (hDN hd)
      simpa only [mul_inv_cancel_left] using hh
  have hNtop : N = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨a, ha⟩ := hs (g • alpha)
    cases a with
    | none =>
      exact hMN (by
        have hh : g ∈ MulAction.stabilizer G alpha := ha.symm
        rwa [baseCoset_stabilizer] at hh)
    | some a =>
      have halpha : ((a : G) * t) • alpha = g • alpha := by
        simpa only [f, beta, alpha, mul_smul, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using ha
      have hdM : ((a : G) * t)⁻¹ * g ∈ M := by
        have hh : ((a : G) * t)⁻¹ * g ∈ MulAction.stabilizer G alpha := by
          change (((a : G) * t)⁻¹ * g) • alpha = alpha
          rw [mul_smul, ← halpha, inv_smul_smul]
        rwa [baseCoset_stabilizer] at hh
      have hh := N.mul_mem (L.le_normalizer (L.mul_mem (hAL a.property) htL)) (hMN hdM)
      simpa only [mul_inv_cancel_left] using hh
  have hn : L.Normal := normalizer_eq_top_iff.mp hNtop
  rcases r.simple.eq_bot_or_eq_top_of_normal L hn with hb | hb
  · have hh : t ∈ (⊥ : Subgroup G) := hb ▸ htL
    exact (h.involutions t ht).ne_one (mem_bot.mp hh)
  · exact hL hb
end BenderSuzuki.ZD


namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem source_parameter (h : IsProductDisconnected Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1}) :
    theorem4bM M z = Nat.card (closure (Z ∩ (M : Set G))) - 1 := by
  let : MulAction M G := {
    smul a x := MulAut.conj (a : G) x
    one_smul x := by change (1 : G) * x * 1⁻¹ = x; simp
    mul_smul a b x := by
      change ((a : G) * (b : G)) * x * ((a : G) * (b : G))⁻¹ =
        (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
      group }
  have hstab : MulAction.stabilizer M z =
      (M ⊓ centralizer ({z} : Set G)).subgroupOf M := by
    ext a
    change MulAut.conj (a : G) z = z ↔ _
    simp only [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff,
      a.property, true_and]
    exact mul_inv_eq_iff_eq_mul
  have horbit : MulAction.orbit M z = Z ∩ (M : Set G) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨h.invariant _ _ hz, (h.conjugate_mem_iff z hz hzM a).mpr a.property⟩
    · rintro ⟨hx, hxM⟩
      exact productDisconnected_conjugator_mem h hz hzM hx hxM
  rw [theorem4bM, ← hstab, MulAction.index_stabilizer, horbit]
  change (Z ∩ (M : Set G)).ncard = (closure (Z ∩ (M : Set G)) : Set G).ncard - 1
  conv_lhs => rw [hZA]
  exact Set.ncard_sdiff_singleton_of_mem (one_mem _)

omit [Finite G] in
private theorem odd_normalizer_base (h : IsProductDisconnected Z M)
    {n : ℕ} (hAc : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (Y : Subgroup G) (hodd : Odd (Nat.card Y)) (hYM : Y ≤ M)
    {s : G} (hsZ : s ∈ Z) (hsM : s ∈ M) (hsN : s ∈ normalizer (Y : Set G)) :
    s ∈ centralizer (Y : Set G) := by
  let A := closure (Z ∩ (M : Set G))
  have hsA : s ∈ A := subset_closure ⟨hsZ, hsM⟩
  have hdis : Disjoint Y A := disjoint_of_coprime_natCard (by
    rw [hAc]
    exact hodd.coprime_two_right.pow_right _)
  rw [mem_centralizer_iff]
  intro y hy
  have hyN : y ∈ normalizer (A : Set G) := by
    rw [distinguishedClosure_normalizer h]
    exact hYM hy
  have hcY : s * y * s⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((mem_normalizer_iff.mp hsN y).mp hy) (Y.inv_mem hy)
  have hcA : s * y * s⁻¹ * y⁻¹ ∈ A := by
    have hh := A.mul_mem hsA ((mem_normalizer_iff.mp hyN s⁻¹).mp (A.inv_mem hsA))
    simpa only [mul_assoc] using hh
  have hc : s * y * s⁻¹ * y⁻¹ = 1 := hdis.le_bot ⟨hcY, hcA⟩
  have he : s * y = y * s := by
    apply (mul_inv_eq_iff_eq_mul).mp
    exact (mul_inv_eq_iff_eq_mul).mp hc |>.trans (one_mul y)
  exact he.symm

omit [Finite G] in
private theorem fixes_mk_iff (x b : G) :
    x • (QuotientGroup.mk b : G ⧸ M) = QuotientGroup.mk b ↔ b⁻¹ * x * b ∈ M := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  constructor <;> intro h <;> simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem h

omit [Finite G] in
private theorem odd_normalizer_fixed (h : IsProductDisconnected Z M)
    {n : ℕ} (hAc : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (Y : Subgroup G) (hodd : Odd (Nat.card Y))
    {s : G} (hsZ : s ∈ Z) (hsN : s ∈ normalizer (Y : Set G))
    {beta : G ⧸ M} (hsBeta : s • beta = beta)
    (hYBeta : Y ≤ MulAction.stabilizer G beta) : s ∈ centralizer (Y : Set G) := by
  induction beta using Quotient.inductionOn with
  | h b =>
    let e := MulAut.conj b⁻¹
    let Q := Y.map e.toMonoidHom
    have hQodd : Odd (Nat.card Q) := by
      rw [card_map_of_injective e.injective]
      exact hodd
    have hQM : Q ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        (fixes_mk_iff x b).mp (hYBeta hx)
    have hsM : e s ∈ M := by
      simpa only [e, MulAut.conj_apply, inv_inv] using (fixes_mk_iff s b).mp hsBeta
    have hsQ : e s ∈ normalizer (Q : Set G) :=
      le_normalizer_map (H := Y) e.toMonoidHom (mem_map_of_mem e.toMonoidHom hsN)
    have hc := odd_normalizer_base h hAc Q hQodd hQM
      (h.invariant _ _ hsZ) hsM hsQ
    rw [mem_centralizer_iff] at hc ⊢
    intro y hy
    apply e.injective
    simpa only [map_mul] using hc (e y) (mem_map_of_mem e.toMonoidHom hy)

private theorem no_candidate (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {n : ℕ} (hAc : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {p : ℕ} (hp : p.Prime) (hpo : Odd p) (hm : 1 < theorem4bPrimeShare M z p)
    {P : Subgroup G} (hP : actionPrimeShareCandidate Z M z p P) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, _, hmax⟩ := Finite.exists_le_maximal hP
  obtain ⟨s, hsZ, hsN, hshare⟩ := hmax.1.2.2
  obtain ⟨g, hg⟩ := isConj_iff.mp (r.one_class z hz s hsZ)
  have hzfix : z • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 :=
    MulAction.mem_stabilizer_iff.mp (by simpa only [baseCoset_stabilizer] using hzM)
  have hsfix : s • (g • (QuotientGroup.mk 1 : G ⧸ M)) = g • QuotientGroup.mk 1 := by
    rw [← hg]
    simp only [mul_smul, inv_smul_smul, hzfix]
  have hQfix := actionPrimeShareMaximalFixes_of_sectionThree h r
    (actionSectionThree_of_productDisconnected h.disconnected) z hz hzM p hp hpo
    Q hmax s hsZ hsN _ hsfix
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hmax.1.1.exists_card_eq
    rw [hk]
    exact hpo.pow
  have hc := odd_normalizer_fixed h.disconnected hAc Q hQodd hsZ hsN hsfix hQfix
  have hone : theorem4bInvertedCard s Q = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨1, by simp⟩, ?_⟩
    intro x
    apply Subtype.ext
    have he := (mem_centralizer_iff.mp hc x x.property.1).symm
    have hxx : (x : G) = (x : G)⁻¹ := by
      simpa only [he, mul_inv_cancel_right] using x.property.2
    have hsq : (x : G) ^ 2 = 1 := by
      calc
        (x : G) ^ 2 = (x : G) * x := pow_two _
        _ = (x : G) * (x : G)⁻¹ := congrArg ((x : G) * ·) hxx
        _ = 1 := mul_inv_cancel _
    have hxo := hQodd.of_dvd_nat (Q.orderOf_dvd_natCard x.property.1)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hxo.coprime_two_right
      (dvd_refl _) (orderOf_dvd_of_pow_eq_one hsq))
  omega

private theorem pair_fixed_card (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {n : ℕ} (hAc : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    {p : ℕ} (hp : p.Prime) (hpo : Odd p) (hm : 1 < theorem4bPrimeShare M z p)
    {P : Subgroup G} (hP : theorem4bIsSylowSubgroupOf p P (residualPairStabilizer M t)) :
    Nat.card (theorem4bFixedPoints M P) = 2 := by
  have hD : residualPairStabilizer M t =
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
        MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M) := by
    rw [baseCoset_stabilizer, conjugateCoset_stabilizer,
      (h.disconnected.involutions t ht).inv_eq_self]
    rfl
  have hba : (QuotientGroup.mk t : G ⧸ M) ≠ QuotientGroup.mk 1 := by
    intro he
    exact htM (by simpa using M.inv_mem (QuotientGroup.eq.mp he))
  have hPD : P ≤ residualPairStabilizer M t := by
    obtain ⟨S, rfl⟩ := hP
    exact map_subtype_le _
  have hPp : IsPGroup p P := by
    obtain ⟨S, rfl⟩ := hP
    exact S.isPGroup'.map _
  have htwo := action_two_le_fixedPoints (hPD.trans inf_le_left)
    (hPD.trans (by rw [hD]; exact inf_le_right)) hba
  by_contra hne
  have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M P) := by omega
  have h3 := actionSectionThree_of_productDisconnected h.disconnected
  obtain ⟨s, hsZ, hsN, hsSwap⟩ := sectionFive_distinguished_sylow_swap h.disconnected h3
    hp hpo hba.symm (hD ▸ hP)
  have hshare := (h3.swapping_bound z hz hzM s hsZ (QuotientGroup.mk 1)
    (by rwa [hsSwap]) p hp hpo P hPp
    (by rwa [hsSwap, ← hD]) hsN).2 (by rwa [hsSwap, ← hD])
  exact no_candidate h r hAc hz hzM hp hpo hm ⟨hPp, hthree, s, hsZ, hsN, hshare⟩


private theorem prime_share_of_dvd (h : IsProductDisconnected Z M)
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M)
    {n : ℕ} (hn : 2 ≤ n)
    (hAc : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card (closure (Z ∩ (M : Set G))) - 1) :
    Odd p ∧ 1 < theorem4bPrimeShare M z p := by
  have hodd : Odd (Nat.card (closure (Z ∩ (M : Set G))) - 1) := by
    rw [hAc]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega : n ≠ 0)) odd_one
  refine ⟨hodd.of_dvd_nat hdvd, ?_⟩
  have hm := source_parameter h hz hzM hZA
  have hfour : 4 ≤ 2 ^ n := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hmne : theorem4bM M z ≠ 0 := by rw [hm, hAc]; omega
  have he : 1 ≤ (theorem4bM M z).factorization p :=
    (hp.dvd_iff_one_le_factorization hmne).mp (hm.symm ▸ hdvd)
  exact lt_of_lt_of_le hp.one_lt (by
    simpa only [theorem4bPrimeShare, pow_one] using Nat.pow_le_pow_right hp.pos he)

private theorem congruence_local (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {n : ℕ} (hn : 2 ≤ n)
    (hAc : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (hZA : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Nat.card (closure (Z ∩ (M : Set G))) - 1) :
    Nat.ModEq p (Nat.card (G ⧸ M)) 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpo, hm⟩ := prime_share_of_dvd h.disconnected hz hzM hn hAc hZA hp hdvd
  let S : Sylow p (residualPairStabilizer M t) := Classical.choice inferInstance
  let P := (S : Subgroup (residualPairStabilizer M t)).map (residualPairStabilizer M t).subtype
  have hP : theorem4bIsSylowSubgroupOf p P (residualPairStabilizer M t) := ⟨S, rfl⟩
  have hcard := pair_fixed_card h r hAc hz hzM ht htM hp hpo hm hP
  have hPp : IsPGroup p P := S.isPGroup'.map _
  have hmod := BenderSuzuki.IsPGroup.card_modEq_card_fixedPointsOfSubgroup
    (Omega := G ⧸ M) hPp
  exact hcard ▸ hmod


/-- The Section 3 parameter is the order of the actual residual torus,
which is one less than the order of the distinguished closure (12.2(f)). -/
public theorem proper_residualGenerated_action_parameter
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    theorem4bM M z = Nat.card (residualCommutator M t) ∧
      theorem4bM M z = Nat.card (closure (Z ∩ (M : Set G))) - 1 := by
  obtain ⟨n, _, _, _, _, _, _, _, _, hAc, hZA, _, _, _, _, _, _, _, _, hKc, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  have hm := source_parameter h.disconnected hz hzM hZA
  exact ⟨by rw [hm, hAc, hKc], hm⟩

/-- The free distinguished orbit in the local Borel has `|A|` points.
If it exhausted the complement of the base point, correction by `A` would
give `M = AD` and then `G = LD = N_G(L)`, contrary to simplicity. -/
public theorem proper_residualGenerated_degree_gt
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    Nat.card (closure (Z ∩ (M : Set G))) + 1 < Nat.card (G ⧸ M) := by
  obtain ⟨n, _, _, hAL, hDN, _, _, _, _, _, hZA, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  exact degree_bound h.disconnected r ht htM hL hAL hDN hZA

/-- The Corollary 7.12 consequence for every Sylow subgroup of the actual
pair stabilizer, when the prime divides `|A|-1 = m`. Its fixed points are
literal cosets in `G/M`; ambient strong embedding is not a premise. -/
public theorem proper_residualGenerated_pairSylow_fixedPoints_card
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (closure (Z ∩ (M : Set G))) - 1)
    {P : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P (residualPairStabilizer M t)) :
    Nat.card (theorem4bFixedPoints M P) = 2 := by
  obtain ⟨n, hn, _, _, _, _, _, _, _, hAc, hZA, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  obtain ⟨hpo, hm⟩ := prime_share_of_dvd h.disconnected hz hzM hn hAc hZA hp hdvd
  exact pair_fixed_card h r hAc hz hzM ht htM hp hpo hm hP

/-- The earlier ambient-action input used by Lemma 12.9. The local orbit
supplies the strict degree bound, and Corollary 7.12 on the literal pair
stabilizer supplies the prime congruence by the p-group orbit equation. -/
public theorem proper_residualGenerated_arithmeticInput
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ResidualCentralizerArithmeticInput Z M := by
  obtain ⟨n, hn, _, hAL, hDN, _, _, _, _, hAc, hZA, _⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  exact ⟨degree_bound h.disconnected r ht htM hL hAL hDN hZA,
    fun _ hp hdvd => congruence_local h r hn hAc hZA hz hzM ht htM hp hdvd⟩

end BenderSuzuki.ZD
