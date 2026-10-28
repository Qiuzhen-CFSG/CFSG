module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed.NormalizerStructure

/-!
# Odd normalizers and distinguished centralizers

The distinguished closure `A = ⟨Z ∩ M⟩` is the elementary abelian group of
order `2^n` in the actual PSL₂ Borel. If an odd subgroup `Y ≤ M`
is normalized by a distinguished involution `s ∈ M`, then `[s,Y]` lies in
both `A` and `Y`, so it is trivial. Transport gives the same statement at
every literal coset stabilizer.

Consequently, when a distinguished involution normalizes but does not
centralize `Y`, the existing Section 5 normalizer theorem applies at its
unique fixed point. It gives rank at most one for the distinguished closure
inside `N_G(Y)` and conjugacy of its distinguished involutions. Normality
of `C_G(Y)` inside `N_G(Y)` then excludes distinguished involutions from
`C_G(Y)`, proving `C_G(Y)° = 1`. The normalizer closure contains the
specified involution, so the upper rank bound is the source rank-one case.

The actual consumer is (12F): every nonidentity element of the cyclic odd
torus `K` is inverted by `t`, and has trivial distinguished centralizer
closure. No torus fixed-point or regularity assertion is assumed here.

Source: GLS, Volume 4, Chapter 2, Lemma 12.12 and equation (12F) in the
proof of Proposition 12.13; `refs/KGroup/GLS4/Chapter2.tex`, lines 2275–2300.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- An odd subgroup in the base stabilizer commutes with every distinguished involution normalizing it. -/
public theorem Context.odd_normalizer_in_pointStabilizer_centralizes
    (Y : Subgroup G) (hodd : Odd (Nat.card Y)) (hYM : Y ≤ M)
    {s : G} (hsZ : s ∈ Z) (hsM : s ∈ M) (hsN : s ∈ normalizer (Y : Set G)) :
    s ∈ centralizer (Y : Set G) := by
  let A := closure (Z ∩ (M : Set G))
  have hsA : s ∈ A := subset_closure ⟨hsZ, hsM⟩
  have hdis : Disjoint Y A := disjoint_of_coprime_natCard (by
    rw [d.distinguished_elementary_card.2]
    exact hodd.coprime_two_right.pow_right _)
  rw [mem_centralizer_iff]
  intro y hy
  have hyN : y ∈ normalizer (A : Set G) := by
    rw [distinguishedClosure_normalizer d.minimal.disconnected]
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

omit [Finite G] d in
private theorem fixes_mk_iff (x b : G) :
    x • (QuotientGroup.mk b : G ⧸ M) = QuotientGroup.mk b ↔ b⁻¹ * x * b ∈ M := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  constructor
  · intro h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem h
  · intro h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem h

/-- The same odd-subgroup centralization statement at any literal fixed coset. -/
public theorem Context.odd_normalizer_at_fixedPoint_centralizes
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
    have hc := d.odd_normalizer_in_pointStabilizer_centralizes Q hQodd hQM
      (d.minimal.disconnected.invariant _ _ hsZ) hsM hsQ
    rw [mem_centralizer_iff] at hc ⊢
    intro y hy
    apply e.injective
    simpa only [map_mul] using hc (e y) (mem_map_of_mem e.toMonoidHom hy)

/-- Lemma 12.12: the normalizer has the rank-one, conjugacy and odd-core structure from Section 5. -/
public theorem Context.odd_normalizer_structure
    (Y : Subgroup G) (hodd : Odd (Nat.card Y))
    {s : G} (hsZ : s ∈ Z) (hsN : s ∈ normalizer (Y : Set G))
    (hsC : s ∉ centralizer (Y : Set G)) : SectionFiveNormalizerStructure Z Y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (d.reduction.one_class z d.z_mem s hsZ)
  have hzfix : z • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    change z ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rw [baseCoset_stabilizer]
    exact d.z_mem_M
  have hsfix : s • (g • (QuotientGroup.mk 1 : G ⧸ M)) =
      g • (QuotientGroup.mk 1 : G ⧸ M) := by
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hzfix]
  exact sectionFive_normalizerStructure_of_not_fixed d.minimal d.reduction Y hodd hsZ hsN
    hsfix (fun hY => hsC (d.odd_normalizer_at_fixedPoint_centralizes Y hodd hsZ hsN hsfix hY))

/-- Lemma 12.12: the distinguished closure of the odd subgroup centralizer is trivial. -/
public theorem Context.odd_centralizer_distinguishedClosure_eq_bot
    (Y : Subgroup G) (hodd : Odd (Nat.card Y))
    {s : G} (hsZ : s ∈ Z) (hsN : s ∈ normalizer (Y : Set G))
    (hsC : s ∉ centralizer (Y : Set G)) :
    closure (Z ∩ (centralizer (Y : Set G) : Set G)) = ⊥ := by
  have hstr := d.odd_normalizer_structure Y hodd hsZ hsN hsC
  apply le_antisymm _ bot_le
  apply (closure_le _).mpr
  rintro v ⟨hvZ, hvC⟩
  have hvN := centralizer_le_normalizer (Y : Set G) hvC
  obtain ⟨g, hg⟩ := hstr.one_class v hvZ hvN s hsZ hsN
  have hc := (inferInstance : ((centralizer (Y : Set G)).subgroupOf
    (normalizer (Y : Set G))).Normal).conj_mem ⟨v, hvN⟩ hvC g
  change (g : G) * v * (g : G)⁻¹ ∈ centralizer (Y : Set G) at hc
  exact (hsC (hg ▸ hc)).elim

/-- The source torus is the actual cyclic local pair stabilizer, of order `q - 1`, inverted by `t`. -/
public theorem Context.torus_structure :
    residualCommutator M t = residualPairStabilizer M t ⊓ residualGenerated M z t ∧
      IsCyclic (residualCommutator M t) ∧
      Nat.card (residualCommutator M t) = 2 ^ n - 1 ∧
      ∀ x ∈ residualCommutator M t, rightConjugateElem x t = x⁻¹ := by
  obtain ⟨hK, hcyc, hcard⟩ := d.normalizer_pair_structure.2.2
  exact ⟨hK, hcyc, hcard, fun x hx => psl2_local_pair_inverted
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper ⟨d.model⟩ (hK ▸ hx)⟩

/-- The source torus is normal relative to the actual pair stabilizer. -/
public theorem Context.pair_normalizes_torus :
    residualPairStabilizer M t ≤ normalizer (residualCommutator M t : Set G) := by
  rw [d.torus_structure.1]
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  exact and_congr
    (mem_normalizer_iff.mp ((residualPairStabilizer M t).le_normalizer ha) b)
    (mem_normalizer_iff.mp (d.pair_normalizes ha) b)

/-- The source split torus has odd order. -/
public theorem Context.torus_odd : Odd (Nat.card (residualCommutator M t)) := by
  rw [d.torus_structure.2.2.1]
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (even_two.pow_of_ne_zero (by have := d.parameter; omega : n ≠ 0)) odd_one

/-- A nonidentity odd-order element inverted by a distinguished involution has trivial distinguished centralizer closure. -/
public theorem Context.odd_inverted_centralizerClosure_eq_bot
    {x s : G} (hxne : x ≠ 1) (hodd : Odd (orderOf x))
    (hsZ : s ∈ Z) (hinv : s * x * s⁻¹ = x⁻¹) :
    centralizerClosure Z x = ⊥ := by
  have hs := d.minimal.disconnected.involutions s hsZ
  have hsN := theorem4b_mem_normalizer_zpowers_of_inverts hs hinv
  have hsC : s ∉ centralizer (zpowers x : Set G) := by
    intro hc
    have he := (mem_centralizer_iff.mp hc x (mem_zpowers x)).symm
    have hxx : x = x⁻¹ := by simpa only [he, mul_inv_cancel_right] using hinv
    have hsq : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (x * ·) hxx
        _ = 1 := mul_inv_cancel x
    have horder : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
      (dvd_refl _) (orderOf_dvd_of_pow_eq_one hsq)
    exact hxne (orderOf_eq_one_iff.mp horder)
  have hc := d.odd_centralizer_distinguishedClosure_eq_bot (zpowers x)
    (by rwa [Nat.card_zpowers]) hsZ hsN hsC
  simpa only [zpowers_eq_closure, Subgroup.centralizer_closure, centralizerClosure] using hc

/-- Equation (12F), for every nonidentity source torus element, without a prime-order restriction. -/
public theorem Context.torus_centralizerClosure_eq_bot
    {x : G} (hx : x ∈ residualCommutator M t) (hxne : x ≠ 1) :
    centralizerClosure Z x = ⊥ := by
  have hxi := d.torus_structure.2.2.2 x hx
  have ht := d.minimal.disconnected.involutions t d.t_mem
  apply d.odd_inverted_centralizerClosure_eq_bot hxne
    (d.torus_odd.of_dvd_nat ((residualCommutator M t).orderOf_dvd_natCard hx)) d.t_mem
  simpa only [rightConjugateElem, ht.inv_eq_self] using hxi

end BenderSuzuki.ZD.LinearExclusion
