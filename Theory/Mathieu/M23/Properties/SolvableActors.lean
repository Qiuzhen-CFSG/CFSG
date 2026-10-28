module
public import Theory.Mathieu.M23.Properties.QuinticSylowOvergroups
public import Theory.Mathieu.M23.Properties.CubicInversion
public import Theory.SpecificGroups.Alternating.SevenCyclicSolvable
public import Theory.GroupTheory.Hall.Existence
public import Mathlib.Algebra.Group.PUnit

/-!
# Odd actors in solvable full-Sylow overgroups of M₂₃

A Hall {2,p}-subgroup containing a full Sylow two-subgroup has order 128p
for p = 5, 7, 11 or 23. The native quintic exclusion treats five. For the
other primes, the small odd-core theorem forces a nontrivial two-core,
so the native two-local coverage places the Hall subgroup in a heptad
or triple stabilizer. The actual heptad quotient onto A₇ contradicts its
solvable cyclic-actor bound. The triple stabilizer's point stabilizer has
order 1920 and index at most three, excluding the other primes.

Thus every odd subgroup of a solvable full-Sylow overgroup is a three-group.
Innerness of M₂₃ automorphisms transfers the result to the actual action,
requiring only a full inner Sylow. The Chapter6 consumer discharges the
previously explicit three-group premise for its original quotient action.

Source: Aschbacher--Smith A.3.15 and 5.1.13, printed pp.50--51,636--637,
refs/quasithin.pdf; GLS3 Table 5.3d for the native two-local stabilizers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M23SolvableActors
open M23Geometry M23Geometry.SylowTwoLocals

private theorem heptad_no_large_prime (P : Sylow 2 heptadStabilizer)
    (H : Subgroup heptadStabilizer) (hPH : (P : Subgroup _) ≤ H)
    (hs : Group.IsSolvable H) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hc : Nat.card H = 128 * p) : False := by
  let f := heptadAlternatingAction
  have hf : Function.Surjective f :=
    fun a => ⟨AlternatingSection.s a, heptadAlternatingAction_section a⟩
  have hkc : Nat.card f.ker = 16 := heptadAlternatingAction_ker ▸ heptadKernel_card
  have hkp : IsPGroup 2 f.ker := IsPGroup.of_card (hkc.trans (by decide : 16 = 2^4))
  have hkh : f.ker ≤ H := (hkp.le_sylow_of_normal P).trans hPH
  have hh := (f.ker.subgroupOf H).card_mul_index
  change Nat.card (f.ker.subgroupOf H) * f.ker.relIndex H = _ at hh
  rw [relIndex_ker,Nat.card_congr (subgroupOfEquivOfLe hkh).toEquiv,hkc,hc] at hh
  have hJ : Nat.card (H.map f) = 8 * p := by omega
  let J := H.map f
  let : Group.IsSolvable H := hs
  let : Group.IsSolvable J := Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := J) p (by rw [hJ]; exact dvd_mul_left p 8)
  let E : Subgroup (alternatingGroup (Fin 7)) := zpowers (x : alternatingGroup (Fin 7))
  have hE : Nat.card E = p := by rw [Nat.card_zpowers,Subgroup.orderOf_coe,hx]
  have hEJ : E ≤ J := zpowers_le.mpr x.property
  have ho : Odd (Nat.card E) := hE ▸ (hp.odd_of_ne_two (by omega))
  let Q := P.mapSurjective hf
  have hQJ : (Q : Subgroup _) ≤ J := map_mono hPH
  have he := Theory.SpecificGroups.Alternating.SevenCyclicSolvable.image_card_one_or_three
    (alternatingGroup (Fin 7)).subtype E J hEJ ho Q (map_mono hQJ)
  rw [card_map_of_injective Subtype.val_injective,hE] at he
  omega

private theorem triple_no_large_prime (H : Subgroup tripleStabilizer) {p : ℕ}
    (hp : p = 7 ∨ p = 11 ∨ p = 23) (hc : Nat.card H = 128*p) : False := by
  open TripleSolvable in
  obtain ⟨g,hg⟩ := exists_triple_transport
  let e : tripleStabilizer ≃* TripleSolvable.markedStabilizer :=
    MulAction.stabilizerEquivStabilizer hg.symm
  let D := H.map e.toMonoidHom
  have hD : Nat.card D = 128*p := (card_map_of_injective e.injective).trans hc
  open TripleSolvable in
  have hcK : Nat.card markedPointStabilizer = 1920 := by
    rw [←Nat.card_congr firstEquivMarkedPoint.toEquiv]
    exact m22PairStabilizer_card
  open TripleSolvable in
  have hi : markedPointStabilizer.index ≤ 3 := by
    rw [MulAction.index_stabilizer]
    have ho : MulAction.orbit markedStabilizer (9 : Fin 23) ⊆
        (markedTriple : Set (Fin 23)) := by
      intro x hx
      obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
      have hm : (9 : Fin 23) ∈ markedTriple := by simp [m22M23AugmentedBlock]
      have hg := Finset.smul_mem_smul_finset (a := g.val) hm
      rwa [show g.val • markedTriple = markedTriple from g.property] at hg
    have hh := Set.ncard_le_ncard ho
    have ht : markedTriple.card = 3 := by decide +kernel
    simpa only [Set.ncard_coe_finset,ht] using hh
  have hpos : 0 < TripleSolvable.markedPointStabilizer.index :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hd : p ∣ 1920 * TripleSolvable.markedPointStabilizer.index := by
    rw [←hcK,card_mul_index]
    exact (hD ▸ dvd_mul_left p 128).trans D.card_subgroup_dvd_card
  have hi' : TripleSolvable.markedPointStabilizer.index = 1 ∨
      TripleSolvable.markedPointStabilizer.index = 2 ∨
      TripleSolvable.markedPointStabilizer.index = 3 := by omega
  rcases hp with rfl | rfl | rfl <;> rcases hi' with hi' | hi' | hi' <;>
    rw [hi'] at hd <;> norm_num at hd

private theorem no_large_prime_two_prime_overgroup
    (S : Sylow 2 M23) (H : Subgroup M23) (hSH : (S : Subgroup M23) ≤ H)
    (hs : Group.IsSolvable H) {p : ℕ} (hp : p = 7 ∨ p = 11 ∨ p = 23)
    (hc : Nat.card H = 128*p) : False := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have htwo : pCore 2 H ≠ ⊥ := by
    have hpr (q : ℕ) (hq : q.Prime) (hd : q ∣ Nat.card H) : q = 2 ∨ q = p := by
      rw [hc,show 128 = 2^7 from rfl] at hd
      rcases hq.dvd_mul.mp hd with h2 | hp
      · exact .inl (Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two h2)
      · exact .inr ((Nat.prime_dvd_prime_iff_eq hq hprime).mp hp)
    let P : Sylow p H := default
    have hP : Nat.card P = p := by
      rw [Sylow.card_eq_multiplicity,hc]
      rcases hp with rfl | rfl | rfl <;> decide +kernel
    have hsmall : Nat.card (pCore p H) ≤ p^1 := by
      simpa only [hP,pow_one] using card_le_of_le
        ((pCore_isPGroup (p := p) (G := H)).le_sylow_of_normal P)
    apply twoCore_ne_bot_of_solvable_small_odd_core (p := p) (d := 1) (t := 7)
      (by rcases hp with rfl | rfl | rfl <;> decide) hs hpr hsmall (by rw [hc]; exact dvd_mul_right _ _)
    intro n hn
    interval_cases n <;> rcases hp with rfl | rfl | rfl <;> norm_num [Fin.prod_univ_succ]
  obtain ⟨N,hN,hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H htwo
  obtain ⟨i,⟨e⟩⟩ := sylow_maximal_twoLocal_coverage S N hN (hSH.trans hHN)
  let Q := (S.subtype (hSH.trans hHN)).mapSurjective (f := e.toMonoidHom) e.surjective
  let X := (H.subgroupOf N).map e.toMonoidHom
  have hQX : (Q : Subgroup _) ≤ X := map_mono (comap_mono hSH)
  have hX : Nat.card X = 128*p := by
    rw [card_map_of_injective e.injective,Nat.card_congr (subgroupOfEquivOfLe hHN).toEquiv,hc]
  let : Group.IsSolvable H := hs
  let : Group.IsSolvable (H.subgroupOf N) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hHN).toMonoidHom) (subgroupOfEquivOfLe hHN).injective
  have hsX : Group.IsSolvable X := Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupMap_surjective (H.subgroupOf N))
  fin_cases i
  · exact heptad_no_large_prime Q X hQX hsX hprime
      (by rcases hp with rfl | rfl | rfl <;> decide) hX
  · exact triple_no_large_prime X hp hX


private theorem two_prime_order (S : Sylow 2 M23) (H : Subgroup M23)
    (hSH : (S : Subgroup M23) ≤ H) {p : ℕ}
    (hp : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23) (hpd : p ∣ Nat.card H)
    (hpr : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p) :
    Nat.card H = 128*p := by
  let d := 10200960 / (128*p)
  have hf : 10200960 = (128*p)*d := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  have h2 : ¬ 2 ∣ d := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hp' : ¬ p ∣ d := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have hcop : Nat.Coprime (Nat.card H) d := by
    apply Nat.coprime_of_dvd
    intro q hq hd
    rcases hpr q hq hd with rfl | rfl
    · exact h2
    · exact hp'
  have hupper : Nat.card H ∣ 128*p := by
    have hh := H.card_subgroup_dvd_card
    rw [m23_order,hf] at hh
    exact hcop.dvd_of_dvd_mul_right hh
  have hS : Nat.card S = 128 := by
    rw [Sylow.card_eq_multiplicity,m23_order]
    decide +kernel
  have h128 : 128 ∣ Nat.card H := hS ▸ card_dvd_of_le hSH
  have hcop' : Nat.Coprime 128 p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  exact Nat.dvd_antisymm hupper (hcop'.mul_dvd_of_dvd_of_dvd h128 hpd)

/-- A solvable overgroup of a full native M₂₃ Sylow two-subgroup has no
prime divisors other than two and three. -/
theorem prime_dvd_card (S : Sylow 2 M23) (K : Subgroup M23)
    (hSK : (S : Subgroup M23) ≤ K) (hs : Group.IsSolvable K)
    (p : ℕ) (hp : p.Prime) (hpk : p ∣ Nat.card K) : p = 2 ∨ p = 3 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hlist := (m23_prime_dvd_order_iff p).mp (hpk.trans K.card_subgroup_dvd_card)
  rcases hlist with h | h | hbad
  · exact .inl h
  · exact .inr h
  exfalso
  let _ : MulDistribMulAction Unit K := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let P := S.subtype hSK
  let π : Set Nat.Primes := {q | q.val = 2 ∨ q.val = p}
  have hPπ : IsPiSubgroup π (P : Subgroup K) := by
    intro q hq
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    exact Or.inl (Nat.prime_eq_prime_of_dvd_pow q.property Nat.prime_two (hn ▸ hq))
  obtain ⟨U,hU,_,hPU⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (A := Unit) hs (by simp) π (P : Subgroup K) hPπ ⟨fun _ _ => Iff.rfl⟩
  let H := U.map K.subtype
  have hSH : (S : Subgroup M23) ≤ H := by
    have hh := map_mono (f := K.subtype) hPU
    simpa only [P,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSK] using hh
  have hHU : Nat.card H = Nat.card U := card_map_of_injective K.subtype_injective
  have hpr (q : ℕ) (hq : q.Prime) (hd : q ∣ Nat.card H) : q = 2 ∨ q = p :=
    hU.p_in_pi_of_p_dvd_card ⟨q,hq⟩ (hHU ▸ hd)
  have hpi : ¬ p ∣ U.index := fun hi =>
    hU.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hi (Or.inr rfl)
  have hpd : p ∣ Nat.card H := by
    rw [hHU]
    exact (hp.dvd_mul.mp (U.card_mul_index.symm ▸ hpk)).resolve_right hpi
  have hc := two_prime_order S H hSH hbad hpd hpr
  rcases hbad with rfl | hbad
  · exact M23QuinticSylow.not_five_of_two_five_sylow_overgroup S H hSH 7 1
      (by rw [hc]; decide) hpd
  · let : Group.IsSolvable K := hs
    have hsH : Group.IsSolvable H := Group.isSolvable_of_surjective
      (K.subtype.subgroupMap_surjective U)
    exact no_large_prime_two_prime_overgroup S H hSH hsH hbad hc

/-- Every odd subgroup of a solvable full-Sylow overgroup is a three-group. -/
theorem odd_isPGroup (S : Sylow 2 M23) (K D : Subgroup M23)
    (hSK : (S : Subgroup M23) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (ho : Odd (Nat.card D)) : IsPGroup 3 D := by
  have he := Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := D)).ne' (by
    intro p hp hpd
    rcases prime_dvd_card S K hSK hs p hp (hpd.trans (card_dvd_of_le hDK)) with h | h
    · subst p
      exact (ho.not_two_dvd_nat hpd).elim
    · exact h)
  exact IsPGroup.of_card he

/-- The same prime restriction for the literal automorphism action. A full
inner Sylow suffices; cyclicity of the odd subgroup is not required. -/
theorem odd_aut_isPGroup (S : Sylow 2 M23) (J D : Subgroup (MulAut M23))
    (hSJ : (S : Subgroup M23).map MulAut.conj ≤ J)
    (hs : Group.IsSolvable J) (hDJ : D ≤ J) (ho : Odd (Nat.card D)) :
    IsPGroup 3 D := by
  let := hs
  let i : M23 →* MulAut M23 := MulAut.conj
  have hi : Function.Injective i := MulAut.conj_injective_of_center_eq_bot M23Geometry.m23_center_eq_bot
  let K := J.comap i
  let E := D.comap i
  have hEm : E.map i = D := map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr m23_conj_surjective]
    exact le_top)
  have hEc : Nat.card E = Nat.card D := by rw [←hEm,card_map_of_injective hi]
  have hsK : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap J) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  have hp := odd_isPGroup S K E (fun x hx => hSJ (mem_map_of_mem i hx)) hsK
    (comap_mono hDJ) (hEc ▸ ho)
  have hh := hp.map i
  rwa [hEm] at hh

end Sporadic.Mathieu.M23SolvableActors
