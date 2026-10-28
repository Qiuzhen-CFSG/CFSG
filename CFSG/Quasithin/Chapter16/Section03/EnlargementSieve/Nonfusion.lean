module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The odd-rank nonfusion argument

Distinct components commute. An element of order three in one component
cannot lie in another whose center is a two-group. An elementary subgroup
of three-rank at least two in the latter therefore extends by an independent
commuting element of order three. This contradicts quasithinness in the
actual involution centralizer.

Source: Aschbacher–Smith, 16.3.10, printed p.1181. The final specialization
keeps the two intrinsic model ranks and the conjugacy of t and tz in T_C
explicit. Their discharge is required for the numbered source theorem.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve
variable {G : Type*} [Group G] [Finite G] {t z : G} {K J L : Subgroup G}

/-- The three-rank obstruction uses an elementary subgroup and a commuting
independent element of order three, both inside the actual centralizer. -/
theorem incompatible_components (hqt : IsQuasithin G) (ht : orderOf t = 2)
    (hK : IsCentralizerComponent t K) (hJ : IsCentralizerComponent t J)
    (hne : K ≠ J) (hZ : center K = pCore 2 K)
    (hK3 : 2 ≤ primeRank 3 K) (hJ3 : 3 ∣ Nat.card J) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hc : ⁅J, K⁆ = ⊥ :=
    ComponentTransfer.IsComponentIn.commute_of_ne hJ hK hne.symm
  have hcomm : J ≤ centralizer (K : Set G) := commutator_eq_bot_iff_le_centralizer.mp hc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hJ3
  have hxG : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  have hxK : (x : G) ∉ K := by
    intro hm
    have hz : (⟨x, hm⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (hcomm x.property a a.property)
    rw [hZ] at hz
    let y : pCore 2 K := ⟨⟨x, hm⟩, hz⟩
    have hy : orderOf y = 3 :=
      (orderOf_coe y).symm.trans ((orderOf_coe (⟨x, hm⟩ : K)).symm.trans hxG)
    have hy1 : y ≠ 1 := by intro he; simp [he] at hy
    have hd := (pCore_isPGroup (p := 2) (G := K)).dvd_orderOf hy1
    rw [hy] at hd
    norm_num at hd
  have hn : ¬ primeRank 3 K ≤ 1 := by omega
  rw [primeRank_le_iff_elementary_card_le K] at hn
  push Not at hn
  obtain ⟨E, hE, hEcard⟩ := hn
  let := hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have := Nat.pow_le_pow_right (n := 3) (by decide) hn1
    rw [← hn] at this
    omega
  let H := involutionCentralizer t
  let f : K →* H := inclusion hK.1
  let A := E.map f
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map f
  let xH : H := ⟨x, hJ.1 x.property⟩
  have hxH : orderOf xH = 3 := (orderOf_coe xH).symm.trans hxG
  have hxA : xH ∉ A := by
    rintro ⟨a, _, he⟩
    have he' : (a : G) = x := congrArg (fun u : H => (u : G)) he
    exact hxK (he' ▸ a.property)
  have hAc : A ≤ centralizer ({xH} : Set H) := by
    rintro a ⟨b, _, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (hcomm x.property b b.property)
  have hsize : Nat.card A = 3 ^ n := by
    rw [card_map_of_injective (inclusion_injective hK.1)]
    exact hn
  have hlower := IsElementaryAbelian.primeRank_ge_of_fixed_join A xH hxH hxA hAc hsize
  have hupper : primeRank 3 H ≤ 2 :=
    isQuasithin_iff_twoLocal.mp hqt H (isTwoLocal_involution_centralizer ht)
      3 (by decide) (by decide)
  omega

/-- A conjugate of L cannot coincide with its strict enlargement K; the
resulting distinct components violate the local odd-rank bound. -/
theorem not_conjugate_of_odd_rank (hqt : IsQuasithin G) (ht : orderOf t = 2)
    (hL : IsCentralizerComponent z L) (hK : IsCentralizerComponent t K)
    (hLK : L < K) (hZ : center K = pCore 2 K)
    (hK3 : 2 ≤ primeRank 3 K) (hL3 : 3 ∣ Nat.card L) : ¬ IsConj z t := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let e : G ≃* G := MulAut.conj g
  let J := L.map e.toMonoidHom
  have hj : IsCentralizerComponent t J := by
    have hh := (show Theory.GroupTheory.IsComponentIn L (involutionCentralizer z) from hL).map e
    have hez : e z = t := hg
    change Theory.GroupTheory.IsComponentIn J (involutionCentralizer t)
    simpa only [map_centralizer_equiv, Set.image_singleton, hez] using hh
  have hJcard : Nat.card J = Nat.card L := card_map_of_injective e.injective
  have hne : K ≠ J := by
    intro he
    apply hLK.ne
    exact eq_of_le_of_card_ge hLK.le (by rw [he, hJcard])
  exact incompatible_components hqt ht hK hj hne hZ hK3 (hJcard ▸ hL3)


/-- The complete nonfusion implication once the intrinsic odd-rank and
local-conjugacy witnesses have been supplied. No conjugacy exclusion is assumed. -/
theorem nonfusion_of_rank_and_local_conjugacy {𝒦 : GroupClass} {T : Sylow 2 G}
    (hG : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (balance : ComponentTransfer.OrdinaryBalanceAt (involutionCentralizer t) z)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hK3 : 2 ≤ primeRank 3 (enlargement t L)) (hL3 : 3 ∣ Nat.card L)
    (hfuse : IsConj t (t * z)) : ¬ IsConj z t ∧ ¬ IsConj z (t * z) := by
  have hn := not_conjugate_of_odd_rank hG.quasithin h.involution h.localSetup.component hK
    (enlargement_proper h balance)
    (hG.evenType.component_center_eq_twoCore h.involution hK) hK3 hL3
  exact ⟨hn, fun hc => hn (hc.trans hfuse.symm)⟩

end CFSG.Quasithin.Chapter16.EnlargementSieve
