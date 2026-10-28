module

public import Theory.GroupTheory.PrimeRootsNormalComplement
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.PCoreCommutator
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.QuasithinBasic
public import Theory.Quasithin.Rank

/-!
# Two-core control from a normal rank-two odd section

In three-rank at most two, the centralizer of a normal subgroup of
three-rank two has a normal three-complement. Thus every two-subgroup
of that centralizer lies in the ambient three-complement core.

Apply this after factoring out O₂(G). If K is normal in G and K ≤ H,
then O₂(H) centralizes the image of K. When K/O₂(K) has three-rank two,
O₂(H) therefore lies in O₃′(G). A subgroup of O₂(H) normalized by
O₃′(G) consequently lies in O₂(G).

Source application: the equality branch Kc = K in Aschbacher--Smith
15.2.27(2), printed p.1119. This does not require the stronger equality
K = O^{3′}(G) asserted earlier in 15.2.12(4).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Two-subgroups centralizing a normal full-rank three-subgroup lie in O₃′. -/
theorem two_subgroup_le_threePrimeCore_of_centralizes_normal_rank_two
    (E A : Subgroup G) [E.Normal] (hr : primeRank 3 G ≤ 2)
    (hE : primeRank 3 E = 2) (hA : IsPGroup 2 A)
    (hc : A ≤ centralizer (E : Set G)) : A ≤ pPrimeCore 3 G := by
  let C := centralizer (E : Set G)
  let q := QuotientGroup.mk' (pPrimeCore 3 C)
  have hp : IsPGroup 3 (C ⧸ pPrimeCore 3 C) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 3 C
      (centralizer_hasNormalPComplement_of_rank_two (by decide) E hr hE)
  intro x hx
  let y : C := ⟨x,hc hx⟩
  obtain ⟨n,hn⟩ := hA ⟨x,hx⟩
  obtain ⟨m,hm⟩ := hp (q y)
  have htwo : q y ^ (2 ^ n) = 1 := by
    rw [←map_pow]
    have hy : y ^ (2 ^ n) = 1 := by
      apply Subtype.ext
      simpa [y] using congrArg Subtype.val hn
    rw [hy,map_one]
  have ho : orderOf (q y) = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow n m)
    (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hm)
  have hy : y ∈ pPrimeCore 3 C :=
    (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp ho)
  exact pPrimeCore_map_subtype_le_pPrimeCore_of_normal 3 C ⟨y,hy,rfl⟩

/-- A local two-core centralizing a normal rank-two section lies in the ambient O₃′. -/
theorem twoCoreIn_le_threePrimeCore_of_normal_rank_two_section
    (K H : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (hr : primeRank 3 G ≤ 2) (hK : primeRank 3 (K ⧸ pCore 2 K) = 2) :
    H.pCoreIn 2 ≤ pPrimeCore 3 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let E := K.map q
  have hE : primeRank 3 E = 2 := by
    rw [←primeRank_equiv 3 (coreQuotientEquivImage 2 K)]
    exact hK
  have hc : (H.pCoreIn 2).map q ≤ centralizer (E : Set (G ⧸ pCore 2 G)) := by
    apply le_centralizer_iff.mp
    rw [←commutator_eq_bot_iff_le_centralizer,←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using commutator_pCoreIn_le_of_normal K H hKH
  have hm := two_subgroup_le_threePrimeCore_of_centralizes_normal_rank_two
    E ((H.pCoreIn 2).map q)
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G)
      pCore_isPGroup).trans hr) hE ((isPGroup_pCoreIn 2 H).map q) hc
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hp := map_le_iff_le_comap.mp hm
  rwa [pPrimeCore_comap_eq_of_surjective_coprime 3 q
    (QuotientGroup.mk'_surjective _) hcop] at hp

/-- The actual actor enters O₂(G) once O₃′(G) normalizes it. -/
theorem le_twoCore_of_normal_rank_two_section
    (K H V : Subgroup G) [K.Normal] (hKH : K ≤ H)
    (hr : primeRank 3 G ≤ 2) (hK : primeRank 3 (K ⧸ pCore 2 K) = 2)
    (hV : V ≤ H.pCoreIn 2) (hn : pPrimeCore 3 G ≤ normalizer (V : Set G)) :
    V ≤ pCore 2 G := by
  have hVO : V ≤ pPrimeCore 3 G :=
    hV.trans (twoCoreIn_le_threePrimeCore_of_normal_rank_two_section K H hKH hr hK)
  have hv := le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).to_le hV) hVO hn
  have hcore : (pPrimeCore 3 G).pCoreIn 2 ≤ pCore 2 G := by
    unfold pCoreIn
    rw [pCore_eq_comap_of_normal]
    exact map_comap_le _ _
  exact hv.trans hcore

end Theory.GroupTheory
