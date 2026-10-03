module
public import Theory.GroupTheory.ZStar.InductionHypothesis
public import Theory.GroupAction.NormalComplement

/-!
# Involution centralizers in the Z* induction

Under the exact smaller-group induction hypothesis, trivial ambient odd
core, and odd order of every commutator with a noncentral involution t,
every involution centralizer is proper.

If z is a central involution distinct from t, quotient by its order-two
subgroup. The image of t remains an involution and the group order strictly
decreases, so induction supplies a normal odd subgroup containing its
commutators. Its inverse image has the central order-two subgroup as a
Sylow subgroup. The generic Burnside transfer theorem in
`Theory.GroupAction.NormalComplement` gives a normal two-complement there.
Each odd commutator therefore lies in that inverse image's odd core,
which maps into the trivial ambient odd core. This makes t central,
a contradiction. The proper-centralizer theorem applies this argument
to an involution whose centralizer would be the whole group.

This is the central-involution step of Glauberman's Z* minimal-counterexample
argument, ported from the second half of
`c3503435:glauberman_zStar/Submission/ZStar/Induction.lean`.
-/

namespace Glauberman.ZStar
open Subgroup BenderSuzuki.PFAppendixIII
universe u

/-- A central involution in a core-free minimal counterexample forces the
distinguished involution to be central.  This is the induction step behind
the assertion that every involution centralizer is proper.

The proof passes to the quotient by the central involution.  The inverse
image of the odd normal subgroup supplied by induction has a central Sylow
`2`-subgroup of order two, hence has a normal `2`-complement by Burnside
transfer.  The odd commutators therefore lie in its odd core, which maps into
`O_{2'}(G)=1`. -/
public theorem central_of_induction_of_central_involution
    {G : Type u} [Group G] [Finite G]
    (hIH : OddOrderZStarInductionHypothesis G)
    (hcore : pPrimeCore 2 G = ⊥)
    (t : G) (htI : IsInvolution t)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (z : G) (hzI : IsInvolution z) (hzCentral : z ∈ Subgroup.center G) :
    t ∈ Subgroup.center G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hzt : z = t
  · simpa [hzt] using hzCentral
  let K : Subgroup G := Subgroup.zpowers z
  have hKcenter : K ≤ Subgroup.center G := by
    exact Subgroup.zpowers_le.mpr hzCentral
  have hKnormal : K.Normal := by
    constructor
    intro x hx g
    have hxCenter : x ∈ Subgroup.center G := hKcenter hx
    have hxComm : g * x = x * g := Subgroup.mem_center_iff.mp hxCenter g
    have hxConj : g * x * g⁻¹ = x := by rw [hxComm]; simp
    simpa [hxConj] using hx
  let : K.Normal := hKnormal
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hzOrder : orderOf z = 2 := orderOf_eq_prime hzI.2 hzI.1
  have hKcard : Nat.card K = 2 := by
    simp [K, Nat.card_zpowers, hzOrder]
  have hKneBot : K ≠ ⊥ := by
    intro hbot
    have hzBot : z ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers z
    exact hzI.1 (Subgroup.mem_bot.mp hzBot)
  have hqtI : IsInvolution (q t) := by
    constructor
    · intro hqtOne
      have htK : t ∈ K := by
        exact (QuotientGroup.eq_one_iff (N := K) (x := t)).mp hqtOne
      let tK : K := ⟨t, htK⟩
      let zK : K := ⟨z, Subgroup.mem_zpowers z⟩
      have htKne : tK ≠ 1 := by
        intro htOne
        apply htI.1
        exact congrArg Subtype.val htOne
      have hzKne : zK ≠ 1 := by
        intro hzOne
        apply hzI.1
        exact congrArg Subtype.val hzOne
      have heq : tK = zK :=
        ((Nat.card_eq_two_iff' (1 : K)).mp hKcard).unique htKne hzKne
      exact hzt (congrArg Subtype.val heq).symm
    · simpa [q, map_pow] using congrArg q htI.2
  have hQlt : Nat.card (G ⧸ K) < Nat.card G :=
    natCard_quotient_lt_natCard_of_ne_bot K hKneBot
  have hoddQ : ∀ x : G ⧸ K,
      Odd (orderOf (x * q t * x⁻¹ * (q t)⁻¹)) := by
    intro x
    rcases QuotientGroup.mk'_surjective K x with ⟨g, rfl⟩
    change Odd (orderOf (q g * q t * (q g)⁻¹ * (q t)⁻¹))
    have hdvd :
        orderOf (q (g * t * g⁻¹ * t⁻¹)) ∣
          orderOf (g * t * g⁻¹ * t⁻¹) :=
      orderOf_map_dvd q (g * t * g⁻¹ * t⁻¹)
    simpa [map_mul] using Odd.of_dvd_nat (hodd g) hdvd
  obtain ⟨M, hMnormal, hModd, hMcomm⟩ :=
    hIH (G ⧸ K) hQlt (q t) hqtI hoddQ
  let L : Subgroup G := M.comap q
  have hLnormal : L.Normal := hMnormal.comap q
  let : L.Normal := hLnormal
  have hker : q.ker = K := by
    simp [q]
  have hKleL : K ≤ L := by
    intro x hx
    change q x ∈ M
    have hxker : x ∈ q.ker := by simpa [hker] using hx
    rw [q.mem_ker.mp hxker]
    exact M.one_mem
  let KL : Subgroup L := K.subgroupOf L
  have hKLcard : Nat.card KL = 2 := by
    calc
      Nat.card KL = Nat.card K :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleL).toEquiv
      _ = 2 := hKcard
  have hKLp : IsPGroup 2 KL := by
    apply IsPGroup.of_card (n := 1)
    simp [hKLcard]
  have hquotCard : Nat.card (L ⧸ KL) = Nat.card M := by
    have hcard := card_quotient_subgroupOf_comap_eq
      (f := q) (hf := QuotientGroup.mk'_surjective K) (H := M)
    have hkernelSub : q.ker.subgroupOf L = KL := by
      rw [hker]
    simpa [L, KL, hkernelSub] using hcard
  have hKLindexOdd : Odd KL.index := by
    simpa [Subgroup.index_eq_card, hquotCard] using hModd
  have hKLindexNotDvd : ¬ 2 ∣ KL.index := by
    intro hdvd
    exact (Nat.not_even_iff_odd.mpr hKLindexOdd)
      (even_iff_two_dvd.mpr hdvd)
  let P : Sylow 2 L := IsPGroup.toSylow hKLp hKLindexNotDvd
  have hPcoe : (P : Subgroup L) = KL := by
    simp [P, IsPGroup.toSylow_coe]
  have hPcentralNormalizer :
      (P : Subgroup L) ≤
        centerIn (G := L) (Subgroup.normalizer (P : Subgroup L)) := by
    intro x hx
    have hxKL : x ∈ KL := by simpa [hPcoe] using hx
    have hxK : (x : G) ∈ K := hxKL
    have hxCenterG : (x : G) ∈ Subgroup.center G := hKcenter hxK
    refine ⟨le_normalizer hx, ?_⟩
    change x ∈ Subgroup.centralizer
      ((Subgroup.normalizer (P : Subgroup L) : Subgroup L) : Set L)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxCenterG (y : G)
  have hLcomp : HasNormalPComplement 2 L := by
    simpa [HasNormalPComplement] using
      (exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer
        (G := L) 2 P hPcentralNormalizer)
  have hLquotP : IsPGroup 2 (L ⧸ pPrimeCore 2 L) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := 2) (H := L) hLcomp
  have hcoreLmap : (pPrimeCore 2 L).map L.subtype ≤ pPrimeCore 2 G :=
    pPrimeCore_map_subtype_le_pPrimeCore_of_normal (G := G) (p := 2) L
  rw [hcore] at hcoreLmap
  rw [Subgroup.mem_center_iff]
  intro g
  let c : G := g * t * g⁻¹ * t⁻¹
  have hcL : c ∈ L := by
    change q c ∈ M
    simpa [c, map_mul] using hMcomm (q g)
  let cL : L := ⟨c, hcL⟩
  let qL : L →* L ⧸ pPrimeCore 2 L := QuotientGroup.mk' (pPrimeCore 2 L)
  have hqLcOdd : Odd (orderOf (qL cL)) := by
    apply Odd.of_dvd_nat (hodd g)
    have hmapDvd := orderOf_map_dvd qL cL
    simpa [cL, c] using hmapDvd
  have hqLcOne : qL cL = 1 := by
    by_contra hne
    have htwoDvd : 2 ∣ orderOf (qL cL) := hLquotP.dvd_orderOf hne
    exact (Nat.not_even_iff_odd.mpr hqLcOdd) (even_iff_two_dvd.mpr htwoDvd)
  have hcCoreL : cL ∈ pPrimeCore 2 L := by
    exact (QuotientGroup.eq_one_iff (N := pPrimeCore 2 L) (x := cL)).mp hqLcOne
  have hcMap : c ∈ (pPrimeCore 2 L).map L.subtype := by
    exact Subgroup.mem_map.mpr ⟨cL, hcCoreL, rfl⟩
  have hcBot : c ∈ (⊥ : Subgroup G) := hcoreLmap hcMap
  have hcOne : c = 1 := Subgroup.mem_bot.mp hcBot
  calc
    g * t = c * (t * g) := by dsimp [c]; group
    _ = t * g := by rw [hcOne, one_mul]

/-- In a core-free noncentral minimal counterexample, every involution has a
proper centralizer. -/
public theorem involutionCentralizer_ne_top_of_induction
    {G : Type u} [Group G] [Finite G]
    (hIH : OddOrderZStarInductionHypothesis G)
    (hcore : pPrimeCore 2 G = ⊥)
    (t : G) (htI : IsInvolution t)
    (htNotCentral : t ∉ Subgroup.center G)
    (hodd : ∀ g : G, Odd (orderOf (g * t * g⁻¹ * t⁻¹)))
    (z : G) (hzI : IsInvolution z) :
    Subgroup.centralizer ({z} : Set G) ≠ ⊤ := by
  intro htop
  have hzCentral : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({z} : Set G) := by rw [htop]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  exact htNotCentral
    (central_of_induction_of_central_involution
      hIH hcore t htI hodd z hzI hzCentral)

end Glauberman.ZStar
