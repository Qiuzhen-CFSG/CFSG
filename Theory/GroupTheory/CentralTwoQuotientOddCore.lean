module
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.CentralLiftFromSylow
public import Mathlib.GroupTheory.Transfer

/-!
# Odd-core descent through a central 2-subgroup

For a finite group with trivial odd core, quotienting by a central 2-subgroup
again gives a group with trivial odd core. This supplies the elementary core
reduction used in ABG, Chapter II, Section 3, Proposition 1 (article page 22).

Pull back the quotient odd core to a normal subgroup `N`. The central kernel
is a Sylow 2-subgroup of `N`, since its index is odd. Burnside transfer gives
a normal odd complement. The odd core of `N` is characteristic in `N`, so its
image is a normal odd subgroup of the original group and hence trivial. The
complement is therefore trivial, forcing `N` to equal the quotient kernel.

The final theorem lifts centrality modulo odd cores through this central
quotient, provided the element already centralizes a Sylow two-subgroup.
In the odd-core quotient, the image of the central kernel remains a central
two-subgroup. Its quotient has trivial odd core by the first theorem, so the
original quotient odd core maps trivially there. The Sylow centrality-lifting
lemma then applies. This is also the lifting step of Lyons, A Characterization
of the Group U₃(4) (1972), Lemma 1, pp.372–373.
-/

open scoped commutatorElement
namespace Subgroup

/-- A central 2-quotient of a finite group with trivial odd core has trivial odd core. -/
public theorem pPrimeCore_quotient_eq_bot_of_central_two_subgroup
    {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hZtwo : IsPGroup 2 Z)
    (hcore : pPrimeCore 2 G = ⊥) : pPrimeCore 2 (G ⧸ Z) = ⊥ := by
  classical
  let A : Subgroup (G ⧸ Z) := pPrimeCore 2 (G ⧸ Z)
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  let N : Subgroup G := A.comap q
  have hZN : Z ≤ N := by
    intro x hx
    change q x ∈ A
    have : q x = 1 := (QuotientGroup.eq_one_iff (N := Z) x).2 hx
    simp [this]
  let qN : N →* A := (q.comp N.subtype).codRestrict A (by intro x; exact x.2)
  have hqN : Function.Surjective qN := by
    intro a
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (N := Z) (a : G ⧸ Z)
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change q g ∈ A
      simp [q, hg, a.property]
    · exact Subtype.ext hg
  have hker : qN.ker = Z.subgroupOf N := by
    ext x
    change qN x = 1 ↔ (x : G) ∈ Z
    rw [← Subtype.val_inj]
    change q (x : G) = 1 ↔ (x : G) ∈ Z
    exact QuotientGroup.eq_one_iff (N := Z) (x : G)
  have hcard : Nat.card (N ⧸ Z.subgroupOf N) = Nat.card A := by
    have h := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective qN hqN).toEquiv
    simpa [hker] using h
  have hZp : IsPGroup 2 (Z.subgroupOf N) :=
    hZtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hZN).symm
  have hindex : ¬ 2 ∣ (Z.subgroupOf N).index := by
    rw [Subgroup.index_eq_card, hcard]
    exact Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2))
  let P : Sylow 2 N := hZp.toSylow hindex
  have hcent : Subgroup.normalizer (P : Set N) ≤ Subgroup.centralizer (P : Set N) := by
    intro n _ z hz
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hZ hz) (n : G)).symm
  let K : Subgroup N := (MonoidHom.transferSylow P hcent).ker
  have hKcop : Nat.Coprime 2 (Nat.card K) :=
    Nat.prime_two.coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hcent)
  have hNcore : pPrimeCore 2 N = ⊥ := by
    have hmap : (pPrimeCore 2 N).map N.subtype = ⊥ := by
      apply pPrimeCore_eq_bot_iff.mp hcore
      · infer_instance
      · rw [Subgroup.card_map_of_injective N.subtype_injective]
        exact pPrimeCore_coprime_card
    exact Subgroup.map_injective N.subtype_injective (by simpa using hmap)
  have hK : K = ⊥ := pPrimeCore_eq_bot_iff.mp hNcore K inferInstance hKcop
  have hPtop : (P : Subgroup N) = ⊤ := by
    have h := (MonoidHom.ker_transferSylow_isComplement' P hcent).sup_eq_top
    change K ⊔ (P : Subgroup N) = ⊤ at h
    simpa [hK] using h
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (N := Z) a
  have hgN : g ∈ N := by change q g ∈ A; simpa [q, hg] using ha
  have hgZ : g ∈ Z := by
    have : (⟨g, hgN⟩ : N) ∈ (P : Subgroup N) := by rw [hPtop]; trivial
    exact this
  have : a = 1 := hg.symm.trans ((QuotientGroup.eq_one_iff (N := Z) g).2 hgZ)
  simp [this]

/-- Centrality modulo the odd core lifts through a central two-subgroup
when the element already centralizes a Sylow two-subgroup. -/
public theorem mem_center_mod_oddCore_of_central_two_quotient
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G) (hNp : IsPGroup 2 N)
    (S : Sylow 2 G) {x : G} (hx : x ∈ centralizer (S : Set G))
    (hbar : QuotientGroup.mk' (pPrimeCore 2 (G ⧸ N)) (QuotientGroup.mk' N x) ∈
      center ((G ⧸ N) ⧸ pPrimeCore 2 (G ⧸ N))) :
    QuotientGroup.mk' (pPrimeCore 2 G) x ∈ center (G ⧸ pPrimeCore 2 G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O := pPrimeCore 2 G
  let q : G →* G ⧸ O := QuotientGroup.mk' O
  let K := N.map q
  let : K.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective O)
  have hK : K ≤ center (G ⧸ O) := by
    rintro a ⟨n, hn, rfl⟩
    rw [mem_center_iff]
    intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O b
    exact (map_mul q g n).symm.trans ((congrArg q (mem_center_iff.mp (hN hn) g)).trans
      (map_mul q n g))
  have hKp : IsPGroup 2 K := hNp.map q
  have hcore : pPrimeCore 2 ((G ⧸ O) ⧸ K) = ⊥ :=
    pPrimeCore_quotient_eq_bot_of_central_two_subgroup K hK hKp
      (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))
  let r : G ⧸ O →* (G ⧸ O) ⧸ K := QuotientGroup.mk' K
  have hker : N ≤ (r.comp q).ker := by
    intro n hn
    exact (QuotientGroup.eq_one_iff (N := K) (q n)).mpr (mem_map_of_mem q hn)
  let f : G ⧸ N →* (G ⧸ O) ⧸ K := QuotientGroup.lift N (r.comp q) hker
  have hfq (g : G) : f (QuotientGroup.mk' N g) = r (q g) := rfl
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective K a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O b
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have hkill : (pPrimeCore 2 (G ⧸ N)).map f = ⊥ := by
    apply pPrimeCore_eq_bot_iff.mp hcore
    · exact Subgroup.Normal.map inferInstance f hf
    · exact Nat.Coprime.of_dvd_right (card_map_dvd _ f) (pPrimeCore_coprime_card (p := 2))
  apply mem_center_of_quotient_mem_center_of_centralizes_sylow K hK hKp
    (S.mapSurjective (f := q) (QuotientGroup.mk'_surjective O))
  · rw [mem_centralizer_iff]
    intro a ha
    change a ∈ (S : Subgroup G).map q at ha
    obtain ⟨s, hs, rfl⟩ := ha
    change q s * q x = q x * q s
    simpa only [← map_mul] using congrArg q (mem_centralizer_iff.mp hx s hs)
  · rw [mem_center_iff]
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective K a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O b
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hc : ⁅QuotientGroup.mk' N g, QuotientGroup.mk' N x⁆ ∈ pPrimeCore 2 (G ⧸ N) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pPrimeCore 2 (G ⧸ N))
        ⁅QuotientGroup.mk' N g, QuotientGroup.mk' N x⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_center_iff.mp hbar (QuotientGroup.mk' (pPrimeCore 2 (G ⧸ N))
          (QuotientGroup.mk' N g)))
    have hc' := mem_map_of_mem f hc
    rw [hkill, mem_bot] at hc'
    simpa only [map_commutatorElement, hfq] using hc'

end Subgroup
