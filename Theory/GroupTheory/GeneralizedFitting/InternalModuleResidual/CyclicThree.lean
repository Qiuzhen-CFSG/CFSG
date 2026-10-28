module

public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.NormalThreeHallCentralizer
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic

/-!
# The cyclic-three residual branch

The literal product `G = L T`, together with `L/O₂(L)` of order three,
forces the ambient Sylow two-subgroup to have index three.  The faithful
three-coset quotient then leaves only the orders three and six for the actual
quotient image.  The two-core hypothesis and the nontrivial commutator select
the order-three image, which is the normal Hall-three subgroup in the order-six
case and the whole group in the order-three case.
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

public section

open Subgroup
open Theory.GroupTheory
open scoped Pointwise

namespace Theory.GroupTheory

variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

private theorem sylow_index_eq_index_comap_of_factorization
    (L : Subgroup G) (T : Sylow 2 G)
    (hfac : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    (T : Subgroup G).index = ((T : Subgroup G).comap L.subtype).index := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction L (G ⧸ (T : Subgroup G)) :=
    MulAction.mulLeftCosetsCompSubtypeVal (T : Subgroup G) L
  have htrans : MulAction.IsPretransitive L (G ⧸ (T : Subgroup G)) := by
    apply (MulAction.isPretransitive_iff_base (G := L) (X := G ⧸ (T : Subgroup G))
      (Quotient.mk'' (1 : G))).2
    intro x
    induction x using Quotient.inductionOn' with | _ g =>
      obtain ⟨l, hl, t, ht, hlt⟩ := hfac g
      refine ⟨⟨l, hl⟩, ?_⟩
      change Quotient.mk'' (l * (1 : G)) = Quotient.mk'' g
      rw [mul_one, ← hlt]
      exact QuotientGroup.eq.mpr (by simpa using ht)
  letI : MulAction.IsPretransitive L (G ⧸ (T : Subgroup G)) := htrans
  have hstab : MulAction.stabilizer L ((Quotient.mk'' (1 : G)) : G ⧸ (T : Subgroup G)) =
      (T : Subgroup G).comap L.subtype := by
    ext l
    change (l : L) • ((Quotient.mk'' (1 : G)) : G ⧸ (T : Subgroup G)) =
      ((Quotient.mk'' (1 : G)) : G ⧸ (T : Subgroup G)) ↔ _
    change (Quotient.mk'' (((l : L) : G) * (1 : G)) : G ⧸ (T : Subgroup G)) =
      ((Quotient.mk'' (1 : G)) : G ⧸ (T : Subgroup G)) ↔ _
    rw [mul_one, QuotientGroup.eq]
    simp
    change ((l : L) : G) ∈ (T : Subgroup G) ↔ ((l : L) : G) ∈ (T : Subgroup G)
    rfl
  have hindex : (MulAction.stabilizer L ((Quotient.mk'' (1 : G)) : G ⧸ (T : Subgroup G))).index =
      Nat.card (G ⧸ (T : Subgroup G)) :=
    MulAction.index_stabilizer_of_transitive L _
  calc
    (T : Subgroup G).index = Nat.card (G ⧸ (T : Subgroup G)) := Subgroup.index_eq_card (T : Subgroup G)
    _ = (MulAction.stabilizer L ((Quotient.mk'' (1 : G)) : G ⧸ (T : Subgroup G))).index := hindex.symm
    _ = ((T : Subgroup G).comap L.subtype).index := congrArg Subgroup.index hstab

private theorem sylow_index_three_of_factorization_of_cyclic_three
    (L : Subgroup G) (T : Sylow 2 G)
    (hquot : Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hfac : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    T.index = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : T.index = ((T : Subgroup G).comap L.subtype).index :=
    sylow_index_eq_index_comap_of_factorization L T hfac
  have hnot2 : ¬ 2 ∣ ((T : Subgroup G).comap L.subtype).index := by
    intro hd
    exact T.not_dvd_index (hidx ▸ hd)
  have hPgroup : IsPGroup 2 ((T : Subgroup G).comap L.subtype) :=
    IsPGroup.comap_subtype T.isPGroup'
  let S : Sylow 2 L := hPgroup.toSylow hnot2
  have hquotcard : Nat.card (L ⧸ pCore 2 L) = 3 := by
    obtain ⟨e⟩ := hquot
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  have hPcoreidx : (pCore 2 L).index = 3 := by
    rw [Subgroup.index_eq_card]
    exact hquotcard
  have hSidx : (S : Subgroup L).index = (T : Subgroup G).index := by
    simp [S, hidx]
  have hle : pCore 2 L ≤ (S : Subgroup L) := pCore_isPGroup.le_sylow_of_normal S
  have hcases : (T : Subgroup G).index = 1 ∨ (T : Subgroup G).index = 3 := by
    have hm := Subgroup.relIndex_mul_index (H := pCore 2 L) (K := (S : Subgroup L)) hle
    rw [hPcoreidx, hSidx] at hm
    have hd : (T : Subgroup G).index ∣ 3 := ⟨(pCore 2 L).relIndex (S : Subgroup L), by
      simpa [Nat.mul_comm] using hm.symm⟩
    exact Nat.dvd_prime Nat.prime_three |>.mp hd
  rcases hcases with hone | hthree
  · have htop : (S : Subgroup L) = ⊤ := (Subgroup.index_eq_one.mp (by simp [hSidx, hone]))
    have hLleT : L ≤ (T : Subgroup G) := by
      intro l hl
      have hlS : (⟨l, hl⟩ : L) ∈ (S : Subgroup L) := by
        rw [htop]
        trivial
      exact hlS
    let f : L →* (T : Subgroup G) := Subgroup.inclusion hLleT
    have hLtwo : IsPGroup 2 L := T.isPGroup'.of_injective f (by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : (T : Subgroup G) => (z : G)) hab))
    have hqtwo : IsPGroup 2 (L ⧸ pCore 2 L) := hLtwo.to_quotient (pCore 2 L)
    have hbad := hqtwo.card_eq_or_dvd
    rw [hquotcard] at hbad
    omega
  · exact hthree

private theorem card_surjective_dvd {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) : Nat.card B ∣ Nat.card A := by
  have hi : f.ker.index = Nat.card B := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hm := f.ker.card_mul_index
  rw [hi] at hm
  exact ⟨Nat.card f.ker, by simpa [Nat.mul_comm] using hm.symm⟩

private theorem card_three_or_six_of_core_quotient
    (T : Sylow 2 G) (hidx : T.index = 3) :
    Nat.card (G ⧸ pCore 2 G) = 3 ∨ Nat.card (G ⧸ pCore 2 G) = 6 := by
  by_cases hEq : pCore 2 G = (T : Subgroup G)
  · left
    have hcardT : Nat.card (G ⧸ (T : Subgroup G)) = 3 :=
      (Subgroup.index_eq_card (T : Subgroup G)).symm.trans hidx
    simpa [hEq] using hcardT
  · right
    have hlt : pCore 2 G < (T : Subgroup G) := by
      apply lt_of_le_of_ne
      · exact pCore_isPGroup.le_sylow_of_normal T
      · exact hEq
    obtain ⟨e⟩ := sylow_index_three_core_quotient T hidx hlt
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem card_image_eq_three_of_core_free_index_three
    (V L : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G)
    (hquot : Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hfac : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    Nat.card (L.map q) = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup H := L.map q
  have hidx : T.index = 3 :=
    sylow_index_three_of_factorization_of_cyclic_three L T hquot hfac
  have hpcoreker : pCore 2 G ≤ q.ker := by
    have hmap : (pCore 2 G).map q ≤ pCore 2 H :=
      le_sSup ⟨Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
    rw [hcore] at hmap
    exact (Subgroup.map_eq_bot_iff (pCore 2 G)).mp (bot_unique hmap)
  have hqbar : Nat.card H ∣ Nat.card (G ⧸ pCore 2 G) := by
    let f : G ⧸ pCore 2 G →* H := QuotientGroup.lift (pCore 2 G) q hpcoreker
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := hq y
      exact ⟨QuotientGroup.mk' (pCore 2 G) x, rfl⟩
    exact card_surjective_dvd f hf
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply hcomm
    rw [commutator_eq_bot_iff_le_centralizer]
    have hLker : L ≤ q.ker := by
      intro x hx
      have hxK : q x ∈ K := ⟨x, hx, rfl⟩
      rw [hKbot] at hxK
      simp at hxK
      exact hxK
    apply le_centralizer_iff.mpr
    simp [hker] at hLker
    exact hLker
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  have hKpos : 1 < Nat.card K := Finite.one_lt_card
  have hKdvd : Nat.card K ∣ Nat.card H := Subgroup.card_subgroup_dvd_card K
  obtain hG3 | hG6 := card_three_or_six_of_core_quotient T hidx
  have hHcard : Nat.card H = 3 ∨ Nat.card H = 6 := by
    have hd : Nat.card H ∣ 3 := hG3 ▸ hqbar
    have hHne : Nat.card H ≠ 1 := by
      intro hh
      have hle : Nat.card K ≤ Nat.card H := Nat.le_of_dvd (by simp [hh]) hKdvd
      omega
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · omega
    · exact Or.inl h
  · rcases hHcard with hH3 | hH6
    · rcases (Nat.dvd_prime Nat.prime_three).mp (hH3 ▸ hKdvd) with h | h <;> omega
    · exfalso
      rw [hH6, hG3] at hqbar
      norm_num at hqbar
  have hHcard : Nat.card H = 3 ∨ Nat.card H = 6 := by
    have hd : Nat.card H ∣ 6 := hG6 ▸ hqbar
    have hHne : Nat.card H ≠ 1 := by
      intro hh
      have hle : Nat.card K ≤ Nat.card H := Nat.le_of_dvd (by simp [hh])
        (Subgroup.card_subgroup_dvd_card K)
      omega
    have hHnot2 : Nat.card H ≠ 2 := by
      intro hh
      have hHp : IsPGroup 2 H := IsPGroup.of_card (n := 1) (by simp [hh])
      have htop : (⊤ : Subgroup H) ≤ pCore 2 H :=
        le_sSup ⟨inferInstance, hHp.to_subgroup ⊤⟩
      have : (⊤ : Subgroup H) ≤ (⊥ : Subgroup H) := by simpa [hcore] using htop
      have hne : (⊤ : Subgroup H) ≠ (⊥ : Subgroup H) := by
        intro he
        apply hKne
        apply bot_unique
        rw [← he]
        exact le_top
      exact hne (bot_unique this)
    have hdle : Nat.card H ≤ 6 := Nat.le_of_dvd (by decide) hd
    interval_cases hc : Nat.card H <;> simp_all
  rcases hHcard with hH3 | hH6
  · have hKcard : Nat.card K = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (hH3 ▸ hKdvd) with h | h
      · omega
      · exact h
    change Nat.card K = 3
    exact hKcard
  · have hKcases : Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6 := by
      have hkdiv : Nat.card K ∣ 6 := by simpa [hH6] using hKdvd
      have hk_le : Nat.card K ≤ 6 := Nat.le_of_dvd (by decide) hkdiv
      interval_cases hk : Nat.card K <;> simp_all
    rcases hKcases with hK2 | hK3 | hK6
    · exfalso
      have hqTcard : Nat.card ((T : Subgroup G).map q) ≤ 2 := by
        have hdiv : Nat.card ((T : Subgroup G).map q) ∣ Nat.card H :=
          Subgroup.card_subgroup_dvd_card _
        have hpt : IsPGroup 2 ((T : Subgroup G).map q) := T.isPGroup'.map q
        obtain ⟨n, hn⟩ := hpt.exists_card_eq
        rw [hH6] at hdiv
        let N := Nat.card ((T : Subgroup G).map q)
        change N ∣ 6 at hdiv
        change N = 2 ^ n at hn
        have hle : N ≤ 6 := Nat.le_of_dvd (by decide) hdiv
        have hpos : 0 < N := by
          dsimp [N]
          exact Nat.card_pos
        have hnot3 : N ≠ 3 := by
          intro hc
          have hpow : (3 : ℕ) = 2 ^ n := by simpa [hc] using hn
          have hthree : (3 : ℕ) ∣ 2 ^ n := by rw [← hpow]
          have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hthree
          norm_num at this
        have hnot4 : N ≠ 4 := by
          intro hc
          have hd : (4 : ℕ) ∣ 6 := by simpa [hc] using hdiv
          norm_num at hd
        have hnot5 : N ≠ 5 := by
          intro hc
          have hd : (5 : ℕ) ∣ 6 := by simpa [hc] using hdiv
          norm_num at hd
        have hnot6 : N ≠ 6 := by
          intro hc
          have hpow : (6 : ℕ) = 2 ^ n := by simpa [hc] using hn
          have hthree : (3 : ℕ) ∣ 2 ^ n := by rw [← hpow]; norm_num
          have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hthree
          norm_num at this
        change N ≤ 2
        omega
      have hprod : ((K : Set H) * (((T : Subgroup G).map q : Subgroup H) : Set H)) = Set.univ := by
        ext y
        constructor
        · intro _
          trivial
        · intro _
          obtain ⟨g, rfl⟩ := hq y
          obtain ⟨l, hl, t, ht, hlt⟩ := hfac g
          refine ⟨q l, ⟨l, hl, rfl⟩, q t, ⟨t, ht, rfl⟩, ?_⟩
          calc
            q l * q t = q (l * t) := (q.map_mul l t).symm
            _ = q g := by rw [hlt]
      have hsurj : Function.Surjective (fun x : K × ((T : Subgroup G).map q) =>
          (x.1.1 * x.2.1 : H)) := by
        intro y
        have hy : y ∈ ((K : Set H) * (((T : Subgroup G).map q : Subgroup H) : Set H)) := by
          rw [hprod]
          trivial
        rcases hy with ⟨k, hk, t, ht, rfl⟩
        exact ⟨⟨⟨k, hk⟩, ⟨t, ht⟩⟩, rfl⟩
      have hcardle : Nat.card H ≤ Nat.card K * Nat.card ((T : Subgroup G).map q) := by
        rw [← Nat.card_prod]
        exact Nat.card_le_card_of_surjective _ hsurj
      rw [hH6, hK2] at hcardle
      omega
    · exact hK3
    · exfalso
      have hKtop : K = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (by simp [hH6, hK6])
      have hLsurj : Function.Surjective (q.comp L.subtype) := by
        intro y
        rcases (show y ∈ K from by simp [K, hKtop]) with ⟨x, hx, hxy⟩
        exact ⟨⟨x, hx⟩, hxy⟩
      have hnorm : ((pCore 2 L).map (q.comp L.subtype)).Normal := by
        exact Subgroup.Normal.map inferInstance (q.comp L.subtype) hLsurj
      have htwo : IsPGroup 2 ((pCore 2 L).map (q.comp L.subtype)) :=
        pCore_isPGroup.map _
      have hle : ((pCore 2 L).map (q.comp L.subtype)) ≤ pCore 2 H :=
        le_sSup ⟨hnorm, htwo⟩
      rw [hcore] at hle
      have hOmap : (pCore 2 L).map (q.comp L.subtype) = ⊥ :=
        bot_unique hle
      let f : L ⧸ pCore 2 L →* H :=
        QuotientGroup.lift (pCore 2 L) (q.comp L.subtype)
          ((Subgroup.map_eq_bot_iff (pCore 2 L)).mp hOmap)
      have hf : Function.Surjective f := by
        intro y
        obtain ⟨x, hx⟩ := hLsurj y
        exact ⟨QuotientGroup.mk' (pCore 2 L) x, hx⟩
      have hd : Nat.card H ∣ Nat.card (L ⧸ pCore 2 L) := card_surjective_dvd f hf
      have hLqcard : Nat.card (L ⧸ pCore 2 L) = 3 := by
        obtain ⟨e⟩ := hquot
        rw [Nat.card_congr e.toEquiv]
        simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
      rw [hH6, hLqcard] at hd
      omega

  
private theorem generalizedFitting_image_eq_of_card_three
    (K : Subgroup H) (hKcard : Nat.card K = 3)
    (hHcard : Nat.card H = 3 ∨ Nat.card H = 6)
    (hcore : pCore 2 H = ⊥) : K = generalizedFitting H := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hHcard with hH3 | hH6
  · have hKtop : K = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (by simp [hH3, hKcard])
    have hpcore : pCore 3 H = ⊤ := by
      apply top_unique
      exact le_sSup ⟨inferInstance, (IsPGroup.of_card (n := 1) (by simp [hH3])).to_subgroup ⊤⟩
    have hself : centralizer (pCore 3 H : Set H) ≤ pCore 3 H := by
      rw [hpcore]
      exact le_top
    have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 3 hself
    simpa [hKtop, hpcore] using hfit.symm
  · have hKidx : K.index = 2 := by
      have hm := K.card_mul_index
      rw [hKcard, hH6] at hm
      omega
    let : K.Normal := Subgroup.normal_of_index_eq_two hKidx
    have hsolv : Group.IsSolvable H := by
      apply isSolvable_of_prime_dvd_card_eq_two_or_three H
      intro p hp hd
      have hd6 : p ∣ 6 := by simpa [hH6] using hd
      have hp_le : p ≤ 6 := Nat.le_of_dvd (by decide) hd6
      interval_cases p <;> norm_num at hp <;> omega
    have hquot : IsPGroup 2 (H ⧸ K) := by
      apply IsPGroup.of_card (n := 1)
      calc
        Nat.card (H ⧸ K) = K.index := (Subgroup.index_eq_card K).symm
        _ = 2 := hKidx
        _ = 2 ^ 1 := by simp
    have hKthree : IsPGroup 3 K := IsPGroup.of_card (n := 1) (by simp [hKcard])
    have hself : centralizer (K : Set H) ≤ K :=
      Subgroup.centralizer_normal_three_le_of_two_quotient hsolv hcore K hKthree hquot
    have hKle : K ≤ pCore 3 H := le_sSup ⟨inferInstance, hKthree⟩
    have hFdiv : Nat.card (pCore 3 H) ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
    have hFdiv6 : Nat.card (pCore 3 H) ∣ 6 := by simpa [hH6] using hFdiv
    have hFle : Nat.card (pCore 3 H) ≤ 6 := Nat.le_of_dvd (by decide) hFdiv6
    have hFge : 3 ≤ Nat.card (pCore 3 H) := by
      let f : K → pCore 3 H := fun x => ⟨x, hKle x.property⟩
      have hf : Function.Injective f := by
        intro x y hxy
        exact Subtype.ext (congrArg (fun z : pCore 3 H => (z : H)) hxy)
      have hc := Nat.card_le_card_of_injective f hf
      simpa [hKcard] using hc
    have hpcore : pCore 3 H = K := by
      have heq : K = pCore 3 H := by
        have hFpg := pCore_isPGroup (p := 3) (G := H)
        rcases hFpg.exists_card_eq with ⟨n, hn⟩
        have hFthree : Nat.card (pCore 3 H) = 3 := by
          let N := Nat.card (pCore 3 H)
          have hnot4 : N ≠ 4 := by
            intro hc
            have hpow : (4 : ℕ) = 3 ^ n := by simpa [N, hc] using hn
            have htwo : (2 : ℕ) ∣ 3 ^ n := by rw [← hpow]; norm_num
            have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two htwo
            norm_num at this
          have hnot5 : N ≠ 5 := by
            intro hc
            have hpow : (5 : ℕ) = 3 ^ n := by simpa [N, hc] using hn
            have hfive : (5 : ℕ) ∣ 3 ^ n := by rw [← hpow]
            have : (5 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow (by decide) hfive
            norm_num at this
          have hnot6 : N ≠ 6 := by
            intro hc
            have hpow : (6 : ℕ) = 3 ^ n := by simpa [N, hc] using hn
            have htwo : (2 : ℕ) ∣ 3 ^ n := by rw [← hpow]; norm_num
            have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two htwo
            norm_num at this
          have hNge : 3 ≤ N := by simpa [N] using hFge
          have hNle : N ≤ 6 := by simpa [N] using hFle
          have : N = 3 := by omega
          simpa [N] using this
        have hcardle : Nat.card (pCore 3 H) ≤ Nat.card K := by
          rw [hFthree, hKcard]
        exact (Subgroup.eq_of_le_of_card_ge hKle hcardle)
      exact heq.symm
    have hself' : centralizer (pCore 3 H : Set H) ≤ pCore 3 H := by
      simpa [hpcore] using hself
    have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 3 hself'
    simpa [hpcore] using hfit.symm
theorem cyclic_three_image_structure
    (V L : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G)
    (hquot : Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hfac : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    (∃ P : Sylow 2 (centralizer (V : Set G)),
        (P : Subgroup (centralizer (V : Set G))).Normal) ∧
      L.map q = generalizedFitting H ∧ Nat.card (L.map q) = 3 := by
  let C : Subgroup G := centralizer (V : Set G)
  let : C.Normal := by
    change (centralizer (V : Set G)).Normal
    rw [← hker]
    infer_instance
  have hKcard : Nat.card (L.map q) = 3 :=
    card_image_eq_three_of_core_free_index_three V L q hq hker hcore T hquot hcomm hfac
  have hpcoreker : pCore 2 G ≤ q.ker := by
    have hmap : (pCore 2 G).map q ≤ pCore 2 H :=
      le_sSup ⟨Normal.map inferInstance q hq, pCore_isPGroup.map q⟩
    rw [hcore] at hmap
    exact (Subgroup.map_eq_bot_iff (pCore 2 G)).mp (bot_unique hmap)
  have hqbar : Nat.card H ∣ Nat.card (G ⧸ pCore 2 G) := by
    let f : G ⧸ pCore 2 G →* H := QuotientGroup.lift (pCore 2 G) q hpcoreker
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := hq y
      exact ⟨QuotientGroup.mk' (pCore 2 G) x, rfl⟩
    exact card_surjective_dvd f hf
  have hKdivH : 3 ∣ Nat.card H := by
    rw [← hKcard]
    exact Subgroup.card_subgroup_dvd_card (L.map q)
  have hGcard : Nat.card (G ⧸ pCore 2 G) = 3 ∨ Nat.card (G ⧸ pCore 2 G) = 6 :=
    card_three_or_six_of_core_quotient T (sylow_index_three_of_factorization_of_cyclic_three L T hquot hfac)
  have hHcard : Nat.card H = 3 ∨ Nat.card H = 6 := by
    rcases hGcard with hG3 | hG6
    · have hd : Nat.card H ∣ 3 := hG3 ▸ hqbar
      exact Or.inl (Nat.dvd_antisymm hd hKdivH)
    · have hd : Nat.card H ∣ 6 := hG6 ▸ hqbar
      have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by decide) hd
      interval_cases hc : Nat.card H <;> simp_all
  have hhsyl : ∃ P : Sylow 2 C, (P : Subgroup C).Normal := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    have hNidx : (pCore 2 G).index = Nat.card (G ⧸ pCore 2 G) :=
      Subgroup.index_eq_card _
    have hNmul := (pCore 2 G).card_mul_index
    rw [hNidx] at hNmul
    have hqidx : q.ker.index = Nat.card H := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv
    have hCmul := q.ker.card_mul_index
    rw [hqidx, hker] at hCmul
    change Nat.card C * Nat.card H = Nat.card G at hCmul
    have hCpow : ∃ m, Nat.card C = 2 ^ m := by
      rcases hGcard with hG3 | hG6 <;> rcases hHcard with hH3 | hH6
      · have heq : Nat.card C * 3 = Nat.card (pCore 2 G) * 3 := by
          calc
            Nat.card C * 3 = Nat.card G := by simpa [hH3] using hCmul
            _ = Nat.card (G ⧸ pCore 2 G) * Nat.card (pCore 2 G) := by
              simpa [Nat.mul_comm] using hNmul.symm
            _ = Nat.card (pCore 2 G) * 3 := by rw [hG3]; omega
        exact ⟨n, (Nat.mul_right_cancel (by norm_num) heq) ▸ hn⟩
      · exfalso
        have : Nat.card H ∣ Nat.card (G ⧸ pCore 2 G) := hqbar
        rw [hH6, hG3] at this
        omega
      · have heq : Nat.card C * 3 = Nat.card (pCore 2 G) * 6 := by
          calc
            Nat.card C * 3 = Nat.card G := by simp [hH3] at hCmul ⊢; exact hCmul
            _ = Nat.card (G ⧸ pCore 2 G) * Nat.card (pCore 2 G) := by
              simpa [Nat.mul_comm] using hNmul.symm
            _ = Nat.card (pCore 2 G) * 6 := by rw [hG6]; ring
        have hc : Nat.card C = Nat.card (pCore 2 G) * 2 := by omega
        exact ⟨n + 1, by rw [hc, hn, pow_succ]⟩
      · have heq : Nat.card C * 6 = Nat.card (pCore 2 G) * 6 := by
          calc
            Nat.card C * 6 = Nat.card G := by simp [hH6] at hCmul ⊢; exact hCmul
            _ = Nat.card (G ⧸ pCore 2 G) * Nat.card (pCore 2 G) := by
              simpa [Nat.mul_comm] using hNmul.symm
            _ = Nat.card (pCore 2 G) * 6 := by rw [hG6]; ring
        exact ⟨n, (Nat.mul_right_cancel (by norm_num) heq) ▸ hn⟩
    have hCcore : IsPGroup 2 C := by
      rcases hCpow with ⟨m, hm⟩
      exact IsPGroup.of_card hm
    have hCtop : IsPGroup 2 (⊤ : Subgroup C) := hCcore.to_subgroup ⊤
    let P : Sylow 2 C := hCtop.toSylow (P := ⊤) (by simp)
    exact ⟨P, by simp [P]⟩
  obtain ⟨hpcore_eq, ⟨P, hPn, hPmap⟩⟩ :=
    normalSylow_structure_of_coreFree_image q hq hcore C hker T hhsyl
  have hfit : L.map q = generalizedFitting H := by
    apply generalizedFitting_image_eq_of_card_three (L.map q) hKcard hHcard hcore
  exact ⟨⟨P, hPn⟩, hfit, hKcard⟩

end Theory.GroupTheory
