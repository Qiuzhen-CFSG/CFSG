module
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SL2Products
public import Mathlib.GroupTheory.Frattini

/-!
# Generation in a group with nested Frattini quotient SL₂(2)

If a subgroup A supplements the two-core to a Sylow subgroup, and the
Frattini quotient of the quotient by the two-core is SL₂(2), then A and one
conjugate generate modulo the two-core. No assertion that the first quotient
itself is SL₂(2) is needed.

A Sylow subgroup in SL₂(2) has order two and is not normal. Two distinct
Sylow subgroups generate that quotient. Lift a second Sylow subgroup and
remove the Frattini subgroup by its nongeneration property; then remove the
two-core, which lies in every Sylow subgroup. Sylow conjugacy gives the
conjugate form. The intermediate Sylow supplement is re-exported for the
existing generating-predecessor argument.

These are the finite-group generation steps in Stellmacher, *Pushing up*,
Arch. Math. 46 (1986), proofs of (2.3) and (2.4)(2), journal pp.12–13.
-/

namespace Stellmacher.SectionTwo
open scoped Pointwise
universe u
private theorem normal_subgroup_card_two_le_center
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) [P.Normal] (hPcard : Nat.card P = 2) :
    P ≤ Subgroup.center G := by
  obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : P)).mp hPcard
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hp_one : p = 1
  · simp [hp_one]
  have hp_eq_t : (⟨p, hp⟩ : P) = t := ht_unique ⟨p, hp⟩ (by
    intro h
    exact hp_one (congrArg Subtype.val h))
  have hconj_mem : g * p * g⁻¹ ∈ P :=
    (inferInstance : P.Normal).conj_mem p hp g
  have hconj_ne : g * p * g⁻¹ ≠ 1 := by
    intro hconj
    have h := congrArg (fun x : G ↦ g⁻¹ * x * g) hconj
    exact hp_one (by simpa [mul_assoc] using h)
  have hconj_eq_t : (⟨g * p * g⁻¹, hconj_mem⟩ : P) = t :=
    ht_unique ⟨g * p * g⁻¹, hconj_mem⟩ (by
      intro h
      exact hconj_ne (congrArg Subtype.val h))
  have hconj_eq : g * p * g⁻¹ = p :=
    congrArg Subtype.val (hconj_eq_t.trans hp_eq_t.symm)
  have h := congrArg (fun x : G ↦ x * g) hconj_eq
  simpa [mul_assoc] using h

private theorem sylow_card_two_of_isSL2Two
    {G : Type u} [Group G] [Finite G] (P : Sylow 2 G)
    (hG : IsSL2Two G) : Nat.card P = 2 := by
  have hGcard : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  rw [P.card_eq_multiplicity, hGcard]
  have hf6 : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  simp [hf6]

private theorem pCore_eq_bot_of_isSL2Two
    {G : Type u} [Group G] [Finite G] (hG : IsSL2Two G) :
    pCore 2 G = ⊥ := by
  let P : Sylow 2 G := default
  have hcoreP : pCore 2 G ≤ (P : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal P
  have hcardDvd : Nat.card (pCore 2 G) ∣ Nat.card P :=
    Subgroup.card_dvd_of_le hcoreP
  have hPcard : Nat.card P = 2 := sylow_card_two_of_isSL2Two P hG
  rw [hPcard] at hcardDvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hcardDvd with hcard | hcard
  · exact Subgroup.card_eq_one.mp hcard
  · have hcenter : pCore 2 G ≤ Subgroup.center G :=
      normal_subgroup_card_two_le_center (pCore 2 G) hcard
    exact le_bot_iff.mp (hcenter.trans (le_of_eq
      (SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hG)))

private theorem exists_moved_sylow
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (hG : IsSL2Two G) :
    ∃ g : G, g • P ≠ P := by
  by_contra hmove
  push Not at hmove
  have hnormal : (P : Subgroup G).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro g
    have h := congrArg (fun Q : Sylow 2 G ↦ (Q : Subgroup G)) (hmove g)
    change (MulAut.conj g) • (P : Subgroup G) = (P : Subgroup G) at h
    exact h
  let _ : (P : Subgroup G).Normal := hnormal
  have hPcore : (P : Subgroup G) ≤ pCore 2 G :=
    le_sSup ⟨hnormal, P.isPGroup'⟩
  have hPbot : (P : Subgroup G) = ⊥ :=
    le_bot_iff.mp (hPcore.trans (le_of_eq (pCore_eq_bot_of_isSL2Two hG)))
  have hPcard := sylow_card_two_of_isSL2Two P hG
  rw [hPbot, Subgroup.card_bot] at hPcard
  norm_num at hPcard

private theorem distinct_sylow_sup_eq_top_of_isSL2Two
    {G : Type u} [Group G] [Finite G]
    (P R : Sylow 2 G) (hne : P ≠ R) (hG : IsSL2Two G) :
    (P : Subgroup G) ⊔ (R : Subgroup G) = ⊤ := by
  let H : Subgroup G := (P : Subgroup G) ⊔ (R : Subgroup G)
  have hPcard : Nat.card P = 2 := sylow_card_two_of_isSL2Two P hG
  have hGcard : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  have htwoDvd : 2 ∣ Nat.card H := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hHdvd : Nat.card H ∣ 6 := by
    rw [← hGcard]
    simpa using (Subgroup.card_dvd_of_le (α := G) (H := H) (K := ⊤)
      (show H ≤ (⊤ : Subgroup G) from le_top))
  have hHle : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) hHdvd
  have hHcases : Nat.card H = 2 ∨ Nat.card H = 6 := by
    obtain ⟨k, hk⟩ := htwoDvd
    have hHpos : 0 < Nat.card H := Nat.card_pos
    have hk_le : k ≤ 3 := by omega
    interval_cases hkval : k
    · omega
    · exact Or.inl (by omega)
    · have hHfour : Nat.card H = 4 := by omega
      rw [hHfour] at hHdvd
      norm_num at hHdvd
    · exact Or.inr (by omega)
  rcases hHcases with hHtwo | hHsix
  · have hPH : (P : Subgroup G) = H :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by simp [hPcard, hHtwo])
    have hRH : (R : Subgroup G) = H :=
      Subgroup.eq_of_le_of_card_ge le_sup_right
        (by rw [hHtwo, sylow_card_two_of_isSL2Two R hG])
    exact (hne (Sylow.ext (hPH.trans hRH.symm))).elim
  · exact (Subgroup.card_eq_iff_eq_top H).mp (by simpa [hGcard] using hHsix)

/-- A second Sylow subgroup generates with A under the nested SL₂(2) hypothesis. -/
public theorem exists_sylow_sup_eq_top_of_nestedSL2Two
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (R : Sylow 2 G)
    (hAR : A ⊔ pCore 2 G = (R : Subgroup G))
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    ∃ P : Sylow 2 G, A ⊔ (P : Subgroup G) = ⊤ := by
  classical
  let Q : Subgroup G := pCore 2 G
  let X := G ⧸ Q
  let qQ : G →* X := QuotientGroup.mk' Q
  let Φ : Subgroup X := frattini X
  let Y := X ⧸ Φ
  let qΦ : X →* Y := QuotientGroup.mk' Φ
  let q : G →* Y := qΦ.comp qQ
  have hqQ : Function.Surjective qQ := QuotientGroup.mk'_surjective Q
  have hqΦ : Function.Surjective qΦ := QuotientGroup.mk'_surjective Φ
  have hq : Function.Surjective q := hqΦ.comp hqQ
  let RX : Sylow 2 X := R.mapSurjective hqQ
  let RY : Sylow 2 Y := RX.mapSurjective hqΦ
  have hY : IsSL2Two Y := by simpa [Y, X, Q, Φ] using hA
  obtain ⟨y, hy⟩ := exists_moved_sylow RY hY
  obtain ⟨P, hPmap⟩ := Sylow.mapSurjective_surjective hq 2 (y • RY)
  have hmapsup : (A ⊔ (P : Subgroup G)).map q = ⊤ := by
    rw [Subgroup.map_sup]
    have hAmapR : A.map q = (RY : Subgroup Y) := by
      have h := congrArg (Subgroup.map q) hAR
      rw [Subgroup.map_sup] at h
      have hQmap : Q.map q = ⊥ := by
        apply (Subgroup.map_eq_bot_iff (H := Q) (f := q)).mpr
        intro x hx
        change qΦ (qQ x) = 1
        rw [show qQ x = 1 from
          (QuotientGroup.eq_one_iff (N := Q) x).mpr hx, map_one]
      rw [hQmap, sup_bot_eq] at h
      calc
        A.map q = (R : Subgroup G).map q := h
        _ = (RY : Subgroup Y) := by
          calc
            (R : Subgroup G).map q = ((R : Subgroup G).map qQ).map qΦ := by
              rw [Subgroup.map_map]
            _ = (RX : Subgroup X).map qΦ := by
              rw [← Sylow.coe_mapSurjective hqQ R]
            _ = (RY : Subgroup Y) := by
              rw [← Sylow.coe_mapSurjective hqΦ RX]
    rw [hAmapR, ← Sylow.coe_mapSurjective hq P, hPmap]
    exact distinct_sylow_sup_eq_top_of_isSL2Two RY (y • RY) hy.symm hY
  let AX : Subgroup X := (A ⊔ (P : Subgroup G)).map qQ
  have hAXmap : AX.map qΦ = ⊤ := by
    simpa [AX, q, Subgroup.map_map] using hmapsup
  have hAXcomap := congrArg (Subgroup.comap qΦ) hAXmap
  have hAXPhi : AX ⊔ Φ = ⊤ := by
    rw [Subgroup.comap_top, Subgroup.comap_map_eq] at hAXcomap
    change AX ⊔ (QuotientGroup.mk' Φ).ker = ⊤ at hAXcomap
    rw [QuotientGroup.ker_mk'] at hAXcomap
    exact hAXcomap
  have hAXtop : AX = ⊤ := by
    exact frattini_nongenerating (by simpa [Φ] using hAXPhi)
  have hcomap := congrArg (Subgroup.comap qQ) hAXtop
  have hsupQ : (A ⊔ (P : Subgroup G)) ⊔ Q = ⊤ := by
    rw [Subgroup.comap_top, Subgroup.comap_map_eq] at hcomap
    change (A ⊔ (P : Subgroup G)) ⊔ (QuotientGroup.mk' Q).ker = ⊤ at hcomap
    rw [QuotientGroup.ker_mk'] at hcomap
    exact hcomap
  have hQP : Q ≤ (P : Subgroup G) :=
    (pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal P
  refine ⟨P, ?_⟩
  apply top_unique
  have hQsup : Q ≤ A ⊔ (P : Subgroup G) := hQP.trans le_sup_right
  rw [sup_eq_left.mpr hQsup] at hsupQ
  exact le_of_eq hsupQ.symm


/-- Two conjugates of A generate modulo the two-core. -/
public theorem exists_conjugate_sup_core_eq_top_of_nestedSL2Two
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (R : Sylow 2 G)
    (hAR : A ⊔ pCore 2 G = (R : Subgroup G))
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    ∃ g : G, A ⊔ A.conjBy g ⊔ pCore 2 G = ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_sup_eq_top_of_nestedSL2Two A R hAR hA
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  have hRconj : (R : Subgroup G).conjBy g = (P : Subgroup G) := by
    have h := congrArg (fun T : Sylow 2 G => (T : Subgroup G)) hg
    change (MulAut.conj g) • (R : Subgroup G) = (P : Subgroup G) at h
    exact h
  have hQconj : (pCore 2 G).conjBy g = pCore 2 G := by
    exact (Subgroup.normal_iff_map_conj_eq.mp (inferInstance : (pCore 2 G).Normal)) g
  have hAP : A.conjBy g ⊔ pCore 2 G = (P : Subgroup G) := by
    rw [← hRconj, ← hAR]
    simpa [Subgroup.conjBy, Subgroup.map_sup] using
      congrArg (fun K : Subgroup G => A.conjBy g ⊔ K) hQconj.symm
  refine ⟨g, ?_⟩
  rw [sup_assoc, hAP, hP]
end Stellmacher.SectionTwo
