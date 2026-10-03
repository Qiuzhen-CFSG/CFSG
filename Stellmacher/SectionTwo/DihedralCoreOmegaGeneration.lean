module
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.SpecificGroups.DihedralQuotientSylow

/-!
# Generating the omega-center of a dihedral local core

Let Q = O₂(P) be self-centralizing in a finite solvable group P, with
P/Q dihedral of order twice a power of three. For the supplied Sylow
two-subgroup T, assume J(T) is not contained in Q and the normal closure
V of Ω₁(Z(T)) is not central in P. Then Ω₁(Z(Q)) lies in V.

Put A = Ω₁(Z(Q)) and C = C_A(T). Characteristic two gives V ≤ A and
C ≤ V. A maximal-order elementary subgroup E of T outside Q has the same
image as T in P/Q, since that quotient Sylow has order at most two. Thus
E join Q = T, and C_A(E) = C. Applying the maximal-elementary offender
bound to P/C_P(A), which is a quotient of P/Q, gives |A| ≤ 2|C|.
If V is proper in A, relative-index counting forces V = C. Then both Q
and T centralize V. The normal-generation conclusion for an odd-dihedral
quotient forces all of P to centralize V, a contradiction.

This supplementary local lemma supplies the neighboring-core omega bound
in the first containment case of Stellmacher (8.2), journal pp.37–38.
Its hypotheses are provided there by (6.2) and (6.3), while the counting
input is the offender inequality from (2.2). Source context:
`refs/latex/stellmacher-n-group.tex`. This is not a verbatim source claim;
it does not use the (8.2) classification or critical-distance conclusions.
Solvability is retained in the consumer interface but is not needed by
this argument once the ordinary dihedral quotient is supplied.
-/

namespace Stellmacher.SectionTwo
universe u

/-- The actual Sylow-center conjugates contain the omega-center of the core. -/
public theorem dihedral_core_omega_le_vSubgroup
    {P : Type u} [Group P] [Finite P]
    (hsolv : Group.IsSolvable P)
    (hself : Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P)
    (hdihedral : ∃ n : ℕ, Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup (3 ^ n)))
    (T : Sylow 2 P)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup P) ≤ pCore 2 P)
    (hnoncentral : ¬ vSubgroup T ≤ Subgroup.center P) :
    omegaOneCenterAmbient (pCore 2 P) ≤ vSubgroup T := by
  classical
  have _ := hsolv
  let Q := pCore 2 P
  let A := omegaOneCenterAmbient Q
  let V := vSubgroup T
  let _ : V.Normal := Subgroup.normalClosure_normal
  let C := A ⊓ Subgroup.centralizer (T : Set P)
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ZQ : Subgroup Q := Subgroup.center Q
  let W : Subgroup ZQ := omega₁ (G := ZQ) (p := 2)
  let B : Subgroup Q := W.map ZQ.subtype
  let _ : ZQ.Characteristic := Subgroup.centerCharacteristic
  let _ : W.Characteristic := omega₁_characteristic ZQ
  let _ : B.Characteristic := Subgroup.characteristic_of_characteristic_of_characteristic
  let _ : A.Normal := ConjAct.normal_of_characteristic_of_normal (K := B)
  let _ : IsElementaryAbelian 2 A := omegaOneCenterAmbient_elementaryAbelian Q
  have hQT : Q ≤ (T : Subgroup P) := fitting_pCore_le_sylow T
  have hAQ : A ≤ Q := fun x hx => ((mem_omegaOneCenterAmbient_iff Q x).mp hx).1
  have hACQ : A ≤ Subgroup.centralizer (Q : Set P) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff Q x).mp hx).2.2
  have hQA : Q ≤ Subgroup.centralizer (A : Set P) := Subgroup.le_centralizer_iff.mp hACQ
  have hzA : zSubgroup T ≤ A := by
    intro x hx
    obtain ⟨_, hxpow, hxcent⟩ := (mem_omegaOneCenterAmbient_iff (T : Subgroup P) x).mp hx
    have hxCQ : x ∈ Subgroup.centralizer (Q : Set P) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => hxcent y (hQT hy)
    exact (mem_omegaOneCenterAmbient_iff Q x).mpr
      ⟨hself hxCQ, hxpow, fun y hy => hxcent y (hQT hy)⟩
  have hVA : V ≤ A := Subgroup.normalClosure_le_normal hzA
  have hCV : C ≤ V := by
    apply le_trans _ (Subgroup.le_normalClosure (H := zSubgroup T))
    intro x hx
    obtain ⟨hxQ, hxpow, _⟩ := (mem_omegaOneCenterAmbient_iff Q x).mp hx.1
    exact (mem_omegaOneCenterAmbient_iff (T : Subgroup P) x).mpr
      ⟨hQT hxQ, hxpow, Subgroup.mem_centralizer_iff.mp hx.2⟩
  obtain ⟨E, hE, hEQnot⟩ : ∃ E ∈ elementaryAbelianMaxSubgroups (T : Subgroup P), ¬ E ≤ Q := by
    by_contra! hall
    exact hJ (sSup_le hall)
  let projection : P →* P ⧸ Q := QuotientGroup.mk' Q
  have hsurj : Function.Surjective projection := QuotientGroup.mk'_surjective Q
  let Tbar := T.mapSurjective hsurj
  obtain ⟨n, ⟨equiv⟩⟩ := hdihedral
  have hbar := odd_dihedral_quotient_sylow (3 ^ n) ((by decide : Odd 3).pow)
    equiv.symm.toMonoidHom equiv.symm.surjective Tbar
  have hmapne : E.map projection ≠ ⊥ := by
    intro hb
    apply hEQnot
    have hh := (Subgroup.map_eq_bot_iff E).mp hb
    rwa [QuotientGroup.ker_mk'] at hh
  have hcardE : 2 ≤ Nat.card (E.map projection) := by
    have hh := (Subgroup.one_lt_card_iff_ne_bot (E.map projection)).mpr hmapne
    omega
  have hmap : E.map projection = (T : Subgroup P).map projection :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hE.1) (hbar.1.trans hcardE)
  have hEQ : E ⊔ Q = (T : Subgroup P) := by
    have hh := congrArg (Subgroup.comap projection) hmap
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.mpr hQT] at hh
  have hfixed : A ⊓ Subgroup.centralizer (E : Set P) = C := by
    apply le_antisymm
    · apply le_inf inf_le_left
      change A ⊓ Subgroup.centralizer (E : Set P) ≤
        Subgroup.centralizer ((T : Subgroup P) : Set P)
      rw [← hEQ]
      apply Subgroup.le_centralizer_iff.mpr
      exact sup_le (Subgroup.le_centralizer_iff.mp inf_le_right)
        (hQA.trans (Subgroup.centralizer_le inf_le_left))
    · exact inf_le_inf_left A (Subgroup.centralizer_le hE.1)
  let centralProjection := QuotientGroup.mk' (Subgroup.centralizer (A : Set P))
  have hQker : Q ≤ centralProjection.ker := by
    rwa [QuotientGroup.ker_mk']
  let factor := QuotientGroup.lift Q centralProjection hQker
  have hfactor : factor.comp projection = centralProjection := by ext x; rfl
  have hcentralCard : Nat.card (E.map centralProjection) ≤ 2 := by
    rw [← hfactor, ← Subgroup.map_map]
    have hh : Nat.card (E.map projection) ≤ 2 := hmap ▸ hbar.1
    exact (Nat.le_of_dvd Nat.card_pos ((E.map projection).card_map_dvd factor)).trans hh
  have hbound : Nat.card A ≤ Nat.card C * 2 := by
    have hh := maxElementary_card_le_fixed_mul_image (T : Subgroup P) A E
      (hAQ.trans hQT) hE centralProjection (QuotientGroup.ker_mk' _)
    rw [hfixed] at hh
    exact hh.trans (Nat.mul_le_mul_left _ hcentralCard)
  by_contra hAV
  have hprod : Nat.card V * V.relIndex A = Nat.card A := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup P) V A bot_le hVA
  have hindex : 2 ≤ V.relIndex A := by
    have hne : V.relIndex A ≠ 1 := fun hh => hAV (Subgroup.relIndex_eq_one.mp hh)
    have hpos : 0 < V.relIndex A := by
      have hApos : 0 < Nat.card A := Nat.card_pos
      nlinarith
    omega
  have hVC : V = C := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hCV
    nlinarith
  have hTCV : (T : Subgroup P) ≤ Subgroup.centralizer (V : Set P) := by
    apply Subgroup.le_centralizer_iff.mp
    rw [hVC]
    exact inf_le_right
  have hQCV : Q ≤ Subgroup.centralizer (V : Set P) :=
    hQA.trans (Subgroup.centralizer_le hVA)
  have hgen : Subgroup.normalClosure (T : Set P) ⊔ Q = ⊤ := by
    have hm : (Subgroup.normalClosure (T : Set P)).map projection = ⊤ := by
      rw [Subgroup.map_normalClosure _ _ hsurj]
      exact hbar.2
    have hh := congrArg (Subgroup.comap projection) hm
    simpa only [Subgroup.comap_map_eq, projection, QuotientGroup.ker_mk', Subgroup.comap_top] using hh
  have htop : (⊤ : Subgroup P) ≤ Subgroup.centralizer (V : Set P) := by
    rw [← hgen]
    exact sup_le (Subgroup.normalClosure_le_normal hTCV) hQCV
  apply hnoncentral
  intro x hx
  exact Subgroup.mem_center_iff.mpr fun y =>
    (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top y)) x hx).symm

end Stellmacher.SectionTwo
