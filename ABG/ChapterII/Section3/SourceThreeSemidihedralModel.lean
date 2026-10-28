module
public import ABG.ChapterII.Section3.QSemilinearStructure
public import ABG.ChapterII.Section2.UnitaryTwoPowerScalar
public import ABG.ChapterII.Section2.UnitaryLevelCard
public import Theory.FieldTheory.OddQuadraticCoefficientLift
public import GorensteinWalter.PGL2InnerAction
public import ABG.ChapterII.Section3.CharacteristicPowerDefs

/-!
# The actual GL2(3) model of a core-free semidihedral Q-group

A finite Q-group with trivial odd core, a semidihedral Sylow two-subgroup,
and source characteristic power three is isomorphic to the actual GL2 over
GF(3). The source datum is the characteristic SL2 subgroup of the odd-core
quotient, rather than any final ABG centralizer parameter. Group universes
are unrestricted, and the conclusion is an actual multiplicative equivalence.

Transport the source constituent through the trivial odd-core quotient and
finite-field uniqueness to SL2(GF(3)). The completed semilinear structure
theorem gives an actual determinant level and a pure odd coefficient
complement. Automorphism groups of GF(3) and GF(9) have orders one and two,
so that complement is trivial. The original projective map has trivial
coefficient part; the PSL2 range centralizer in PGL2 is trivial even at q=3,
so the group center lies in the semidihedral Sylow center and has order at
most two. A positive unitary level contains a central scalar subgroup of
order four, and either level-zero model has order 24, inconsistent with
a semidihedral Sylow of order at least 16. The remaining linear level is
exactly GL2(3). Thus orders only exclude impossible models; the surviving
isomorphism is supplied by the actual matrix construction.

Source: ABG II.3 Proposition 3, especially its q=3 discussion on article
p27, together with II.2 Lemma 1 and the source characteristic-power definition.
This is the local model step in the N2 semidihedral specialization; it uses
no ABG main theorem or global simple-group recognition result.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

private theorem model_of_two_coefficients
    {H X A : Type*} [Group H] [Finite H] [Group X] [Group A]
    (α : A →* MulAut X) (hA : IsPGroup 2 A) (D : Subgroup X)
    (L E : Subgroup H) [L.Normal] (hc : L.IsComplement' E) (ho : Odd (Nat.card E))
    (f : H →* X ⋊[α] A) (hf : Function.Injective f)
    (hL : L.map f = D.map SemidirectProduct.inl)
    (hE : E.map f ≤ (SemidirectProduct.inr : A →* X ⋊[α] A).range) :
    Nonempty (H ≃* D) := by
  let c : E →* A := SemidirectProduct.rightHom.comp (f.comp E.subtype)
  have heq (e : E) : f e = SemidirectProduct.inr (c e) := by
    obtain ⟨a, ha⟩ := hE (Subgroup.mem_map_of_mem f e.property)
    have hh := congrArg (fun z : X ⋊[α] A => z.right) ha
    change a = c e at hh
    exact ha.symm.trans (congrArg SemidirectProduct.inr hh)
  have hci : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    apply hf
    rw [heq, heq, hab]
  have hcE : Nat.card E = 1 := by
    rcases (hA.of_injective c hci).card_eq_or_dvd with h | h
    · exact h
    · exact (ho.not_two_dvd_nat h).elim
  have hbot : E = ⊥ := Subgroup.eq_bot_of_card_eq _ hcE
  have htop : L = ⊤ := by simpa only [hbot, sup_bot_eq] using hc.sup_eq_top
  let eL : L ≃* D := (L.equivMapOfInjective f hf).trans
    ((MulEquiv.subgroupCongr hL).trans
      (D.equivMapOfInjective SemidirectProduct.inl SemidirectProduct.inl_injective).symm)
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans eL)⟩

private theorem semidihedral_not_card24 {H : Type*} [Group H] [Finite H]
    (hS : HasQuasiDihedralSylowTwoSubgroups H) : Nat.card H ≠ 24 := by
  obtain ⟨S, n, hn, hSc, _⟩ := hS
  have hd : 16 ∣ Nat.card H :=
    (show 16 ∣ 2 ^ n from Nat.pow_dvd_pow 2 hn).trans
      (hSc ▸ (S : Subgroup H).card_subgroup_dvd_card)
  intro hh
  rw [hh] at hd
  norm_num at hd

private theorem center_le_two
    {H : Type} [Group H] [Finite H]
    (hH : IsQGroup H) (hcore : pPrimeCore 2 H = ⊥)
    (S : Sylow 2 H) (hS : Stellmacher.IsSemidihedralGroup S)
    (L0 : Subgroup H) [L0.Normal]
    (e0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)) :
    Nat.card (Subgroup.center H) ≤ 2 := by
  let K := GaloisField 3 1
  have hKc : Nat.card K = 3 := by simpa using GaloisField.card 3 1 (by decide)
  have hK : IsOddPrimePower (Nat.card K) := ⟨3, 1, Nat.prime_three, by decide, by decide, by simpa⟩
  let : Subsingleton (K ≃+* K) :=
    (Nat.card_eq_one_iff_unique.mp (GaloisField.card_ringAut 3 1 (by decide))).1
  let Z := subgroupCenter (S : Subgroup H)
  have hZc : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH S
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  let : Z.Normal := ⟨fun x hx g => by
    have hh := Subgroup.mem_center_iff.mp (hZc hx) g
    simpa only [hh, mul_inv_cancel_right] using hx⟩
  obtain ⟨_, _, _, _, f, L, E, hfker, _, _, _, _, _, _, hL0, _⟩ :=
    qGroup_projective_linear_complement hH hcore S Z rfl L0 K hK e0
  have hCker : Subgroup.center H ≤ f.ker := by
    intro z hz
    have hfz : f z = SemidirectProduct.inl (f z).left := by
      apply SemidirectProduct.ext
      · rfl
      · exact Subsingleton.elim _ _
    have ha : (f z).left ∈ Subgroup.centralizer
        ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :
          Set (PGL2 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨a, rfl⟩
      have hy : SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL a) ∈
          L0.map f := by rw [hL0]; exact ⟨a, rfl⟩
      obtain ⟨l, _, hl⟩ := hy
      have hh := congrArg f (Subgroup.mem_center_iff.mp hz l)
      rw [map_mul, map_mul, hl, hfz, ← map_mul, ← map_mul] at hh
      exact SemidirectProduct.inl_injective hh
    rw [pgl2_psl2Range_centralizer_eq_bot K hK] at ha
    change f z = 1
    rw [hfz, show (f z).left = 1 from ha, map_one]
  have hCZ : Subgroup.center H ≤ Z := hfker ▸ hCker
  have hZcard : Nat.card Z = 2 :=
    (Subgroup.card_map_of_injective (S : Subgroup H).subtype_injective).trans
      (QuasiDihedral.card_center hS)
  exact hZcard ▸ Subgroup.card_le_of_le hCZ

private theorem canonical_model
    {H : Type} [Group H] [Finite H]
    (hH : IsQGroup H) (hcore : pPrimeCore 2 H = ⊥)
    (hS : HasQuasiDihedralSylowTwoSubgroups H)
    (L0 : Subgroup H) [L0.Normal]
    (e0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)) :
    Nonempty (H ≃* GL2 3 1) := by
  classical
  let K := GaloisField 3 1
  have hKc : Nat.card K = 3 := by simpa using GaloisField.card 3 1 (by decide)
  have hK : IsOddPrimePower (Nat.card K) :=
    ⟨3, 1, Nat.prime_three, by decide, by decide, by simpa⟩
  obtain ⟨S, hS0⟩ := hS
  have hcenter : Nat.card (Subgroup.center H) ≤ 2 := center_le_two hH hcore S hS0 L0 e0
  obtain ⟨L, E, hLn, _, hc, _, ho, hmodel, _⟩ :=
    qGroup_semilinear_structure hH hcore L0 K hK e0
  let : L.Normal := hLn
  rcases hmodel with ⟨m, f, hf, hm, hL, hE⟩ | ⟨p, d, hp, hpo, hd, hcard, m, f, hf, hm, hL, hE⟩
  · have hAut : IsPGroup 2 (K ≃+* K) :=
      IsPGroup.of_card (n := 0) (by simpa using GaloisField.card_ringAut 3 1 (by decide))
    obtain ⟨e⟩ := model_of_two_coefficients (coefficientAction K) hAut
      (determinantTwoPower K m) L E hc ho f hf hL hE
    have hmle : m ≤ 1 := by
      by_contra h
      have h4 : 4 ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega : 2 ≤ m)
      have hbad := h4.trans hm
      norm_num [hKc] at hbad
    interval_cases m
    · have hc24 : Nat.card H = 24 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_congr (determinantTwoPowerZeroEquivSL K).toEquiv,
          sl2_card_formula, hKc]
        norm_num
      exact (semidihedral_not_card24 ⟨S, hS0⟩ hc24).elim
    · have ht : determinantTwoPower K 1 = ⊤ := by
        apply top_unique
        intro A _
        apply (mem_determinantTwoPower 1 A).mpr
        have hh : det A ^ Nat.card Kˣ = 1 := pow_card_eq_one'
        have hu : Nat.card Kˣ = 2 := (Nat.card_units K).trans (by rw [hKc])
        simpa only [hu, pow_one] using hh
      exact ⟨e.trans ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)⟩
  · let : Fact p.Prime := ⟨hp⟩
    have hpd : p ^ d = 3 := hcard.symm.trans hKc
    obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp hpd
    have hAut : IsPGroup 2 (GaloisField 3 (2 * 1) ≃+* GaloisField 3 (2 * 1)) :=
      IsPGroup.of_card (n := 1) (by simpa using GaloisField.card_ringAut 3 2 (by decide))
    obtain ⟨e⟩ := model_of_two_coefficients (GU2CoefficientAction 3 1 hd) hAut
      (SU2Level 3 1 hd m) L E hc ho f hf hL hE
    by_cases hm0 : m = 0
    · subst m
      have hc24 : Nat.card H = 24 := by
        rw [Nat.card_congr e.toEquiv, SU2Level_card 3 1 hpo hd 0 hm]
        norm_num
      exact (semidihedral_not_card24 ⟨S, hS0⟩ hc24).elim
    · let D := SU2Level 3 1 hd m
      let C := SU2ScalarLevel 3 1 hd 1
      obtain ⟨_, hCc, hCcentral, _⟩ :=
        SU2ScalarLevel_structure 3 1 hd (by decide) 1 (by decide)
      have hCD : C ≤ D := by
        apply (show C ≤ SU2Level 3 1 hd 1 from ?_).trans
          (SU2Level_mono 3 1 hd (by omega : 1 ≤ m))
        rw [SU2Level_eq_scalar_sup_zero 3 1 hd (by decide) 1 (by decide)]
        exact le_sup_left
      have hCC : C.subgroupOf D ≤ Subgroup.center D := by
        intro c hc
        apply Subgroup.mem_center_iff.mpr
        intro a
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp (hCcentral hc) a.val
      have hDC : Nat.card (Subgroup.center D) ≤ 2 := by
        rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
        exact hcenter
      have hCCcard : Nat.card C ≤ Nat.card (Subgroup.center D) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCD).toEquiv]
        exact Subgroup.card_le_of_le hCC
      have hbad := hCCcard.trans hDC
      change Nat.card (SU2ScalarLevel 3 1 hd 1) ≤ 2 at hbad
      rw [hCc] at hbad
      norm_num at hbad

universe u
public theorem qGroup_equiv_gl2_three_of_corefree_semidihedral
    {H : Type u} [Group H] [Finite H]
    (hH : IsQGroup H) (hcore : pPrimeCore 2 H = ⊥)
    (hS : HasQuasiDihedralSylowTwoSubgroups H)
    (hq : HasSourceQCharacteristicPower H 3) :
    Nonempty (H ≃* GL2 3 1) := by
  classical
  obtain ⟨F, iF, fF, _, hFc, L0, hL0, ⟨eL0⟩⟩ := hq
  let : Field F := iF
  let : Finite F := fF
  let : L0.Characteristic := hL0
  let eQ : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let M := L0.map eQ.toMonoidHom
  let : M.Normal := (inferInstance : L0.Normal).map _ eQ.surjective
  let eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) F := (eQ.subgroupMap L0).symm.trans eL0
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 3 1)
  let eF : F ≃+* GaloisField 3 1 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by decide), pow_one] using hFc)
  let H' := Shrink.{0} H
  let eH : H' ≃* H := Shrink.mulEquiv.{0} (α := H)
  let : Finite H' := Finite.of_injective eH eH.injective
  let N : Subgroup H' := M.map eH.symm.toMonoidHom
  let : N.Normal := (inferInstance : M.Normal).map _ eH.symm.surjective
  let eN : N ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1) :=
    (eH.symm.subgroupMap M).symm.trans (eM.trans (sl2RingEquiv eF))
  have hH' : IsQGroup H' := (isQGroup_iff_of_mulEquiv eH).mpr hH
  have hcore' : pPrimeCore 2 H' = ⊥ := by
    have hh := pPrimeCore_map_iso 2 eH.symm
    rw [hcore, Subgroup.map_bot] at hh
    exact hh.symm
  obtain ⟨S, hS⟩ := hS
  let T := S.mapSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  let eS : S ≃* T := (S : Subgroup H).equivMapOfInjective eH.symm.toMonoidHom eH.symm.injective
  obtain ⟨e⟩ := canonical_model hH' hcore' ⟨T, semidihedral_equiv eS hS⟩ N eN
  exact ⟨eH.symm.trans e⟩

end ABG
