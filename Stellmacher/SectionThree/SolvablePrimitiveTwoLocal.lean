module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Quotient
public import FeitThompson.BGsection4.theorem_4_12_a

/-!
# Solvable primitive 2-local groups

This module proves the solvable primitive-group structure theorem used in
Stellmacher (3.3), Journal of Algebra 190 (1997), pp. 21--22.  If a Sylow
2-subgroup `T` lies in a unique maximal subgroup `B`, the `2`-core is trivial,
and the ambient group is solvable, then the two-residual is an odd-prime group,
the normal core of `B` is its Frattini subgroup, and the two-residual in the
normal-core quotient is irreducible under the image of `T`.

The proof first applies the core-free quotient construction.  Hall
`{2,p}`-subgroups show that no other primes divide the group order.  A Frattini
normalizer argument excludes a `2`-part in `B.normalCore`, so the preimage of
the quotient's elementary abelian complement is the ambient two-residual and
is a `p`-group.  Finally, Maschke's invariant-complement theorem on the
Frattini quotient forces `B.normalCore` to equal the residual's Frattini
subgroup.  The irreducibility statement is intentionally formulated in
`Q/B.normalCore`, matching the journal source's `O²(Q/P₀)` rather than the
mistranscribed quotient of `O²(Q)` in the LaTeX reference.
-/

namespace Stellmacher.SectionThree

open scoped Pointwise IsMulCommutative
open BenderSuzuki.External

universe u

private theorem hall_map_of_surjective
    {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {π : Set Nat.Primes} {H : Subgroup G} (hHall : IsHallSubgroup π H)
    (f : G →* G') (hf : Function.Surjective f) :
    IsHallSubgroup π (H.map f) := by
  refine isHallSubgroup_of (G := G') (π := π) (H := H.map f) ?_ ?_
  · intro q hq
    exact hHall.p_in_pi_of_p_dvd_card q
      (hq.trans (Subgroup.card_map_dvd (H := H) f))
  · intro q hqπ hq
    exact (hHall.p_in_pi_of_p_dvd_index q
      (hq.trans (Subgroup.index_map_dvd (H := H) hf))) hqπ

private theorem normal_pSubgroup_le_hall
    {G : Type*} [Group G] [Finite G] {π : Set Nat.Primes}
    {H N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hNp : IsPGroup p N) (hHall : IsHallSubgroup π H)
    (hpπ : (⟨p, Fact.out⟩ : Nat.Primes) ∈ π) :
    N ≤ H := by
  classical
  let PH : Sylow p H := Classical.choice (Sylow.nonempty (p := p) (G := H))
  let Psub : Subgroup G := (PH : Subgroup H).map H.subtype
  have hPsubp : IsPGroup p Psub := by
    simpa [Psub] using PH.isPGroup'.map H.subtype
  have hpH : ¬ p ∣ H.index := by
    intro hp
    exact (hHall.p_in_pi_of_p_dvd_index ⟨p, Fact.out⟩ hp) hpπ
  have hpPH : ¬ p ∣ (PH : Subgroup H).index := PH.not_dvd_index
  have hpPsub : ¬ p ∣ Psub.index := by
    rw [show Psub.index = (PH : Subgroup H).index * H.index by
      simpa [Psub] using Subgroup.index_map_subtype (K := (PH : Subgroup H))]
    exact Nat.Prime.not_dvd_mul Fact.out hpPH hpH
  let S : Sylow p G := IsPGroup.toSylow hPsubp hpPsub
  have hSH : (S : Subgroup G) ≤ H := by
    intro x hx
    change x ∈ Psub at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  obtain ⟨P, hNP⟩ := IsPGroup.exists_le_sylow (p := p) hNp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hNgP : N ≤ ((g • P : Sylow p G) : Subgroup G) := by
    intro n hn
    rw [Sylow.coe_subgroup_smul]
    refine (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
      (a := MulAut.conj g) (S := (P : Subgroup G)) (x := n)).2 ?_
    have hnN : g⁻¹ * n * g ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem n hn g⁻¹
    have hnP : g⁻¹ * n * g ∈ (P : Subgroup G) := hNP hnN
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hnP
  exact (by simpa [hg] using hNgP : N ≤ (S : Subgroup G)).trans hSH

private theorem solvable_isPi_of_quotient_p_complement
    {Q : Type u} [Group Q] [Finite Q]
    (T B N : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hsolv : Group.IsSolvable Q)
    (hNnormal : N.Normal) (hNleB : N ≤ B)
    {p : ℕ} (hp : p.Prime) (K : Subgroup (Q ⧸ N))
    (hKnormal : K.Normal) (hKp : IsPGroup p K)
    (hKT : K ⊔ T.map (QuotientGroup.mk' N) = ⊤) :
    IsPiSubgroup ({q : Nat.Primes | q.val = 2 ∨ q.val = p})
      (⊤ : Subgroup Q) := by
  classical
  let _ : Group.IsSolvable Q := hsolv
  let _ : N.Normal := hNnormal
  let _ : Fact p.Prime := ⟨hp⟩
  let π : Set Nat.Primes := {q | q.val = 2 ∨ q.val = p}
  have hTtwo : IsPGroup 2 T := by
    rw [← hT]
    exact Tₛ.isPGroup'
  have hTπ : IsPiSubgroup π T := by
    have hs : IsPiSubgroup ({⟨2, Nat.prime_two⟩} : Set Nat.Primes) T :=
      section8_isPiSubgroup_singleton_of_isPGroup hTtwo
    intro q hq
    have hq2 : q = ⟨2, Nat.prime_two⟩ :=
      Set.mem_singleton_iff.mp (hs q hq)
    subst q
    exact Or.inl rfl
  let _ : MulDistribMulAction Unit Q := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  have hTinv : IsInvariant Unit Q T := by
    constructor
    intro a x
    cases a
    rfl
  obtain ⟨H, hHall, _hHinv, hTH⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := Q) (A := Unit) hsolv (by simp) π T hTπ hTinv
  let qN : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hqN : Function.Surjective qN := QuotientGroup.mk'_surjective N
  have hHallbar : IsHallSubgroup π (H.map qN) :=
    hall_map_of_surjective hHall qN hqN
  have hKle : K ≤ H.map qN := by
    apply normal_pSubgroup_le_hall hKp hHallbar
    exact Or.inr rfl
  have hTbarle : T.map qN ≤ H.map qN := Subgroup.map_mono hTH
  have hHbar : H.map qN = ⊤ := by
    apply top_unique
    rw [← hKT]
    exact sup_le hKle hTbarle
  have hHN : H ⊔ N = ⊤ := by
    have hc := Subgroup.comap_map_eq qN H
    rw [hHbar] at hc
    simpa [qN, QuotientGroup.ker_mk', hqN] using hc.symm
  have hHtop : H = ⊤ := by
    rcases eq_top_or_exists_le_coatom H with h | ⟨M, hM, hHM⟩
    · exact h
    · have hMT : T ≤ M := hTH.trans hHM
      have hMB : M = B := huniq M hM hMT
      have hNleM : N ≤ M := hNleB.trans_eq hMB.symm
      have : (⊤ : Subgroup Q) ≤ M := by
        rw [← hHN]
        exact sup_le hHM hNleM
      exact False.elim (hM.ne_top (top_unique this))
  intro q hq
  have hqH : q.val ∣ Nat.card H := by simpa [hHtop] using hq
  exact hHall.p_in_pi_of_p_dvd_card q hqH

private theorem normal_core_card_not_even
    {Q : Type u} [Group Q] [Finite Q]
    (T B N : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hNnormal : N.Normal) (hNleB : N ≤ B)
    (hcore2 : pCore 2 Q = ⊥) :
    ¬ 2 ∣ Nat.card N := by
  classical
  let _ : N.Normal := hNnormal
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Sylow 2 N := default
  let F : Subgroup Q := (U : Subgroup N).map N.subtype
  have hFp : IsPGroup 2 F := by
    simpa [F] using U.isPGroup'.map N.subtype
  by_contra htwo
  have hUne : (U : Subgroup N) ≠ ⊥ :=
    U.ne_bot_of_dvd_card htwo
  have hFne : F ≠ ⊥ := by
    intro hF
    apply hUne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := (U : Subgroup N)) (f := N.subtype) N.subtype_injective).1
        (by simpa [F] using hF)
  obtain ⟨W, hFW⟩ := IsPGroup.exists_le_sylow (p := 2) hFp
  have hWtwo : IsPGroup 2 (W : Subgroup Q) := W.isPGroup'
  have hWsubtwo : IsPGroup 2 (W.subgroupOf N) :=
    hWtwo.comap_subtype
  have hUle : (U : Subgroup N) ≤ W.subgroupOf N := by
    intro x hx
    change (x : N).1 ∈ W
    exact hFW ⟨x, hx, rfl⟩
  have hWsub : W.subgroupOf N = (U : Subgroup N) :=
    U.is_maximal' hWsubtwo hUle
  have hWinfN : (W : Subgroup Q) ⊓ N = F := by
    ext x
    constructor
    · intro hx
      have hxsub : (⟨x, hx.2⟩ : N) ∈ W.subgroupOf N := hx.1
      rw [hWsub] at hxsub
      exact ⟨⟨x, hx.2⟩, hxsub, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hFW ⟨x, hx, rfl⟩, x.2⟩
  have hFleN : F ≤ N := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  have hWnorm : (W : Subgroup Q) ≤ Subgroup.normalizer (F : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro w hw f hf
    rw [← hWinfN]
    refine ⟨?_, ?_⟩
    · exact W.mul_mem (W.mul_mem hw (hFW hf)) (W.inv_mem hw)
    · exact hNnormal.conj_mem f (hFleN hf) w
  have hnorm_ne_top : Subgroup.normalizer (F : Set Q) ≠ ⊤ := by
    intro htop
    have hFnorm : F.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hFcore : F ≤ pCore 2 Q := by
      exact le_sSup ⟨hFnorm, hFp⟩
    apply hFne
    apply le_antisymm
    · simpa [hcore2] using hFcore
    · exact bot_le
  obtain ⟨M, hM, hnormM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (F : Set Q))).resolve_left
      hnorm_ne_top
  have hWM : (W : Subgroup Q) ≤ M := hWnorm.trans hnormM
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q W Tₛ
  let e : Q ≃* Q := MulAut.conj g
  let M' : Subgroup Q := M.map e.toMonoidHom
  have hM' : IsCoatom M' := by
    exact (OrderIso.isCoatom_iff e.mapSubgroup M).2 hM
  have hmapW : (W : Subgroup Q).map e.toMonoidHom = T := by
    have h := congrArg (fun P : Sylow 2 Q ↦ (P : Subgroup Q)) hg
    have he :
        MulDistribMulAction.toMonoidEnd (MulAut Q) Q (MulAut.conj g) =
          (MulAut.conj g).toMonoidHom := by
      ext x
      rfl
    simpa only [e, hT, Sylow.coe_subgroup_smul,
      Subgroup.pointwise_smul_def, he] using h
  have hTM' : T ≤ M' := by
    rw [← hmapW]
    exact Subgroup.map_mono hWM
  have hM'B : M' = B := huniq M' hM' hTM'
  have hNM : N ≤ M := by
    intro n hn
    have henN : e n ∈ N := by
      simpa [e, MulAut.conj_apply] using hNnormal.conj_mem n hn g
    have henB : e n ∈ B := hNleB henN
    rw [← hM'B] at henB
    obtain ⟨m, hm, hmn⟩ := henB
    have hmn' : m = n := e.injective hmn
    simpa [hmn'] using hm
  have hfrattini := Sylow.normalizer_sup_eq_top (G := Q) (N := N) U
  have htopM : (⊤ : Subgroup Q) ≤ M := by
    rw [← hfrattini]
    exact sup_le hnormM hNM
  exact hM.ne_top (top_unique htopM)

private theorem pGroup_of_isPi_two_prime_of_card_not_even
    {Q : Type u} [Group Q] [Finite Q]
    (N : Subgroup Q) {p : ℕ} (hp : p.Prime)
    (hQπ : IsPiSubgroup ({q : Nat.Primes | q.val = 2 ∨ q.val = p})
      (⊤ : Subgroup Q))
    (hNodd : ¬ 2 ∣ Nat.card N) :
    IsPGroup p N := by
  let pp : Nat.Primes := ⟨p, hp⟩
  apply section8_isPGroup_of_isPiSubgroup_singleton (q := pp)
  intro q hq
  have hqQ : q.val ∣ Nat.card (⊤ : Subgroup Q) := by
    have hdiv : Nat.card N ∣ Nat.card Q :=
      Subgroup.card_subgroup_dvd_card (s := N) (α := Q)
    simpa using hq.trans hdiv
  rcases hQπ q hqQ with hq2 | hqp
  · exact False.elim (hNodd (by simpa [hq2] using hq))
  · have : q = pp := by
      apply Subtype.ext
      exact hqp
    exact Set.mem_singleton_iff.mpr this

private theorem preimage_pGroup_and_residual
    {Q : Type u} [Group Q] [Finite Q]
    (T N : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hNnormal : N.Normal) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hNp : IsPGroup p N) (K : Subgroup (Q ⧸ N))
    (hKnormal : K.Normal) (hKp : IsPGroup p K)
    (hKT : K ⊔ T.map (QuotientGroup.mk' N) = ⊤) :
    let R := K.comap (QuotientGroup.mk' N)
    R.Normal ∧ IsPGroup p R ∧ R ⊔ T = ⊤ ∧
      twoResidualAmbient (⊤ : Subgroup Q) = R := by
  classical
  let _ : N.Normal := hNnormal
  let _ : Fact p.Prime := ⟨hp⟩
  let qN : Q →* Q ⧸ N := QuotientGroup.mk' N
  let R : Subgroup Q := K.comap qN
  have hqN : Function.Surjective qN := QuotientGroup.mk'_surjective N
  have hRnormal : R.Normal := hKnormal.comap qN
  let _ : R.Normal := hRnormal
  have hNR : N ≤ R := by
    intro n hn
    change qN n ∈ K
    have hnq : qN n = 1 := by
      exact (QuotientGroup.eq_one_iff n).2 hn
    rw [hnq]
    exact K.one_mem
  have hRmap : R.map qN = K := by
    simpa [R, hqN] using Subgroup.map_comap_eq qN K
  have hNsubp : IsPGroup p (N.subgroupOf R) :=
    hNp.comap_subtype
  have hNsubnormal : (N.subgroupOf R).Normal := hNnormal.subgroupOf R
  let _ : (N.subgroupOf R).Normal := hNsubnormal
  have hquotp : IsPGroup p (R ⧸ N.subgroupOf R) := by
    have himagep : IsPGroup p (R.map qN) := by
      rw [hRmap]
      exact hKp
    exact himagep.of_equiv (quotientSubgroupRangeEquiv R N).symm
  have hRp : IsPGroup p R :=
    hkt_isPGroup_of_normal_quotient (N.subgroupOf R) hNsubp hquotp
  have hmapRT : (R ⊔ T).map qN = ⊤ := by
    rw [Subgroup.map_sup, hRmap]
    exact hKT
  have hRTtop : R ⊔ T = ⊤ := by
    have hc := Subgroup.comap_map_eq qN (R ⊔ T)
    rw [hmapRT] at hc
    have hker : qN.ker ≤ R ⊔ T := by
      simpa [qN, QuotientGroup.ker_mk'] using hNR.trans le_sup_left
    have htop_eq : (⊤ : Subgroup Q) = (R ⊔ T) ⊔ qN.ker := by
      simpa only [Subgroup.comap_top] using hc
    apply top_unique
    rw [htop_eq]
    exact sup_le le_rfl hker
  exact ⟨hRnormal, hRp, hRTtop,
    twoResidualAmbient_top_eq_of_normal_complement_sylow_two
      hp hp2 R T Tₛ hT hRnormal hRp hRTtop⟩

private theorem elementaryAbelian_of_mulEquiv
    {A B : Type u} [Group A] [Group B] (p : ℕ)
    (e : A ≃* B) (hA : IsElementaryAbelian p A) :
    IsElementaryAbelian p B := by
  let _ : IsElementaryAbelian p A := hA
  refine
    { toIsMulCommutative := { is_comm := Std.Commutative.mk ?_ }
      exponent_dvd_p := ?_ }
  · intro a b
    have hcomm : e.symm a * e.symm b = e.symm b * e.symm a :=
      IsMulCommutative.is_comm.comm (e.symm a) (e.symm b)
    apply_fun e at hcomm
    simpa using hcomm
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    have hx : (e.symm x) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p A) (e.symm x)
    apply_fun e at hx
    simpa using hx

private theorem normal_subgroup_eq_frattini_of_maschke
    {Q : Type u} [Group Q] [Finite Q]
    (T B R N : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hB : IsCoatom B) (hTB : T ≤ B)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hRnormal : R.Normal)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRp' : IsPGroup p R) (hNR : N ≤ R)
    (hRinfB : R ⊓ B = N) (hRT : R ⊔ T = ⊤)
    (hresR : twoResidualAmbient (⊤ : Subgroup Q) = R)
    (hNnormal : N.Normal)
    (hQuotElem : IsElementaryAbelian p (R ⧸ N.subgroupOf R)) :
    N = (frattini R).map R.subtype := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : R.Normal := hRnormal
  let _ : N.Normal := hNnormal
  let Nsub : Subgroup R := N.subgroupOf R
  have hNsubnormal : Nsub.Normal := hNnormal.subgroupOf R
  let _ : Nsub.Normal := hNsubnormal
  have hQuotP : IsPGroup p (R ⧸ Nsub) := by
    let _ : IsElementaryAbelian p (R ⧸ Nsub) := hQuotElem
    exact IsElementaryAbelian.isPGroup p (R ⧸ Nsub)
  have hPhiN : frattini R ≤ Nsub := by
    let _ : IsElementaryAbelian p (R ⧸ Nsub) := hQuotElem
    let _ : Fact (IsPGroup p (R ⧸ Nsub)) := ⟨hQuotP⟩
    have hPhiQuot : frattini (R ⧸ Nsub) = ⊥ :=
      frattini_eq_bot_of_isElementaryAbelian (R := R ⧸ Nsub) (p := p)
    have hle := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective Nsub)
    simpa [hPhiQuot, QuotientGroup.ker_mk'] using hle
  apply le_antisymm
  · intro n hn
    have hnR : n ∈ R := hNR hn
    suffices (⟨n, hnR⟩ : R) ∈ frattini R by
      exact ⟨⟨n, hnR⟩, this, rfl⟩
    by_contra hnPhi
    let Φ : Subgroup R := frattini R
    have hPhiNe : Φ ≠ Nsub := by
      intro heq
      apply hnPhi
      change (⟨n, hnR⟩ : R) ∈ Φ
      rw [heq]
      exact hn
    have hTtwo : IsPGroup 2 T := by
      rw [← hT]
      exact Tₛ.isPGroup'
    have hRTdisj : Disjoint R T :=
      IsPGroup.disjoint_of_ne p 2 hp2 R T hRp' hTtwo
    have hTnormR : T ≤ Subgroup.normalizer (R : Set Q) :=
      Subgroup.le_normalizer_of_normal
    let _ : MulDistribMulAction T R :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer T R hTnormR
    have hNsubInv : IsInvariant T R Nsub := by
      constructor
      intro t x
      change x.1 ∈ N ↔ (t : Q) * x.1 * (t : Q)⁻¹ ∈ N
      exact Subgroup.mem_normalizer_iff.mp
        (Subgroup.le_normalizer_of_normal (H := N) t.2) x.1
    let _ : IsInvariant T R Nsub := hNsubInv
    have hPhiInv : IsInvariant T R Φ := by
      let _ : Φ.Characteristic := by
        simpa [Φ] using frattini_characteristic (G := R)
      exact isInvariant_of_characteristic Φ
    let _ : IsInvariant T R Φ := hPhiInv
    let _ : Φ.Normal := by
      dsimp [Φ]
      infer_instance
    let qPhi : R →* R ⧸ Φ := QuotientGroup.mk' Φ
    let _ : MulDistribMulAction T (R ⧸ Φ) :=
      quotientMulDistribMulAction Φ hPhiInv
    let Nbar : Subgroup (R ⧸ Φ) := Nsub.map qPhi
    have hNbarInv : IsInvariant T (R ⧸ Φ) Nbar := by
      simpa [Nbar, qPhi] using isInvariant_map_quotient Nsub
    let _ : IsInvariant T (R ⧸ Φ) Nbar := hNbarInv
    let _ : Fact (IsPGroup p R) := ⟨hRp'⟩
    let _ : IsElementaryAbelian p (R ⧸ Φ) :=
      isElementaryAbelian_quotient_frattini
    have hcop : Nat.Coprime p (Nat.card T) := by
      obtain ⟨k, hTk⟩ := hTtwo.exists_card_eq
      rw [hTk]
      exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right k
    obtain ⟨C, hCompl, hCInv⟩ :=
      exists_isCompl_isInvariant_of_elementaryAbelian_coprime
        hcop Nbar
    let _ : IsInvariant T (R ⧸ Φ) C := hCInv
    let A : Subgroup R := C.comap qPhi
    have hqPhi : Function.Surjective qPhi := QuotientGroup.mk'_surjective Φ
    have hAmap : A.map qPhi = C := by
      simpa [A, hqPhi] using Subgroup.map_comap_eq qPhi C
    have hNbarComap : Nbar.comap qPhi = Nsub := by
      calc
        Nbar.comap qPhi = Nsub ⊔ qPhi.ker := by
          exact Subgroup.comap_map_eq qPhi Nsub
        _ = Nsub ⊔ Φ := by
          rw [show qPhi.ker = Φ by exact QuotientGroup.ker_mk' Φ]
        _ = Nsub := sup_eq_left.2 hPhiN
    have hAneTop : A ≠ ⊤ := by
      intro hAtop
      have hCtop : C = ⊤ := by
        rw [← hAmap, hAtop]
        exact Subgroup.map_top_of_surjective qPhi hqPhi
      have hNbarBot : Nbar = ⊥ := by
        have hi := hCompl.inf_eq_bot
        simpa [hCtop] using hi
      apply hPhiNe
      apply le_antisymm hPhiN
      have hc : Nsub ≤ Φ := by
        rw [← hNbarComap, hNbarBot]
        simp [qPhi, QuotientGroup.ker_mk']
      simpa [Φ] using hc
    have hNsubNeTop : Nsub ≠ ⊤ := by
      intro hNtop
      have hRleB : R ≤ B := by
        intro r hr
        have hrNsub : (⟨r, hr⟩ : R) ∈ Nsub := by simp [hNtop]
        have hrN : r ∈ N := hrNsub
        rw [← hRinfB] at hrN
        exact hrN.2
      apply hB.ne_top
      apply top_unique
      rw [← hRT]
      exact sup_le hRleB hTB
    have hAnotN : ¬ A ≤ Nsub := by
      intro hAN
      have hCN : C ≤ Nbar := by
        rw [← hAmap]
        exact Subgroup.map_mono hAN
      have hNbarTop : Nbar = ⊤ := by
        apply top_unique
        rw [← hCompl.sup_eq_top]
        exact sup_le le_rfl hCN
      apply hNsubNeTop
      rw [← hNbarComap, hNbarTop]
      simp
    have hAInv : IsInvariant T R A := by
      constructor
      intro t x
      change qPhi x ∈ C ↔ qPhi (t • x) ∈ C
      exact IsInvariant.invariant t (qPhi x)
    let Aamb : Subgroup Q := A.map R.subtype
    have hAambR : Aamb ≤ R := by
      simpa [Aamb] using Subgroup.map_subtype_le (H := R) (K := A)
    have hAnormal : A.Normal := by
      exact (Subgroup.normal_of_isMulCommutative C).comap qPhi
    have hRnormAamb : R ≤ Subgroup.normalizer (Aamb : Set Q) := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hAambR).mp
      have hsubeq : Aamb.subgroupOf R = A := by
        apply Subgroup.map_injective R.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hAambR]
      rw [hsubeq]
      exact hAnormal
    have hTnormAamb : T ≤ Subgroup.normalizer (Aamb : Set Q) := by
      apply subgroup_le_normalizer_of_conj_mem Aamb T
      intro t x hx
      rcases hx with ⟨a, ha, rfl⟩
      refine ⟨t • a, (hAInv.invariant t a).1 ha, ?_⟩
      rfl
    have hAambNormal : Aamb.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hRT]
      exact sup_le hRnormAamb hTnormAamb
    have hAambp : IsPGroup p Aamb := IsPGroup.map (hRp'.to_subgroup A) R.subtype
    have hATneTop : Aamb ⊔ T ≠ ⊤ := by
      intro hAT
      let _ : Aamb.Normal := hAambNormal
      let qA : Q →* Q ⧸ Aamb := QuotientGroup.mk' Aamb
      have hmapT : T.map qA = ⊤ := by
        have hmapSup := congrArg (fun H : Subgroup Q => H.map qA) hAT
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self,
          bot_sup_eq, Subgroup.map_top_of_surjective qA
            (QuotientGroup.mk'_surjective Aamb)] at hmapSup
        exact hmapSup
      have hmapTtwo : IsPGroup 2 (T.map qA) := IsPGroup.map hTtwo qA
      have htop2 : IsPGroup 2 (⊤ : Subgroup (Q ⧸ Aamb)) := by
        rw [hmapT] at hmapTtwo
        exact hmapTtwo
      have hquot2 : IsPGroup 2 (Q ⧸ Aamb) :=
        htop2.of_equiv Subgroup.topEquiv
      have hresA := twoResidualAmbient_top_eq_of_normal_pGroup_quotient_two
        hp hp2 Aamb hAambNormal hAambp hquot2
      have hAambEqR : Aamb = R := hresA.symm.trans hresR
      apply hAneTop
      apply Subgroup.map_injective R.subtype_injective
      rw [show (⊤ : Subgroup R).map R.subtype = R by
        exact (MonoidHom.range_eq_map R.subtype).symm.trans R.range_subtype]
      exact hAambEqR
    obtain ⟨M, hM, hATM⟩ :=
      (eq_top_or_exists_le_coatom (Aamb ⊔ T)).resolve_left hATneTop
    have hMT : T ≤ M := le_sup_right.trans hATM
    have hMB : M = B := huniq M hM hMT
    apply hAnotN
    intro a ha
    have haAmb : (a : Q) ∈ Aamb := ⟨a, ha, rfl⟩
    have haB : (a : Q) ∈ B := by
      rw [← hMB]
      exact hATM ((le_sup_left : Aamb ≤ Aamb ⊔ T) haAmb)
    have haN : (a : Q) ∈ N := by
      rw [← hRinfB]
      exact ⟨a.2, haB⟩
    exact haN
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact hPhiN hr

public theorem solvable_primitive_two_local
    {Q : Type u} [Group Q] [Finite Q]
    (T B : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hB : IsCoatom B) (hTB : T ≤ B)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hcore2 : pCore 2 Q = ⊥) (hsolv : Group.IsSolvable Q) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      IsPGroup p (twoResidualAmbient (⊤ : Subgroup Q)) ∧
      B.normalCore = frattiniAmbient (twoResidualAmbient (⊤ : Subgroup Q)) ∧
      IsIrreducibleResidualQuotient T B.normalCore := by
  classical
  let N : Subgroup Q := B.normalCore
  have hNnormal : N.Normal := inferInstance
  let _ : N.Normal := hNnormal
  have hNleB : N ≤ B := B.normalCore_le
  obtain ⟨p, K, hp, hpodd, hKnormal, hKelem, hKinfB, hKT, hirred⟩ :=
    quotientCoreFree_data T B Tₛ hT hB hTB huniq hsolv
  have hp2 : p ≠ 2 := by
    intro hp2
    subst p
    rcases hpodd with ⟨k, hk⟩
    omega
  let _ : Fact p.Prime := ⟨hp⟩
  have hKp : IsPGroup p K := by
    let _ : IsElementaryAbelian p K := hKelem
    exact IsElementaryAbelian.isPGroup p K
  have hQpi := solvable_isPi_of_quotient_p_complement
    T B N Tₛ hT huniq hsolv hNnormal hNleB hp K
      hKnormal hKp hKT
  have hNodd := normal_core_card_not_even
    T B N Tₛ hT huniq hNnormal hNleB hcore2
  have hNp : IsPGroup p N :=
    pGroup_of_isPi_two_prime_of_card_not_even N hp hQpi hNodd
  obtain ⟨hRnormal, hRp, hRT, hresR⟩ :=
    preimage_pGroup_and_residual T N Tₛ hT hNnormal hp hp2 hNp K
      hKnormal hKp hKT
  let qN : Q →* Q ⧸ N := QuotientGroup.mk' N
  let R : Subgroup Q := K.comap qN
  have hNR : N ≤ R := by
    intro n hn
    change qN n ∈ K
    have hnq : qN n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [hnq]
    exact K.one_mem
  have hRmap : R.map qN = K := by
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N) K
  have hRinfB : R ⊓ B = N := by
    apply le_antisymm
    · intro x hx
      have hxK : qN x ∈ K := hx.1
      have hxB : qN x ∈ B.map qN := Subgroup.mem_map_of_mem qN hx.2
      have hxbot : qN x ∈ (⊥ : Subgroup (Q ⧸ N)) := by
        rw [← hKinfB]
        exact ⟨hxK, hxB⟩
      exact (QuotientGroup.eq_one_iff x).1 hxbot
    · exact le_inf hNR hNleB
  have hRquotElem : IsElementaryAbelian p (R ⧸ N.subgroupOf R) := by
    have hImageElem : IsElementaryAbelian p (R.map qN) := by
      rw [hRmap]
      exact hKelem
    exact elementaryAbelian_of_mulEquiv p
      (quotientSubgroupRangeEquiv R N).symm hImageElem
  have hfrattini : N = (frattini R).map R.subtype :=
    normal_subgroup_eq_frattini_of_maschke T B R N Tₛ hT hB hTB huniq
      hRnormal hp hp2 hRp hNR hRinfB hRT hresR hNnormal hRquotElem
  refine ⟨p, hp, hpodd, ?_, ?_, hirred⟩
  · rw [hresR]
    exact hRp
  · rw [hresR]
    exact hfrattini

end Stellmacher.SectionThree
