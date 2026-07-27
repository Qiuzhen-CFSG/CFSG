import Mathlib
import Submission.FeitThompson.FinalTheorem
import Submission.ZStar.LocalReduction
import Submission.ZStar.CoreFree

/-!
# Quotient reduction

Reduces `glauberman_zstar_local` to `glauberman_zstar_corefree`.

## Status

The quotient reduction is complete.  The only remaining dependency of
`glauberman_zstar_local` is the core-free theorem
`glauberman_zstar_corefree`.
-/

namespace Submission.ZStar

open Subgroup
open scoped Pointwise

private lemma zpowers_subtype_eq_subgroupOf
    {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    Subgroup.zpowers (⟨x, hx⟩ : H) = (Subgroup.zpowers x).subgroupOf H := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_zpowers_iff] at hy
    change (y : G) ∈ Subgroup.zpowers x
    rw [Subgroup.mem_zpowers_iff]
    rcases hy with ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · intro hy
    change (y : G) ∈ Subgroup.zpowers x at hy
    rw [Subgroup.mem_zpowers_iff] at hy ⊢
    rcases hy with ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩

section localTheorem

variable {G : Type*} [Group G] [Finite G]
  (S : Sylow 2 G) (t : G)
  (htI : IsInvolution t)
  (htS : t ∈ (S : Subgroup G))
  (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
  (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G))

include htI htS htCentral htWeak in
/-- The image of `t` is weakly closed in the image of `S` modulo the odd core.

**Proof sketch** (see `plan.md` §7 for full details):

Let `N := pPrimeCore 2 G` (odd order), `q := QuotientGroup.mk' N`.
Suppose `q(g₀)*q(t)*q(g₀)⁻¹ ∈ (S : Subgroup G).map q`.
Then `q(g₀*t*g₀⁻¹) ∈ (S : Subgroup G).map q`, so `∃ s ∈ S, q s = q(g₀*t*g₀⁻¹)`.
Let `x := g₀*t*g₀⁻¹`.

Key steps:
1. `orderOf x = 2` (conjugacy preserves order) and `orderOf s = 2`
   (the quotient map is injective on the 2-group `S`).
2. From `q s = q x`, both `s / x` and `x / s` lie in `N`.
3. In `D := N ⊔ ⟨x⟩`, the subgroups `⟨x⟩` and `⟨s⟩` both complement the
   normal odd-order subgroup `N ∩ D`.  Hence both have odd index and are
   Sylow 2-subgroups of `D`.
4. Sylow conjugacy gives `∃ d ∈ D, d·x·d⁻¹ = s`.
5. Thus `s` is a `G`-conjugate of `t` lying in `S`; weak closure forces `s = t`.
6. Hence `q(g₀*t*g₀⁻¹) = q s = q t`. ∎
-/
theorem weaklyClosed_image_pPrimeCore :
    IsWeaklyClosedInSylow
      (QuotientGroup.mk' (pPrimeCore 2 G) t)
      ((S : Subgroup G).map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := pPrimeCore 2 G
  have hNnormal : N.Normal := by
    dsimp [N]
    exact pPrimeCore_normal
  letI : N.Normal := hNnormal
  let q : G →* G ⧸ N := QuotientGroup.mk' N

  have hqSinj : Function.Injective (q.comp (S : Subgroup G).subtype) := by
    simpa [q, N] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := G) (p := 2) (H := (S : Subgroup G)) S.isPGroup'
  let tS : (S : Subgroup G) := ⟨t, htS⟩
  have htOrder : orderOf t = 2 := orderOf_eq_prime htI.2 htI.1
  have hqtOrder : orderOf (q t) = 2 := by
    calc
      orderOf (q t) = orderOf ((q.comp (S : Subgroup G).subtype) tS) := rfl
      _ = orderOf tS := orderOf_injective _ hqSinj tS
      _ = orderOf t := (Subgroup.orderOf_coe tS).symm
      _ = 2 := htOrder

  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨t, htS, rfl⟩
  · intro gbar
    refine QuotientGroup.induction_on gbar ?_
    intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨s, hsS, hqs⟩
    let x : G := g * t * g⁻¹
    have hqsx : q s = q x := by
      simpa [q, x] using hqs

    have hxOrder : orderOf x = 2 := by
      calc
        orderOf x = orderOf ((MulAut.conj g) t) := by rw [MulAut.conj_apply]
        _ = orderOf t :=
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
        _ = 2 := htOrder
    have hqxOrder : orderOf (q x) = 2 := by
      calc
        orderOf (q x) = orderOf ((MulAut.conj (q g)) (q t)) := by
          simp [q, x, MulAut.conj_apply]
        _ = orderOf (q t) :=
          orderOf_injective (MulAut.conj (q g)).toMonoidHom
            (MulAut.conj (q g)).injective (q t)
        _ = 2 := hqtOrder

    let sS : (S : Subgroup G) := ⟨s, hsS⟩
    have hsOrder : orderOf s = 2 := by
      calc
        orderOf s = orderOf sS := Subgroup.orderOf_coe sS
        _ = orderOf ((q.comp (S : Subgroup G).subtype) sS) :=
          (orderOf_injective _ hqSinj sS).symm
        _ = orderOf (q s) := rfl
        _ = orderOf (q x) := congrArg orderOf hqsx
        _ = 2 := hqxOrder

    let D : Subgroup G := N ⊔ Subgroup.zpowers x
    have hNleD : N ≤ D := by
      exact le_sup_left
    have hxD : x ∈ D := by
      change x ∈ N ⊔ Subgroup.zpowers x
      exact (show Subgroup.zpowers x ≤ N ⊔ Subgroup.zpowers x from le_sup_right)
        (Subgroup.mem_zpowers x)
    have hsDivX_N : s / x ∈ N :=
      (QuotientGroup.eq_iff_div_mem (N := N)).mp hqsx
    have hsD : s ∈ D := by
      have hprod := D.mul_mem (hNleD hsDivX_N) hxD
      simpa only [div_mul_cancel] using hprod

    let ND : Subgroup D := N.subgroupOf D
    have hNDnormal : ND.Normal := hNnormal.subgroupOf D
    letI : ND.Normal := hNDnormal
    let xD : D := ⟨x, hxD⟩
    let sD : D := ⟨s, hsD⟩
    let X : Subgroup D := Subgroup.zpowers xD
    let T : Subgroup D := Subgroup.zpowers sD

    have hxDOrder : orderOf xD = 2 := by
      rw [← Subgroup.orderOf_coe xD]
      exact hxOrder
    have hsDOrder : orderOf sD = 2 := by
      rw [← Subgroup.orderOf_coe sD]
      exact hsOrder
    have hXcard : Nat.card X = 2 := by
      simpa [X] using (Nat.card_zpowers xD).trans hxDOrder
    have hTcard : Nat.card T = 2 := by
      simpa [T] using (Nat.card_zpowers sD).trans hsDOrder

    have hNodd : Odd (Nat.card N) := by
      rw [← Nat.coprime_two_left]
      simpa [N] using pPrimeCore_coprime_card (p := 2) (G := G)
    have hNDcard : Nat.card ND = Nat.card N := by
      simpa [ND] using Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleD).toEquiv
    have hNDodd : Odd (Nat.card ND) := by
      rw [hNDcard]
      exact hNodd

    have hXsub : X = (Subgroup.zpowers x).subgroupOf D := by
      simpa [X, xD] using zpowers_subtype_eq_subgroupOf hxD
    have hNDXtop : ND ⊔ X = ⊤ := by
      calc
        ND ⊔ X = N.subgroupOf D ⊔ (Subgroup.zpowers x).subgroupOf D := by
          rw [hXsub]
        _ = (N ⊔ Subgroup.zpowers x).subgroupOf D :=
          (Subgroup.subgroupOf_sup hNleD (by exact le_sup_right)).symm
        _ = D.subgroupOf D := by rfl
        _ = ⊤ := Subgroup.subgroupOf_self D

    have hxsN : x / s ∈ N :=
      (QuotientGroup.eq_iff_div_mem (N := N)).mp hqsx.symm
    let nD : D := ⟨x / s, hNleD hxsN⟩
    have hnD_ND : nD ∈ ND := by
      exact hxsN
    have hsD_T : sD ∈ T := Subgroup.mem_zpowers sD
    have hxD_NDT : xD ∈ ND ⊔ T := by
      have hprod := Subgroup.mul_mem_sup hnD_ND hsD_T
      simpa [nD, xD, sD] using hprod
    have hX_le_NDT : X ≤ ND ⊔ T := by
      exact Subgroup.zpowers_le.mpr hxD_NDT
    have hNDTtop : ND ⊔ T = ⊤ := by
      apply top_unique
      rw [← hNDXtop]
      exact sup_le le_sup_left hX_le_NDT

    have hNDXcop : Nat.Coprime (Nat.card ND) (Nat.card X) := by
      rw [hXcard]
      exact Nat.coprime_two_right.mpr hNDodd
    have hNDTcop : Nat.Coprime (Nat.card ND) (Nat.card T) := by
      rw [hTcard]
      exact Nat.coprime_two_right.mpr hNDodd
    have hNDXdis : Disjoint ND X := Subgroup.disjoint_of_coprime_natCard hNDXcop
    have hNDTdis : Disjoint ND T := Subgroup.disjoint_of_coprime_natCard hNDTcop

    have hNDXmul : (ND : Set D) * (X : Set D) = Set.univ := by
      rw [← Subgroup.normal_mul ND X, hNDXtop]
      rfl
    have hNDTmul : (ND : Set D) * (T : Set D) = Set.univ := by
      rw [← Subgroup.normal_mul ND T, hNDTtop]
      rfl
    have hXcomp : ND.IsComplement' X :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hNDXdis hNDXmul
    have hTcomp : ND.IsComplement' T :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hNDTdis hNDTmul

    have hXindexOdd : Odd X.index := by
      rw [hXcomp.index_eq_card]
      exact hNDodd
    have hTindexOdd : Odd T.index := by
      rw [hTcomp.index_eq_card]
      exact hNDodd
    have hXindexNot : ¬ 2 ∣ X.index :=
      Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hXindexOdd)
    have hTindexNot : ¬ 2 ∣ T.index :=
      Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hTindexOdd)
    have hXp : IsPGroup 2 X := by
      apply IsPGroup.of_card (n := 1)
      simpa using hXcard
    have hTp : IsPGroup 2 T := by
      apply IsPGroup.of_card (n := 1)
      simpa using hTcard

    let PX : Sylow 2 D := hXp.toSylow hXindexNot
    let PT : Sylow 2 D := hTp.toSylow hTindexNot
    obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D PX PT

    have hxPX : xD ∈ (PX : Subgroup D) := by
      simpa [PX, IsPGroup.toSylow_coe, X] using (Subgroup.mem_zpowers xD)
    have hyPT : d * xD * d⁻¹ ∈ (PT : Subgroup D) := by
      have hySmul : d * xD * d⁻¹ ∈ ((d • PX : Sylow 2 D) : Subgroup D) := by
        rw [Sylow.coe_subgroup_smul]
        exact Set.mem_smul_set.mpr ⟨xD, hxPX, rfl⟩
      simpa [hd] using hySmul
    have hyT : d * xD * d⁻¹ ∈ T := by
      simpa [PT, IsPGroup.toSylow_coe] using hyPT

    let yT : T := ⟨d * xD * d⁻¹, hyT⟩
    let sT : T := ⟨sD, Subgroup.mem_zpowers sD⟩
    have hyTne : yT ≠ 1 := by
      intro hy1
      have hyD1 : d * xD * d⁻¹ = 1 := congrArg Subtype.val hy1
      have hxD1 : xD = 1 := by
        apply (MulAut.conj d).injective
        simpa [MulAut.conj_apply] using hyD1
      have hx1 : x = 1 := congrArg Subtype.val hxD1
      rw [hx1] at hxOrder
      simp at hxOrder
    have hsTne : sT ≠ 1 := by
      intro hs1
      have hsD1 : sD = 1 := congrArg Subtype.val hs1
      have hs1G : s = 1 := congrArg Subtype.val hsD1
      rw [hs1G] at hsOrder
      simp at hsOrder
    have hyTsT : yT = sT :=
      ((Nat.card_eq_two_iff' (1 : T)).mp hTcard).unique hyTne hsTne
    have hyEqS : (d : G) * x * (d : G)⁻¹ = s := by
      have hval := congrArg (fun z : T => (((z : D) : G))) hyTsT
      simpa [yT, sT, xD, sD] using hval

    have hconjEqS : ((d : G) * g) * t * ((d : G) * g)⁻¹ = s := by
      calc
        ((d : G) * g) * t * ((d : G) * g)⁻¹ = (d : G) * x * (d : G)⁻¹ := by
          simp [x, mul_assoc]
        _ = s := hyEqS
    have hweak : ((d : G) * g) * t * ((d : G) * g)⁻¹ = t := by
      apply htWeak.2 ((d : G) * g)
      rw [hconjEqS]
      exact hsS
    have hsEqT : s = t := hconjEqS.symm.trans hweak
    calc
      (QuotientGroup.mk' (pPrimeCore 2 G)) g *
            (QuotientGroup.mk' (pPrimeCore 2 G)) t *
            ((QuotientGroup.mk' (pPrimeCore 2 G)) g)⁻¹ =
          (QuotientGroup.mk' (pPrimeCore 2 G)) s := hqs.symm
      _ = (QuotientGroup.mk' (pPrimeCore 2 G)) t := by rw [hsEqT]

include htI htS htCentral htWeak in
/-- **Glauberman's Z*-theorem, local form.**

Under the Sylow-local hypotheses, `t` maps to the center of `G / O_{2'}(G)`.

Reduces to `glauberman_zstar_corefree`:
1. Let `N := pPrimeCore 2 G`, `Gbar := G ⧸ N`.
2. `pPrimeCore 2 Gbar = ⊥` (by `pPrimeCore_quotient_pPrimeCore_eq_bot`).
3. Transport the Sylow subgroup to the quotient: `Sbar := S.map q` is a Sylow
   2-subgroup of `Gbar` (Sylow subgroups map to Sylow subgroups modulo a
   normal subgroup of coprime order).
4. `q t` is an involution in `Sbar`, central in `Sbar` (centrality descends).
5. Weak closure descends by `weaklyClosed_image_pPrimeCore`.
6. Apply `glauberman_zstar_corefree` in `Gbar` to get `q t ∈ Z(Gbar)`. -/
theorem glauberman_zstar_local :
    QuotientGroup.mk' (pPrimeCore 2 G) t ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := pPrimeCore 2 G
  have hNnormal : N.Normal := by
    dsimp [N]
    exact pPrimeCore_normal
  letI : N.Normal := hNnormal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Sbar : Sylow 2 (G ⧸ N) :=
    S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)

  have hqSinj : Function.Injective (q.comp (S : Subgroup G).subtype) := by
    simpa [q, N] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := G) (p := 2) (H := (S : Subgroup G)) S.isPGroup'
  let tS : (S : Subgroup G) := ⟨t, htS⟩
  have htOrder : orderOf t = 2 := orderOf_eq_prime htI.2 htI.1
  have hqtOrder : orderOf (q t) = 2 := by
    calc
      orderOf (q t) = orderOf ((q.comp (S : Subgroup G).subtype) tS) := rfl
      _ = orderOf tS := orderOf_injective _ hqSinj tS
      _ = orderOf t := (Subgroup.orderOf_coe tS).symm
      _ = 2 := htOrder
  have hqtI : IsInvolution (q t) := by
    have h := (orderOf_eq_prime_iff (x := q t) (p := 2)).mp hqtOrder
    exact ⟨h.2, h.1⟩

  have hqtSbar : q t ∈ (Sbar : Subgroup (G ⧸ N)) := by
    rw [show (Sbar : Subgroup (G ⧸ N)) = (S : Subgroup G).map q by
      simp [Sbar, Sylow.coe_mapSurjective]]
    exact Subgroup.mem_map.mpr ⟨t, htS, rfl⟩

  have hqtCentral : ∀ z, z ∈ (Sbar : Subgroup (G ⧸ N)) → z * q t = q t * z := by
    intro z hz
    have hzMap : z ∈ (S : Subgroup G).map q := by
      rw [← show (Sbar : Subgroup (G ⧸ N)) = (S : Subgroup G).map q by
        simp [Sbar, Sylow.coe_mapSurjective]]
      exact hz
    rcases Subgroup.mem_map.mp hzMap with ⟨s, hs, rfl⟩
    simpa using congrArg q (htCentral s hs)

  have hqtWeak : IsWeaklyClosedInSylow (q t) (Sbar : Subgroup (G ⧸ N)) := by
    have h := weaklyClosed_image_pPrimeCore S t htI htS htCentral htWeak
    simpa [q, N, Sbar, Sylow.coe_mapSurjective] using h

  have hcore : pPrimeCore 2 (G ⧸ N) = ⊥ := by
    simpa [N] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := 2))
  have hcenter :=
    glauberman_zstar_corefree hcore Sbar (q t) hqtI hqtSbar hqtCentral hqtWeak
  simpa [q, N] using hcenter

end localTheorem

end Submission.ZStar
