module

public import CFSG.Quasithin.ChapterE.Section01.ReverseLift.Preparation
public import Theory.GroupTheory.PCoreSurjective.OddExtension
/-!
# Odd-case preservation under residual--tau shrinking

For an odd E-member `I`, the smaller subgroup `O²(I)τ(I,T ∩ I,A)`
retains the odd-core commutator and rank-one conditions, and its prescribed
Sylow intersection equals its intrinsic tau.

Modulo `O₂(I)`, the odd core is the two-residual. Coprime subgroup
intersection then gives `S ∩ O²(I) ≤ O₂(I) ≤ τ(S,B)`, hence
`S ∩ (O²(I)τ(S,B)) = τ(S,B)`. Restricting the quotient map has a two-group
kernel; the odd-extension theorem transfers the odd core and actor rank.
Finally the actual embedding into the ambient group transports every clause.

This discharges the shrinking premise of the odd branch of E.1.10(7).
Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
proof of E.1.10(7), printed pp.211--212 (1 March 2004 manuscript).
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A normal odd core with two-group quotient is exactly the two-residual. -/
private theorem odd_core_residual {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hq : IsPGroup 2 (G ⧸ pCore p G)) : pResidual 2 G = pCore p G := by
  refine le_antisymm ?_ ?_
  · exact sInf_le ⟨inferInstance, hq⟩
  apply le_sInf
  rintro N ⟨hN, hQ⟩
  let := hN
  let q := QuotientGroup.mk' N
  have hz : (pCore p G).map q = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne p 2 hp _ _ (pCore_isPGroup.map q) (hQ.to_subgroup _))
  simpa only [q, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

/-- Shrinking cuts the prescribed Sylow subgroup down to its original local tau. -/
private theorem residual_tau_intersection (S : Sylow 2 G) (B : Subgroup G)
    [IsElementaryAbelian 2 B] (hBS : B ≤ (S : Subgroup G))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hq : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ pCore p (G ⧸ pCore 2 G))) :
    (S : Subgroup G) ⊓ (pResidual 2 G ⊔ tau (S : Subgroup G) B) =
      tau (S : Subgroup G) B := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hr : (pResidual 2 G).map q = pCore p (G ⧸ pCore 2 G) := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    exact odd_core_residual hp hq
  have hi : (S : Subgroup G) ⊓ pResidual 2 G ≤ pCore 2 G := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_ne 2 p hp.symm _ _ (S.isPGroup'.map q) pCore_isPGroup)
        (mem_map_of_mem q hx.1)
    rw [← hr]
    exact mem_map_of_mem q hx.2
  have hD : pCore 2 G ≤ tau (S : Subgroup G) B :=
    le_sup_right.trans (sup_pCore_le_tau S B hBS)
  apply le_antisymm ?_ (le_inf (tau_le _ _) le_sup_right)
  rintro x ⟨hxS, hxL⟩
  obtain ⟨r, hr, d, hd, rfl⟩ := mem_sup_of_normal_left.mp hxL
  have hrS : r ∈ (S : Subgroup G) := by
    simpa only [mul_inv_cancel_right] using
      (S : Subgroup G).mul_mem hxS ((S : Subgroup G).inv_mem (tau_le _ _ hd))
  exact (tau (S : Subgroup G) B).mul_mem (hD (hi ⟨hrS, hr⟩)) hd

/-- Intrinsic shrinking before embedding back into the original ambient group. -/
private theorem residual_tau_intrinsic (S B : Subgroup G)
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    [IsElementaryAbelian 2 B] (hBS : B ≤ S)
    {p : ℕ} (hpprime : p.Prime) (hpodd : Odd p)
    (hq : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ pCore p (G ⧸ pCore 2 G)))
    (hne : pCore p (G ⧸ pCore 2 G) ≠ ⊥)
    (hcomm : pCore p (G ⧸ pCore 2 G) = ⁅pCore p (G ⧸ pCore 2 G),
      B.map (QuotientGroup.mk' (pCore 2 G))⁆)
    (hrank : Group.rank (B.map (QuotientGroup.mk' (pCore 2 G))) = 1) :
    let L := pResidual 2 G ⊔ tau S B
    ECaseOdd B L ∧ tau (S.subgroupOf L) (B.subgroupOf L) =
      S.subgroupOf L := by
  let : Fact p.Prime := ⟨hpprime⟩
  have hp : p ≠ 2 := by rintro rfl; norm_num at hpodd
  let D := tau S B
  let L := pResidual 2 G ⊔ D
  let q := QuotientGroup.mk' (pCore 2 G)
  let P := pCore p (G ⧸ pCore 2 G)
  let H := L.map q
  let f : L →* H := q.subgroupMap L
  have hf : Function.Surjective f := q.subgroupMap_surjective L
  have hBD : B ⊔ pCore 2 G ≤ D := by
    dsimp only [D]
    obtain ⟨P, hP⟩ := hS
    rw [← hP] at hBS ⊢
    exact sup_pCore_le_tau P B hBS
  have hBL : B ≤ L := (le_sup_left.trans hBD).trans le_sup_right
  have hr : (pResidual 2 G).map q = P := by
    rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
    exact odd_core_residual hp hq
  have hPH : P ≤ H := hr ▸ map_mono (f := q) (show pResidual 2 G ≤ L from le_sup_left)
  have hker : f.ker = (pCore 2 G).subgroupOf L := by
    ext x
    change (f x = 1) ↔ (x : G) ∈ pCore 2 G
    rw [← Subtype.val_inj]
    exact QuotientGroup.eq_one_iff (x : G)
  have hk : IsPGroup 2 f.ker := hker ▸ pCore_isPGroup.comap_subtype
  let N := P.subgroupOf H
  have hNmap : N.map H.subtype = P := map_subgroupOf_eq_of_le hPH
  have hBmap : ((B.subgroupOf L).map f).map H.subtype = B.map q := by
    rw [map_map]
    change (B.subgroupOf L).map (q.comp L.subtype) = B.map q
    rw [← map_map, map_subgroupOf_eq_of_le hBL]
  have hNq : IsPGroup 2 (H ⧸ N) := by
    let g := (QuotientGroup.mk' P).comp H.subtype
    have hNg : N = g.ker := by
      ext x
      exact (QuotientGroup.eq_one_iff (N := P) (x : G ⧸ pCore 2 G)).symm
    exact (hq.to_subgroup g.range).of_equiv
      ((QuotientGroup.quotientKerEquivRange g).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hNg.symm))
  have hNne : N ≠ ⊥ := by
    intro hz
    apply hne
    change P = ⊥
    rw [← hNmap, hz, Subgroup.map_bot]
  have hNc : N = ⁅N, (B.subgroupOf L).map f⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, hNmap, hBmap]
    exact hcomm
  have hBr : Group.rank ((B.subgroupOf L).map f) = 1 := by
    rw [← hrank]
    exact Group.rank_congr
      ((((B.subgroupOf L).map f).equivMapOfInjective H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr hBmap))
  have hodd := odd_quotient_commutator_rank_of_surjective hp f hf hk N
    (B.subgroupOf L) pCore_isPGroup.comap_subtype hNq hNne hNc hBr
  refine ⟨⟨p, hpprime, hpodd, hodd⟩, ?_⟩
  have hi : S ⊓ L = D := by
    obtain ⟨P, hP⟩ := hS
    dsimp only [L, D]
    rw [← hP] at hBS ⊢
    exact residual_tau_intersection P B hBS hp hq
  apply le_antisymm (tau_le _ _) ?_
  intro x hx
  have hxD : (x : G) ∈ D := hi.le ⟨hx, x.property⟩
  obtain ⟨_, hc⟩ := mem_centralizerModulo_iff.mp hxD
  apply mem_centralizerModulo_iff.mpr
  refine ⟨hx, fun b hb => ?_⟩
  have hcore : (pCore 2 G).subgroupOf L ≤ pCore 2 L :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  exact hcore (hc b hb)

/-- The odd E-case survives the source residual--tau shrinking, and the
restricted Sylow subgroup is its own local tau. -/
public theorem IsEMember.residualTau_odd_data {T A I : Subgroup G}
    (h0 : IsEMember T A I) (ho : ECaseOdd A I) :
    let R := residualTau T A I
    let Q := R ⧸ pCore 2 R
    let a := (A.subgroupOf R).map (QuotientGroup.mk' (pCore 2 R))
    let s := T.subgroupOf R
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup 2 (Q ⧸ pCore p Q) ∧
      pCore p Q ≠ ⊥ ∧ pCore p Q = ⁅pCore p Q, a⁆ ∧ Group.rank a = 1 ∧
      tau s (A.subgroupOf R) = s := by
  let B := A.subgroupOf I
  let L := pResidual 2 I ⊔ tau (T.subgroupOf I) B
  let R := residualTau T A I
  let e : L ≃* R := L.equivMapOfInjective I.subtype I.subtype_injective
  let := h0.1
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf h0.2.2.1
  have hBS : B ≤ T.subgroupOf I := subgroupOf_mono I h0.2.1
  obtain ⟨p, hp, hpodd, hq, hn, hc, hr⟩ := ho
  have hd := residual_tau_intrinsic (T.subgroupOf I) B h0.2.2.2.2.1
    hBS hp hpodd hq hn hc hr
  have hodd : ECaseOdd B L := hd.1
  have hoddR : ECaseOdd A R := by
    have hh := hodd.map_injective I.subtype I.subtype_injective
    rwa [map_subgroupOf_eq_of_le h0.2.2.1] at hh
  have hB : (B.subgroupOf L).map e.toMonoidHom = A.subgroupOf R := by
    have hh := intrinsic_subgroupOf_map I.subtype I.subtype_injective B L
    rwa [map_subgroupOf_eq_of_le h0.2.2.1] at hh
  have hSmap : ((T.subgroupOf I).subgroupOf L).map e.toMonoidHom =
      T.subgroupOf R := by
    calc
      _ = ((T.subgroupOf I).map I.subtype).subgroupOf R :=
        intrinsic_subgroupOf_map I.subtype I.subtype_injective (T.subgroupOf I) L
      _ = T.subgroupOf R := by
        rw [subgroupOf_map_subtype]
        ext x
        change ((x : G) ∈ T ∧ (x : G) ∈ I) ↔ (x : G) ∈ T
        exact ⟨And.left, fun hx => ⟨hx, residualTau_le T A I x.property⟩⟩
  have htau := congrArg (Subgroup.map e.toMonoidHom) hd.2
  rw [map_tau_equiv, hB, hSmap] at htau
  obtain ⟨r, hrprime, hrodd, hquot, hnon, hcomm, hrank⟩ := hoddR
  exact ⟨r, hrprime, hrodd, hquot, hnon, hcomm, hrank, htau⟩

end CFSG.Quasithin.ChapterE
