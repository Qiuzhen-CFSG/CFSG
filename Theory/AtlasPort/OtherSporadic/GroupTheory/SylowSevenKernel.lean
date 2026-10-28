/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/SylowSevenKernel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalSylowEight

/-!
# SylowSevenKernel

The permutation action on Sylow seven subgroups constrains its kernel.
Sylow counting and subgroup-order bounds yield the needed obstruction.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/SylowSevenKernel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem order_seven_not_fix_all_sylow {N : Type*} [Group N] [Finite N]
    (hn : Nat.card N = 336) (hs : Nat.card (Sylow 7 N) = 8)
    (u : N) (hu : orderOf u = 7) (fixed : ∀ Q : Sylow 7 N, u • Q = Q) : False := by
  let P := Subgroup.zpowers u
  have hp : Nat.card P = 7 := by rw [Nat.card_zpowers,hu]
  have hpg : IsPGroup 7 P := IsPGroup.of_card (n := 1) (by simpa using hp)
  have hall (Q : Sylow 7 N) : P = Q.toSubgroup := by
    have hnorm : P ≤ Subgroup.normalizer Q :=
      (Subgroup.zpowers_le).mpr ((Sylow.smul_eq_iff_mem_normalizer).mp (fixed Q))
    have hle : P ≤ Q := by
      have h := hpg.inf_normalizer_sylow Q
      rw [inf_eq_left.mpr hnorm] at h
      exact inf_eq_left.mp h.symm
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hp,sylow_seven_card_of_336 hn Q])
  have : Subsingleton (Sylow 7 N) := ⟨fun Q R => Sylow.ext ((hall Q).symm.trans (hall R))⟩
  have hc : Nat.card (Sylow 7 N) = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance,inferInstance⟩
  omega

noncomputable def normalSylowSevenPermutation {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] : G →* Equiv.Perm (Sylow 7 N) :=
  (MulAction.toPermHom (MulAut N) (Sylow 7 N)).comp MulAut.conjNormal

theorem normalSylowSevenPermutation_injective {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    (x : X) (hx : Nat.card X = 21) (hG : Nat.card G = 20160)
    (N : Subgroup G) [N.Normal] (hn : Nat.card N = 336) :
    Function.Injective (normalSylowSevenPermutation N) := by
  let R := (normalSylowSevenPermutation N).ker
  apply (normalSylowSevenPermutation N).ker_eq_bot_iff.mp
  by_contra hR
  have : IsPretransitive R X := normal_pretransitive R hR
  have hd := transitive_degree_dvd (G := R) x
  rw [hx] at hd
  have h7 : 7 ∣ Nat.card R := dvd_trans (by decide : 7 ∣ 21) hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := R) 7 h7
  have hindex : N.index = 60 := by
    have h := N.card_mul_index
    rw [hn,hG] at h
    omega
  have hquot : Nat.card (G ⧸ N) = 60 := by rwa [Subgroup.index_eq_card] at hindex
  have hupow : u.val ^ 7 = 1 := by
    exact congrArg Subtype.val (hu ▸ pow_orderOf_eq_one u)
  have huN : u.val ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply orderOf_eq_one_iff.mp
    have hpow : (QuotientGroup.mk' N u.val)^7 = 1 := by rw [← map_pow,hupow,map_one]
    have hcard := orderOf_dvd_natCard (QuotientGroup.mk' N u.val)
    rw [hquot] at hcard
    exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 7 60)
      (orderOf_dvd_of_pow_eq_one hpow) hcard
  let v : N := ⟨u.val,huN⟩
  have hv : orderOf v = 7 := by
    exact (Subgroup.orderOf_mk _ _).trans ((Subgroup.orderOf_coe u).trans hu)
  apply order_seven_not_fix_all_sylow hn (normal_336_has_eight_sylow x hx N hn) v hv
  intro Q
  have hf : normalSylowSevenPermutation N u.val = 1 := u.prop
  have hh := congrArg (fun σ : Equiv.Perm (Sylow 7 N) => σ Q) hf
  change (MulAut.conjNormal u.val : MulAut N) • Q = Q at hh
  change (MulAut.conj v : MulAut N) • Q = Q
  rwa [show u.val = (v : G) from rfl,MulAut.conjNormal_val] at hh

end Atlas.GroupTheory
