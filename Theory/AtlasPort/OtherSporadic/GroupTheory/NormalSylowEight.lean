/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/NormalSylowEight.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.Sylow

/-!
# NormalSylowEight

Sylow arithmetic restricts normal subgroups of order 336 in primitive degree 21.
A unique Sylow seven subgroup would be characteristic and hence impossibly transitive.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/NormalSylowEight.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.GroupTheory
open MulAction
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem transitive_degree_dvd {G X : Type*} [Group G] [MulAction G X]
    [IsPretransitive G X] (x : X) : Nat.card X ∣ Nat.card G := by
  have he : orbit G x ≃ X := Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
    intro y
    exact ⟨⟨y,mem_orbit_iff.mpr (exists_smul_eq G x y)⟩,rfl⟩⟩
  have h := Nat.card_congr (orbitProdStabilizerEquivGroup G x)
  rw [Nat.card_prod,Nat.card_congr he] at h
  exact ⟨Nat.card (stabilizer G x),h.symm⟩

theorem characteristic_in_normal {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (P : Subgroup N) [P.Characteristic] :
    (P.map N.subtype).Normal := by
  constructor
  rintro _ ⟨p,hp,rfl⟩ g
  have hh : MulAut.conjNormal g p ∈ P := by
    have h := (inferInstance : P.Characteristic).fixed (MulAut.conjNormal g)
    have hm : p ∈ P.comap (MulAut.conjNormal g).toMonoidHom := by rwa [h]
    exact hm
  exact ⟨MulAut.conjNormal g p,hh,rfl⟩

theorem sylow_seven_card_of_336 {N : Type*} [Group N] [Finite N]
    (hn : Nat.card N = 336) (P : Sylow 7 N) : Nat.card P = 7 := by
  rw [Sylow.card_eq_multiplicity,hn]
  rw [show 336 = 7 * 48 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 7 48),
    (by decide : Nat.Prime 7).factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 48)]
  norm_num

theorem sylow_seven_count_of_336 {N : Type*} [Group N] [Finite N]
    (hn : Nat.card N = 336) : Nat.card (Sylow 7 N) = 1 ∨ Nat.card (Sylow 7 N) = 8 := by
  let P : Sylow 7 N := Classical.choice inferInstance
  have hp := sylow_seven_card_of_336 hn P
  have hi : P.index = 48 := by
    have h := P.toSubgroup.card_mul_index
    rw [hp,hn] at h
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hm := card_sylow_modEq_one 7 N
  have hb : Nat.card (Sylow 7 N) ≤ 48 := Nat.le_of_dvd (by decide) hd
  have hmod : Nat.card (Sylow 7 N) % 7 = 1 := hm
  interval_cases h : Nat.card (Sylow 7 N) <;> omega

theorem normal_336_has_eight_sylow {G X : Type*} [Group G] [Finite G]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    (x : X) (hx : Nat.card X = 21) (N : Subgroup G) [N.Normal]
    (hn : Nat.card N = 336) : Nat.card (Sylow 7 N) = 8 := by
  rcases sylow_seven_count_of_336 hn with hs | hs
  · have : Subsingleton (Sylow 7 N) := (Nat.card_eq_one_iff_unique.mp hs).1
    let P : Sylow 7 N := Classical.choice inferInstance
    let Q := P.toSubgroup.map N.subtype
    have : Q.Normal := characteristic_in_normal N P.toSubgroup
    have hq : Nat.card Q = 7 := by
      rw [← Nat.card_congr (P.toSubgroup.equivMapOfInjective N.subtype
        Subtype.val_injective).toEquiv]
      exact sylow_seven_card_of_336 hn P
    have hne : Q ≠ ⊥ := by intro h; rw [h,Subgroup.card_bot] at hq; omega
    have : IsPretransitive Q X := normal_pretransitive Q hne
    have hd := transitive_degree_dvd (G := Q) x
    rw [hx,hq] at hd
    norm_num at hd
  · exact hs

end Atlas.GroupTheory
