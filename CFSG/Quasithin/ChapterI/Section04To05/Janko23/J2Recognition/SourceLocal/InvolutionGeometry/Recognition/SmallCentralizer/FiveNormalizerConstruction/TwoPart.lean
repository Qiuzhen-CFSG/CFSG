module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConsequences
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The two-part of the ambient five-normalizer

For the source Sylow subgroup P of H = C_G(z), an isomorphism N_H(P) ≃ D₂₀
implies that C_H(P) has order ten. This is checked on a generator of P in
the dihedral model. The Sylow normalizer congruence then makes ⟨z⟩ a Sylow
two-subgroup of C_G(P): its normalizer there is its centralizer, of order ten.

Inside N_G(P), the centralizer C_G(P) is normal. Frattini's argument shows
that it and C_{N_G(P)}(z) generate N_G(P). Their intersection has order ten
and the latter group has order twenty, so C_G(P) has index two in N_G(P).
Consequently the ambient normalizer has two-part four. All transports below
use the literal subgroup inclusions defining `ambientFive` and `fiveNormalizer`.
The local dihedral isomorphism remains the sole additional premise.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, printed p.260.
-/

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem dihedral_five_centralizer (a : DihedralGroup 10) (ha : orderOf a = 5) :
    Nat.card (centralizer ({a} : Set (DihedralGroup 10))) = 10 := by
  have table : ∀ a : DihedralGroup 10, a ^ 5 = 1 → a ≠ 1 →
      Fintype.card {b : DihedralGroup 10 // b * a = a * b} = 10 := by
    decide +kernel
  have hp : a ^ 5 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hne : a ≠ 1 := by intro hh; simp [hh] at ha
  calc
    Nat.card (centralizer ({a} : Set (DihedralGroup 10))) =
        Nat.card {b : DihedralGroup 10 // b * a = a * b} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_centralizer_singleton_iff)
    _ = 10 := by rw [Nat.card_eq_fintype_card]; exact table a hp hne

private theorem card_centralizer_equiv {B E : Type*} [Group B] [Group E]
    (e : B ≃* E) (a : B) :
    Nat.card (centralizer ({a} : Set B)) = Nat.card (centralizer ({e a} : Set E)) := by
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv _)
  intro b
  simp only [mem_centralizer_singleton_iff]
  change b * a = a * b ↔ e b * e a = e a * e b
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

private theorem local_centralizer_card {B : Type*} [Group B] [Finite B]
    (P : Subgroup B) (hP : Nat.card P = 5)
    (e : normalizer (P : Set B) ≃* DihedralGroup 10) :
    Nat.card (centralizer (P : Set B)) = 10 := by
  obtain ⟨p, hp⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  have hgen : zpowers (p : B) = P := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr p.property)
    rw [Nat.card_zpowers, orderOf_coe, hp, hP]
  let N := normalizer (P : Set B)
  let a : N := ⟨p, le_normalizer p.property⟩
  have hC : centralizer (P : Set B) = centralizer ({(p : B)} : Set B) := by
    calc
      centralizer (P : Set B) = centralizer (zpowers (p : B) : Set B) :=
        congrArg (fun U : Subgroup B => centralizer (U : Set B)) hgen.symm
      _ = _ := by rw [zpowers_eq_closure, centralizer_closure]
  have hsub : (centralizer (P : Set B)).subgroupOf N = centralizer ({a} : Set N) := by
    ext b
    rw [mem_subgroupOf, hC]
    simp only [mem_centralizer_singleton_iff, Subtype.ext_iff]
    rfl
  calc
    Nat.card (centralizer (P : Set B)) =
        Nat.card ((centralizer (P : Set B)).subgroupOf N) :=
      (Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P : Set B))).toEquiv).symm
    _ = Nat.card (centralizer ({e a} : Set (DihedralGroup 10))) := by
      rw [hsub, card_centralizer_equiv e a]
    _ = 10 := dihedral_five_centralizer (e a) (by
      rw [e.orderOf_eq, ← orderOf_coe a]
      exact (orderOf_coe p).trans hp)

private theorem centralizer_card_swap {B : Type*} [Group B] [Finite B]
    (K : Subgroup B) (z : K) :
    Nat.card (centralizer ({z} : Set K)) =
      Nat.card (K.subgroupOf (centralizer ({(z : B)} : Set B))) := by
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨⟨x.val.val, ?_⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val, x.property⟩, ?_⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl }
  · exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))
  · exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))

private theorem twoPart_of_centralizers {B : Type*} [Group B] [Finite B]
    (K : Subgroup B) [K.Normal] (z : K)
    (hz : orderOf z = 2)
    (hlocal : Nat.card (centralizer ({(z : B)} : Set B)) = 20)
    (hfixed : Nat.card (centralizer ({z} : Set K)) = 10) :
    (Nat.card B).factorization 2 = 2 := by
  let Z := zpowers z
  have hZ : Nat.card Z = 2 := by simpa [Z] using hz
  have hn : normalizer (Z : Set K) = centralizer ({z} : Set K) :=
    normalizer_zpowers_eq_centralizer_of_order_two z hz
  have hi : Z.relIndex (normalizer (Z : Set K)) = 5 := by
    have hc := (Z.subgroupOf (normalizer (Z : Set K))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_normalizer (H := Z))).toEquiv,
      hZ, hn, hfixed] at hc
    change 2 * Z.relIndex (centralizer ({z} : Set K)) = 10 at hc
    rw [hn]
    omega
  have hc := Sylow.card_quotient_normalizer_modEq_card_quotient
    (p := 2) (n := 1) (H := Z) (by simpa using hZ)
  change Z.relIndex (normalizer (Z : Set K)) ≡ Z.index [MOD 2] at hc
  have hind : ¬ 2 ∣ Z.index := by
    intro hd
    have := (hc.dvd_iff dvd_rfl).mpr hd
    rw [hi] at this
    norm_num at this
  let S : Sylow 2 K := (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hZ)).toSylow hind
  have hKpart : (Nat.card K).factorization 2 = 1 := by
    have hs := S.card_eq_multiplicity
    change Nat.card Z = 2 ^ (Nat.card K).factorization 2 at hs
    rw [hZ] at hs
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hs.symm)
  have hmap : (S : Subgroup K).map K.subtype = zpowers (z : B) :=
    MonoidHom.map_zpowers K.subtype z
  have hsup := S.normalizer_sup_eq_top
  rw [hmap, normalizer_zpowers_eq_centralizer_of_order_two (z : B)
    ((orderOf_coe z).trans hz)] at hsup
  have hrel : K.relIndex (centralizer ({(z : B)} : Set B)) = 2 := by
    have hh := (K.subgroupOf (centralizer ({(z : B)} : Set B))).card_mul_index
    rw [← centralizer_card_swap K z, hfixed, hlocal] at hh
    change 10 * K.relIndex (centralizer ({(z : B)} : Set B)) = 20 at hh
    omega
  have hindex : K.index = 2 := by
    rw [← relIndex_top_right, ← hsup, relIndex_sup_right, hrel]
  rw [← K.card_mul_index, hindex,
    Nat.factorization_mul Nat.card_pos.ne' (by decide), Finsupp.add_apply, hKpart]
  norm_num [Nat.prime_two.factorization]

variable {G : Type*} [Group G] [Finite G]

/-- The source local dihedral normalizer forces the ambient normalizer's
order to have two-part four, without an assumption on the ambient group order. -/
public theorem fiveNormalizer_twoPart_of_local_dihedral (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z))
    (e : normalizer ((P : Subgroup (involutionCentralizer D.z)) : Set (involutionCentralizer D.z)) ≃*
      DihedralGroup 10) :
    (Nat.card (fiveNormalizer D P)).factorization 2 = 2 := by
  have hP : Nat.card P = 5 := by
    have hc := ambientFive_card D P
    rwa [ambientFive, card_map_of_injective
      (involutionCentralizer D.z).subtype_injective] at hc
  have hPc := local_centralizer_card (P : Subgroup (involutionCentralizer D.z)) hP e
  let H := involutionCentralizer D.z
  let A := ambientFive D P
  let N := fiveNormalizer D P
  let C := centralizer (A : Set G)
  let K := C.subgroupOf N
  let : K.Normal := normal_subgroupOf_centralizer_normalizer (A : Set G)
  have hAH : A ≤ H := map_subtype_le _
  have hzC : D.z ∈ C := by
    intro p hp
    exact mem_centralizer_singleton_iff.mp (hAH hp)
  have hzN : D.z ∈ N := centralizer_le_normalizer (A : Set G) hzC
  let zK : K := ⟨⟨D.z, hzN⟩, hzC⟩
  have hzK : orderOf zK = 2 := by
    rw [← orderOf_coe zK, ← orderOf_coe (zK : N)]
    exact D.localType.involution
  have hNH : N.comap H.subtype = normalizer ((P : Subgroup H) : Set H) := by
    rw [show N = normalizer (A : Set G) from rfl,
      comap_normalizer_eq_of_le_range (hAH.trans_eq H.range_subtype.symm)]
    exact congrArg (fun U : Subgroup H => normalizer (U : Set H))
      (comap_map_eq_self_of_injective H.subtype_injective _)
  have hCH : C.comap H.subtype = centralizer ((P : Subgroup H) : Set H) := by
    ext x
    constructor
    · intro hx p hp
      exact Subtype.ext (hx (p : G) (mem_map_of_mem H.subtype hp))
    · intro hx a ha
      obtain ⟨p, hp, rfl⟩ := ha
      exact congrArg Subtype.val (hx p hp)
  have hlocal : Nat.card (centralizer ({(zK : N)} : Set N)) = 20 := by
    have he : centralizer ({(zK : N)} : Set N) ≃ N.comap H.subtype := {
      toFun := fun x => ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
        x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
    rw [Nat.card_congr he, hNH, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hfixed : Nat.card (centralizer ({zK} : Set K)) = 10 := by
    have he : centralizer ({zK} : Set K) ≃ C.comap H.subtype := {
      toFun := fun x => ⟨⟨x.val.val.val, mem_centralizer_singleton_iff.mpr
        (congrArg (fun y : K => ((y : N) : G))
          (mem_centralizer_singleton_iff.mp x.property))⟩, x.val.property⟩
      invFun := fun x => ⟨⟨⟨x.val.val,
        centralizer_le_normalizer (A : Set G) x.property⟩, x.property⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property)))⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
    rw [Nat.card_congr he, hCH]
    exact hPc
  exact twoPart_of_centralizers K zK hzK hlocal hfixed

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
