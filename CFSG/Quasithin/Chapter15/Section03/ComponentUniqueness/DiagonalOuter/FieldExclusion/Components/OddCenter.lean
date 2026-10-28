module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Centralizer

/-!
# Bounding component centers from the actual field residual

A perfect subgroup centralizes a normal group of order dividing nine,
since its automorphism group is solvable. The simple PSL₃(2) residual meets
the small odd core trivially. If that odd core contained an elementary nine,
an order-three element of the residual would produce three-rank at least
three. Thus the odd core has three-rank at most one. The odd cores of
subnormal subgroups embed in the ambient odd core, giving the same bound
for every component center.

This is the center bound used by `Selection`, proved from the inputs on
Aschbacher--Smith, combined manuscript of 1 March 2004, printed p.1137.
It avoids an additional hypothesis about Schur multipliers. The action
argument uses the elementary order-nine automorphism theorem, as in `Layer`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G] [Finite G]

private theorem aut_solvable_of_card_dvd_nine {D : Type*} [Group D] [Finite D]
    (hD : Nat.card D ∣ 9) : Group.IsSolvable (MulAut D) := by
  have hc : Nat.card D = 1 ∨ Nat.card D = 3 ∨ Nat.card D = 9 := by
    have hd : Nat.card D ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hD, by decide⟩
    have he : Nat.divisors 9 = {1, 3, 9} := by decide
    simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hd
  rcases hc with h | h | h
  · let : Subsingleton D := (Nat.card_eq_one_iff_unique.mp h).1
    exact Group.isSolvable_of_comm (fun a b => by ext x; exact Subsingleton.elim _ _)
  · let : IsCyclic D := isCyclic_of_prime_card h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv D).toMonoidHom) (IsCyclic.mulAutMulEquiv D).injective
  · exact MulAut.isSolvable_of_card_nine h

private theorem simple_subgroup_centralizes_small_normal
    (F N : Subgroup G) [IsSimpleGroup F] [Group.IsPerfect F] [N.Normal]
    (hc : Nat.card N ∣ 9) : F ≤ centralizer (N : Set G) := by
  let : Group.IsSolvable (MulAut N) := aut_solvable_of_card_dvd_nine hc
  let φ : F →* MulAut N := (MulAut.conjNormal : G →* MulAut N).comp F.subtype
  have ht : φ = 1 := by
    let : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hb : φ.range = ⊥ := by
      by_contra hb
      let : Nontrivial φ.range := (nontrivial_iff_ne_bot _).mpr hb
      exact Group.IsPerfect.not_isSolvable φ.range inferInstance
    exact MonoidHom.range_eq_bot_iff.mp hb
  intro f hf n hn
  have he := congrArg (fun ψ : F →* MulAut N => ψ ⟨f, hf⟩ ⟨n, hn⟩) ht
  have he' : f * n * f⁻¹ = n := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

omit [Finite G] in
private theorem oddCore_card_dvd_nine
    (ι : pPrimeCore 2 G →* ElementaryNine) (hι : Function.Injective ι) :
    Nat.card (pPrimeCore 2 G) ∣ 9 := by
  have h := card_dvd_of_injective ι hι
  have he : Nat.card ElementaryNine = 9 := by
    simp [ElementaryNine, Nat.card_eq_fintype_card]
  rwa [he] at h

/-- The simple residual forces the small odd core to have three-rank at most one. -/
theorem oddCore_rank_le_one_of_simple_subgroup
    (F : Subgroup G) [IsSimpleGroup F] [Group.IsPerfect F]
    (hF : Nat.card F = 168) (hrank : primeRank 3 G ≤ 2)
    (ι : pPrimeCore 2 G →* ElementaryNine) (hι : Function.Injective ι) :
    primeRank 3 (pPrimeCore 2 G) ≤ 1 := by
  let O := pPrimeCore 2 G
  have hOc : Nat.card O ∣ 9 := oddCore_card_dvd_nine ι hι
  have hFO : F ≤ centralizer (O : Set G) :=
    simple_subgroup_centralizes_small_normal F O hOc
  have hinter : O.subgroupOf F = ⊥ := by
    rcases (inferInstance : (O.subgroupOf F).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hle : F ≤ O := subgroupOf_eq_top.mp h
      have hd := (card_dvd_of_le hle).trans hOc
      rw [hF] at hd
      norm_num at hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 3
    (show 3 ∣ Nat.card F by rw [hF]; decide)
  have hxG : orderOf (x : G) = 3 :=
    (orderOf_injective F.subtype F.subtype_injective x).trans hx
  have hxO : (x : G) ∉ O := by
    intro h
    have hm : x ∈ O.subgroupOf F := h
    rw [hinter, mem_bot] at hm
    have := orderOf_eq_one_iff.mpr hm
    omega
  by_contra! hlarge
  obtain ⟨E, hE, hcard⟩ := CoverReduction.LocalCover.exists_elementary_nine hlarge
  let := hE
  let A := E.map O.subtype
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map _
  have hAc : Nat.card A = 3 ^ 2 :=
    (Nat.card_congr (equivMapOfInjective E _ O.subtype_injective).toEquiv).symm.trans hcard
  have hfix : A ≤ centralizer ({(x : G)} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hFO x.property a (map_subtype_le _ ha))
  have h := IsElementaryAbelian.primeRank_ge_of_fixed_join A (x : G) hxG
    (fun ha => hxO (map_subtype_le _ ha)) hfix hAc
  omega

private theorem oddCore_subnormal_le {J : Subgroup G} (hJ : J.IsSubnormal) :
    (pPrimeCore 2 J).map J.subtype ≤ pPrimeCore 2 G := by
  induction hJ with
  | top => exact pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 ⊤
  | step J K hJK hK hn ih =>
    let := hn
    have h := map_mono (f := K.subtype)
      (pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 (J.subgroupOf K))
    have he : K.subtype.comp (J.subgroupOf K).subtype =
        J.subtype.comp (subgroupOfEquivOfLe hJK).toMonoidHom := by ext x; rfl
    rw [map_map, he, ← map_map, pPrimeCore_map_iso] at h
    exact h.trans ih

/-- Every component center inherits the small odd-core three-rank bound. -/
theorem component_center_rank_le_one_of_oddCore
    (hO : primeRank 3 (pPrimeCore 2 G) ≤ 1)
    {J : Subgroup G} (hJ : IsComponent G J) : primeRank 3 (center J) ≤ 1 := by
  by_contra! hlarge
  obtain ⟨E, hE, hcard⟩ := CoverReduction.LocalCover.exists_elementary_nine hlarge
  let := hE
  let A := E.map (center J).subtype
  have hAc : Nat.card A = 9 :=
    (Nat.card_congr (equivMapOfInjective E _ (center J).subtype_injective).toEquiv).symm.trans hcard
  have hAZ : A ≤ center J := map_subtype_le _
  let : A.Normal := ⟨by
    intro a ha j
    rw [mem_center_iff.mp (hAZ ha) j, mul_assoc, mul_inv_cancel, mul_one]
    exact ha⟩
  have hAO : A ≤ pPrimeCore 2 J := le_sSup ⟨inferInstance, by rw [hAc]; decide⟩
  let B := A.map J.subtype
  have hBO : B ≤ pPrimeCore 2 G := (map_mono hAO).trans (oddCore_subnormal_le hJ.1)
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map _
  let D := B.subgroupOf (pPrimeCore 2 G)
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.subgroupOf hBO
  have hBc : Nat.card B = 9 :=
    (Nat.card_congr (equivMapOfInjective A _ J.subtype_injective).toEquiv).symm.trans hAc
  have hDc : Nat.card D = 3 ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBO).toEquiv).trans hBc
  have hr := IsElementaryAbelian.primeRank_ge_of_card D hDc
  omega

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
