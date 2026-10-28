module

public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.ReflectionGeometry.Choice.Alternating
public import Theory.PGroupCore
public import Mathlib.GroupTheory.GroupAction.SubMulAction


/-!
# Proper Sylow-two overgroups in A₆

A proper subgroup containing a Sylow two-subgroup has order eight or
twenty-four. Simplicity and the faithful coset action exclude index below
six. The only other possible order is forty; its unique Sylow five-subgroup
has a unique fixed point on six letters, so the whole subgroup would lie
in a point stabilizer of order sixty, a contradiction.

A Sylow subgroup of index at most three proves solvability. A nontrivial
three-core would be cyclic of order three, but its ambient normalizer has
order eighteen and cannot contain a Sylow two-subgroup of order eight.
The remaining odd prime cores vanish by divisibility.

These elementary permutation arguments supply the exact geometry needed
for the central-cover step in Aschbacher–Smith, combined manuscript of
1 March 2004, B.1.13, printed p.74 (PDF p.85). No subgroup classification
or recognition by order is assumed.
-/

public section
open Subgroup
namespace AlternatingSix.ProperSylowOvergroups
local notation "A6" => alternatingGroup (Fin 6)
private theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem point_stabilizer_card (i : Fin 6) :
    Nat.card (MulAction.stabilizer A6 i) = 60 := by
  classical
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin 6) (by simp)
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A6 i)
  rw [Nat.card_prod, MulAction.orbit_eq_univ] at h
  simp only [Nat.card_eq_fintype_card, Fintype.card_setUniv, Fintype.card_fin] at h
  have hc : Fintype.card A6 = 360 := by simpa only [Nat.card_eq_fintype_card] using card_A6
  rw [hc] at h
  rw [Nat.card_eq_fintype_card]
  omega

private theorem fixed_points_five (H : Subgroup A6) (P : Subgroup H)
    (hc : Nat.card P = 5) : Nat.card (MulAction.fixedPoints P (Fin 6)) = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hm := hp.card_modEq_card_fixedPoints (Fin 6)
  have hb : Nat.card (MulAction.fixedPoints P (Fin 6)) ≤ 6 :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans_eq (Nat.card_fin 6)
  have hn : Nat.card (MulAction.fixedPoints P (Fin 6)) ≠ 6 := by
    intro he
    have hs : Function.Surjective (Subtype.val : MulAction.fixedPoints P (Fin 6) → Fin 6) :=
      ((Nat.bijective_iff_injective_and_card _).mpr
        ⟨Subtype.val_injective, he.trans (Nat.card_fin 6).symm⟩).surjective
    have htriv : Subsingleton P := by
      apply subsingleton_of_forall_eq 1
      intro x
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Equiv.ext
      intro i
      obtain ⟨j, rfl⟩ := hs i
      exact j.property x
    have hone : Nat.card P = 1 := by
      let := htriv
      exact Nat.card_eq_one_iff_unique.mpr ⟨htriv, inferInstance⟩
    omega
  rw [Nat.card_fin] at hm
  change 6 % 5 = Nat.card (MulAction.fixedPoints P (Fin 6)) % 5 at hm
  omega

private theorem not_card_forty (H : Subgroup A6) : Nat.card H ≠ 40 := by
  intro hc
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 H := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hc]
    decide +kernel
  have hi : (P : Subgroup H).index = 8 := by
    have h := (P : Subgroup H).card_mul_index
    rw [hP, hc] at h
    omega
  have hn : Nat.card (Sylow 5 H) = 1 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hm := card_sylow_modEq_one 5 H
    have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
    change Nat.card (Sylow 5 H) % 5 = 1 % 5 at hm
    interval_cases hn : Nat.card (Sylow 5 H) <;> omega
  let : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hn).1
  let : (P : Subgroup H).Normal := P.normal_of_subsingleton
  obtain ⟨hsub, hnon⟩ := Nat.card_eq_one_iff_unique.mp (fixed_points_five H P hP)
  let i := hnon.some
  have hfix (g : H) : g • i.val = i.val := by
    exact congrArg Subtype.val (hsub.elim
      (⟨g • i.val, smul_mem_fixedPoints_of_normal g i.property⟩ :
        MulAction.fixedPoints (P : Subgroup H) (Fin 6)) i)
  have hle : H ≤ MulAction.stabilizer A6 i.val := by
    intro g hg
    exact hfix ⟨g, hg⟩
  have hd := card_dvd_of_le hle
  rw [hc, point_stabilizer_card] at hd
  norm_num at hd

/-- A proper Sylow-two overgroup in A₆ has order eight or twenty-four. -/
theorem card_eight_or_twentyFour (S : Sylow 2 A6) (H : Subgroup A6)
    (hSH : (S : Subgroup A6) ≤ H) (hH : H ≠ ⊤) :
    Nat.card H = 8 ∨ Nat.card H = 24 := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have hi : 6 ≤ H.index := by
    by_contra hn
    apply hH
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le (show H.index ≤ 5 by omega)
    rw [card_A6]
    norm_num [Nat.factorial] at hb ⊢
    omega
  have hcard := H.card_mul_index
  rw [card_A6] at hcard
  have hb : Nat.card H ≤ 60 := by nlinarith [Nat.card_pos (α := H)]
  have hd : Nat.card H ∣ 360 := card_A6 ▸ H.card_subgroup_dvd_card
  have hs : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity, card_A6]
    decide +kernel
  have h8 : 8 ∣ Nat.card H := hs ▸ card_dvd_of_le hSH
  have h40 := not_card_forty H
  interval_cases hc : Nat.card H <;> omega

private theorem solvable_small_index {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Group.IsSolvable H] (hi : H.index ≤ 4) : Group.IsSolvable G := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ H) ≤ Fintype.card (Fin 4) := by
    simpa only [Subgroup.index_eq_card, ← Nat.card_eq_fintype_card, Nat.card_fin] using hi
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (G ⧸ H)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  apply Group.isSolvable_of_ker_le_range H.subtype (MulAction.toPermHom G (G ⧸ H))
  rw [Subgroup.range_subtype, ← H.normalCore_eq_ker]
  exact H.normalCore_le

/-- Solvability is obtained from a Sylow subgroup of index at most three. -/
theorem isSolvable (S : Sylow 2 A6) (H : Subgroup A6)
    (hSH : (S : Subgroup A6) ≤ H) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  have hc := card_eight_or_twentyFour S H hSH hH
  let P := S.subtype hSH
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  apply solvable_small_index (P : Subgroup H)
  have hp : Nat.card P = 8 := by
    rw [Sylow.card_eq_multiplicity]
    rcases hc with hc | hc <;> rw [hc] <;> decide +kernel
  have hi := (P : Subgroup H).card_mul_index
  rw [hp] at hi
  rcases hc with hc | hc <;> omega

private theorem three_core_eq_bot (S : Sylow 2 A6) (H : Subgroup A6)
    (hSH : (S : Subgroup A6) ≤ H) (hH : H ≠ ⊤) : pCore 3 H = ⊥ := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P := pCore 3 H
  have hc := card_eight_or_twentyFour S H hSH hH
  have hd := P.card_subgroup_dvd_card
  have hthree : Nat.card P = 1 ∨ Nat.card P = 3 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (pCore_isPGroup (p := 3) (G := H)))
    have hd24 : 3 ^ n ∣ 24 := by
      rw [← hn]
      rcases hc with hc | hc
      · exact hd.trans (hc ▸ (by decide : 8 ∣ 24))
      · exact hc ▸ hd
    have hb : n ≤ 1 := by
      by_contra! h
      have h9 : 9 ∣ 24 := (show 3 ^ 2 ∣ 3 ^ n from pow_dvd_pow 3 h).trans hd24
      norm_num at h9
    change Nat.card P = 3 ^ n at hn
    interval_cases n
    · exact Or.inl hn
    · exact Or.inr hn
  rcases hthree with hcP | hcP
  · exact Subgroup.card_eq_one.mp hcP
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 3 (by rw [hcP])
  let y : A6 := x.val.val
  have hy : orderOf y = 3 := by
    change orderOf (H.subtype (P.subtype x)) = 3
    rw [orderOf_injective H.subtype H.subtype_injective,
      orderOf_injective P.subtype P.subtype_injective, hx]
  have hPgen : P = zpowers (x : H) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr x.property) ?_).symm
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, hcP]
  have hmap : P.map H.subtype = zpowers y := by
    rw [hPgen, MonoidHom.map_zpowers]
    rfl
  have hHN : H ≤ normalizer (zpowers y : Set A6) := by
    have hN := P.le_normalizer_map H.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, hmap] at hN
    exact hN
  have h8 : 8 ∣ Nat.card (normalizer (zpowers y : Set A6)) := by
    have hs : Nat.card S = 8 := by rw [Sylow.card_eq_multiplicity, card_A6]; decide +kernel
    exact hs ▸ card_dvd_of_le (hSH.trans hHN)
  rw [(Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.ReflectionChoice.a6_three_normalizer y hy).1] at h8
  norm_num at h8

/-- No odd prime core survives in a proper Sylow-two overgroup of A₆. -/
theorem odd_pCore_eq_bot (S : Sylow 2 A6) (H : Subgroup A6)
    (hSH : (S : Subgroup A6) ≤ H) (hH : H ≠ ⊤)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : pCore p H = ⊥ := by
  by_cases hp3 : p = 3
  · subst p
    exact three_core_eq_bot S H hSH hH
  have hc := card_eight_or_twentyFour S H hSH hH
  have hd24 : Nat.card H ∣ 24 := by
    rcases hc with hc | hc
    · rw [hc]; decide
    · rw [hc]
  rcases (pCore_isPGroup (p := p) (G := H)).card_eq_or_dvd with hcP | hd
  · exact Subgroup.card_eq_one.mp hcP
  have hpd : p ∣ 2 ^ 3 * 3 := hd.trans ((pCore p H).card_subgroup_dvd_card.trans hd24)
  rcases (Fact.out : p.Prime).dvd_mul.mp hpd with h2 | h3
  · exact (hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h2))).elim
  · exact (hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h3)).elim
end AlternatingSix.ProperSylowOvergroups
