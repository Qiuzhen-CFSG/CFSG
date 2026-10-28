module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Tactic

/-!
# Small A₆ actions and their fixed letters

Every orbit in an A₆ action of degree at most eight has size one or six.
Simplicity excludes proper subgroups of index below six. Index seven is
excluded by divisibility, and index eight would give a subgroup of order 45.
Such a subgroup has a unique Sylow five-subgroup, whose unique fixed letter
would put the whole subgroup in an order-60 point stabilizer. Consequently
every action on eight letters fixes at least two letters.

This supplies the permutation-group step in four-dimensional binary A₆
recognition, Aschbacher–Smith, K.1.1, printed p.452. The Sylow fixed-point
argument adapts the order-40 calculation in
`Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups`; the imported
small-index result retains its ATLAS attribution and license.
-/

@[expose] public section

open Subgroup MulAction
namespace Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
abbrev A6 := alternatingGroup (Fin 6)

theorem card_A6 : Nat.card A6 = 360 := by
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

theorem not_card_fortyFive (H : Subgroup A6) : Nat.card H ≠ 45 := by
  intro hc
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 H := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hc]
    decide +kernel
  have hi : (P : Subgroup H).index = 9 := by
    have h := (P : Subgroup H).card_mul_index
    rw [hP, hc] at h
    omega
  have hn : Nat.card (Sylow 5 H) = 1 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hm := card_sylow_modEq_one 5 H
    have hb := Nat.le_of_dvd (by decide : 0 < 9) hd
    change Nat.card (Sylow 5 H) % 5 = 1 % 5 at hm
    interval_cases hn : Nat.card (Sylow 5 H) <;> norm_num at hd <;> omega
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

theorem small_index (H : Subgroup A6) (hi : H.index ≤ 8) : H.index = 1 ∨ H.index = 6 := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  by_cases hsmall : H.index < 6
  · left
    apply Subgroup.index_eq_one.mpr
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le (show H.index ≤ 5 by omega)
    rw [card_A6]
    norm_num [Nat.factorial] at hb ⊢
    omega
  · have hd := H.index_dvd_card
    rw [card_A6] at hd
    have hne : H.index ≠ 8 := by
      intro he
      have hc := H.card_mul_index
      rw [he, card_A6] at hc
      exact not_card_fortyFive H (by omega)
    have he : H.index = 6 ∨ H.index = 7 := by omega
    rcases he with he | he
    · exact Or.inr he
    · norm_num [he] at hd

theorem orbit_card {X : Type*} [Finite X] [MulAction A6 X]
    (hc : Nat.card X ≤ 8) (x : X) :
    Nat.card (orbit A6 x) = 1 ∨ Nat.card (orbit A6 x) = 6 := by
  have he : Nat.card (orbit A6 x) = (stabilizer A6 x).index :=
    Nat.card_congr (orbitEquivQuotientStabilizer A6 x)
  rw [he]
  apply small_index
  rw [← he]
  exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans hc



theorem exists_fixed_pair (f : A6 →* Equiv.Perm (Fin 8)) :
    ∃ a b : Fin 8, a ≠ b ∧ ∀ g : A6, f g a = a ∧ f g b = b := by
  classical
  let : MulAction A6 (Fin 8) := MulAction.compHom _ f
  have hc (x : Fin 8) := orbit_card (by simp : Nat.card (Fin 8) ≤ 8) x
  have hfixed (x : Fin 8) (h : Nat.card (orbit A6 x) = 1) :
      x ∈ fixedPoints A6 (Fin 8) := by
    apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rwa [Nat.card_eq_fintype_card] at h
  by_cases hlarge : ∃ x : Fin 8, Nat.card (orbit A6 x) = 6
  · obtain ⟨x, hx⟩ := hlarge
    have hcompl : Nat.card (↥(orbit A6 x)ᶜ) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
      rw [Nat.card_eq_fintype_card] at hx
      simp [hx]
    have hfix (y : ↥(orbit A6 x)ᶜ) : y.val ∈ fixedPoints A6 (Fin 8) := by
      have hle : orbit A6 y.val ⊆ (orbit A6 x)ᶜ := by
        intro z hz hzx
        apply y.property
        rw [← orbit_eq_iff] at hz hzx ⊢
        exact hz.symm.trans hzx
      have hsmall : Nat.card (orbit A6 y.val) ≤ 2 := by
        rw [← hcompl]
        exact Nat.card_le_card_of_injective (Set.inclusion hle) (Set.inclusion_injective hle)
      exact hfixed y.val ((hc y.val).resolve_right (by omega))
    have : Nontrivial (↥(orbit A6 x)ᶜ) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(orbit A6 x)ᶜ)
    refine ⟨a.val, b.val, fun he => hab (Subtype.ext he), fun g => ?_⟩
    exact ⟨hfix a g, hfix b g⟩
  · have hall (x : Fin 8) : x ∈ fixedPoints A6 (Fin 8) :=
      hfixed x ((hc x).resolve_right (fun h => hlarge ⟨x, h⟩))
    exact ⟨0, 1, by decide, fun g => ⟨hall 0 g, hall 1 g⟩⟩

end Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
