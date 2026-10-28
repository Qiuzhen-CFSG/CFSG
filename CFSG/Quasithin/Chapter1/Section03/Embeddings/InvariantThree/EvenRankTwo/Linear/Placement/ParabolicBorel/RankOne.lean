module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Solvable Sylow overgroups through a binary rank-one local factor

The proved matrix version of F.1.3 places every proper overgroup of a Sylow
in SL₂ inside its normalizer. When |F| ≥ 4, SL₂ is nontrivial and perfect,
so a solvable image is proper. This includes |F| = 4.

For a local factor L with L/O₂(L) ≃ SL₂(F), the two-core lies in the Sylow,
so normalizers lift through the quotient. If H normalizes L and contains
the Sylow S, this makes S normal in H ∩ L. It is then characteristic there,
and H normalizes S. Normality is relative to these actual overgroups.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), using F.1.3, printed p.260.
This adapter uses the proved concrete Chapter F matrix result.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private theorem sl2_not_solvable (hF : 4 ≤ Nat.card F) : ¬ Group.IsSolvable SL(2,F) := by
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := by simpa using ha
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha1
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using h)
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top a.ne_zero hasq⟩
  let : Nontrivial SL(2,F) := ⟨⟨
    Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F),
    1, by
      intro h
      have he := congrArg (fun g : SL(2,F) => g.val 0 1) h
      simp [Matrix.SpecialLinearGroup.transvection_coe] at he⟩⟩
  exact Group.IsPerfect.not_isSolvable _

private theorem solvable_overgroup_normalizes_of_core_quotient
    {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (e : G ⧸ pCore 2 G ≃* SL(2,F))
    (H : Subgroup G) [Group.IsSolvable H] (hSH : (S : Subgroup G) ≤ H) :
    H ≤ normalizer (S : Set G) := by
  let q : G →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 G := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 G) x) = 1 ↔ x ∈ pCore 2 G
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff _
  let T := S.mapSurjective hq
  have hT := ChapterF.Source.Linear.all_sylows
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
    (ChapterF.Source.Linear.standard_facts F n (by omega) hF) T
  have hsol : Group.IsSolvable (H.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective H)
  have hproper : H.map q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    have : Group.IsSolvable (⊤ : Subgroup SL(2,F)) := ht ▸ hsol
    have hs : Group.IsSolvable SL(2,F) :=
      Group.isSolvable_of_surjective (f := (⊤ : Subgroup SL(2,F)).subtype)
        (by intro x; exact ⟨⟨x,mem_top x⟩,rfl⟩)
    have hfour : (2 : ℕ)^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
    exact sl2_not_solvable F (by rw [hF]; exact hfour) hs
  have hN := hT.unique_maximal (H.map q) (map_mono hSH) hproper
  have hc : ((S : Subgroup G).map q).comap q = (S : Subgroup G) :=
    comap_map_eq_self (by rw [hker]; exact pCore_isPGroup.le_sylow_of_normal S)
  have hnq : (normalizer ((T : Subgroup SL(2,F)) : Set SL(2,F))).comap q =
      normalizer (S : Set G) := by
    rw [comap_normalizer_eq_of_surjective _ hq]
    change normalizer (((S : Subgroup G).map q).comap q : Set G) = _
    rw [hc]
    rfl
  rw [← hnq]
  exact map_le_iff_le_comap.mp hN

/-- A normal local factor with binary rank-one core quotient controls solvable Sylow overgroups. -/
theorem solvable_overgroup_normalizes_of_normal_local
    {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (L H : Subgroup G)
    (hSL : (S : Subgroup G) ≤ L) (hSH : (S : Subgroup G) ≤ H)
    (hHL : H ≤ normalizer (L : Set G))
    (e : L ⧸ pCore 2 L ≃* SL(2,F)) [Group.IsSolvable H] :
    H ≤ normalizer (S : Set G) := by
  let K := L ⊓ H
  have hSK : (S : Subgroup G) ≤ K := le_inf hSL hSH
  let T := S.subtype hSL
  have hsol : Group.IsSolvable (H.subgroupOf L) := by
    let incl : H.subgroupOf L →* H :=
      { toFun := fun x => ⟨x.val.val,x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := incl)
      (by
        intro x y h
        have he : x.val.val = y.val.val := congrArg (fun z : H => (z : G)) h
        exact Subtype.ext (Subtype.ext he))
  have hh : H.subgroupOf L ≤ normalizer (T : Set L) :=
    solvable_overgroup_normalizes_of_core_quotient F hn hF T e (H.subgroupOf L)
      (by intro x hx; exact hSH hx)
  have hKN : K ≤ normalizer (S : Set G) := by
    have hm := map_mono (f := L.subtype) hh
    have hl : (normalizer (T : Set L)).map L.subtype ≤
        normalizer (S : Set G) := by
      change (normalizer ((T : Subgroup L) : Set L)).map L.subtype ≤ _
      have h := (T : Subgroup L).le_normalizer_map L.subtype
      simpa only [T, Sylow.coe_subtype, map_subgroupOf_eq_of_le hSL, Sylow.coe_coe] using h
    have hk := hm.trans hl
    simpa only [K, subgroupOf_map_subtype, inf_comm] using hk
  let U := S.subtype hSK
  have hU : (U : Subgroup K).Normal := normal_subgroupOf_of_le_normalizer hKN
  let : (U : Subgroup K).Characteristic := U.characteristic_of_normal hU
  have hchar : normalizer (K : Set G) ≤ normalizer (S : Set G) := by
    have h := normalizer_le_normalizer_characteristic_image K (U : Subgroup K)
    simpa only [U, Sylow.coe_subtype, map_subgroupOf_eq_of_le hSK, Sylow.coe_coe] using h
  exact (le_inf hHL H.le_normalizer).trans (inf_normalizer_le_normalizer_inf.trans hchar)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel
