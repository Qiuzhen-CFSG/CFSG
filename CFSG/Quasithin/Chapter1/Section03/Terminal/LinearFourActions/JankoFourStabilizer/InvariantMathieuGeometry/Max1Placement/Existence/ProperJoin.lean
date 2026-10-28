module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Candidates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.Order.Atoms.Finite

/-!
# Properness of the J₄ local L₄(2) join

The concrete matrix model has no nontrivial two-group quotient: the certified
order-37 element `a * b` normally generates it. A proper subnormal subgroup
therefore cannot generate the model together with a two-subgroup. The order of
an L₄(2) section is 20160, so adjoining its two-core cannot introduce the prime
37. Consequently the source-local subgroup A is proper, its join with S is
proper, and a maximal proper overgroup containing both exists.

This argument uses the actual matrix-word normal-generation certificate and
requires neither simplicity nor the full order of the J₄ model. It prepares
the Sylow-overgroup argument in Aschbacher–Smith A.3.12(17), printed pp.47–48,
used in the proof of 1.3.9, p.514. The matrix provenance is recorded in
`Theory.SpecificGroups.Janko4.Model.Simplicity.NormalGeneration`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels

private theorem normal_eq_top_of_two_quotient (N : Subgroup Janko4.Model) [N.Normal]
    (hp : IsPGroup 2 (Janko4.Model ⧸ N)) : N = ⊤ := by
  let q := QuotientGroup.mk' N
  let r := Janko4.a * Janko4.b
  have hr37 : q r ^ 37 = 1 := by
    rw [← map_pow, ← Janko4.orderOf_a_mul_b]
    simp only [r, pow_orderOf_eq_one, map_one]
  obtain ⟨n, hn⟩ := hp.exists_pow_pow_eq_one (q r)
  have hr : q r = 1 :=
    (pow_eq_one_iff_of_coprime ((by decide : Nat.Coprime 2 37).pow_left n)).mp ⟨hn, hr37⟩
  have hrN : r ∈ N := (QuotientGroup.eq_one_iff r).mp hr
  have hgen : normalClosure ({r} : Set Janko4.Model) = ⊤ := by
    exact Janko4.Simplicity.normalClosure_primeRepresentative_eq_top
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four 10
  have hle : normalClosure ({r} : Set Janko4.Model) ≤ N :=
    normalClosure_le_normal (by rintro x rfl; exact hrN)
  exact top_unique (hgen ▸ hle)

private theorem section_card {G : Type*} [Group G]
    (h : ClassicalGroup.IsPSL G 4 2) : Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem section_ne_top (A : Subgroup Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2) : A ≠ ⊤ := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hc := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
  rw [section_card hA, hn] at hc
  have hcop : Nat.Coprime 37 (Nat.card A) := by
    rw [hc]
    exact (by decide : Nat.Coprime 37 20160).mul_right
      ((by decide : Nat.Coprime 37 2).pow_right n)
  intro ht
  have hd : 37 ∣ Nat.card A := by
    rw [ht, card_top, ← Janko4.orderOf_a_mul_b]
    exact orderOf_dvd_natCard (Janko4.a * Janko4.b)
  exact (by decide : Nat.Prime 37).coprime_iff_not_dvd.mp hcop hd

/-- The source-local join is proper, without ambient simplicity. -/
theorem local_join_ne_top (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S) :
    A ⊔ S.toSubgroup ≠ ⊤ := by
  intro hgen
  have hsub : A.IsSubnormal := by
    change (A.subgroupOf (A ⊔ S.toSubgroup)).IsCComponent at hlocal
    rw [hgen] at hlocal
    have h := hlocal.subnormal.map (f := (⊤ : Subgroup Janko4.Model).subtype)
      (MonoidHom.range_eq_top.mp (range_subtype ⊤))
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  obtain ⟨N, hN, hAN, hNt⟩ :=
    hsub.exists_normal_and_le_and_lt_top_of_ne (section_ne_top A hA)
  let := hN
  have hsup : N ⊔ S.toSubgroup = ⊤ :=
    top_unique (hgen ▸ sup_le_sup_right hAN S.toSubgroup)
  exact hNt.ne (normal_eq_top_of_two_quotient N
    (isPGroup_quotient_of_sup_eq_top N S.toSubgroup S.isPGroup' hsup))

/-- The local subgroup and its original Sylow lie in a maximal proper subgroup. -/
theorem exists_maximal_local_overgroup (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S) :
    ∃ M : Subgroup Janko4.Model, IsCoatom M ∧ A ≤ M ∧ S.toSubgroup ≤ M := by
  obtain htop | ⟨M, hM, hle⟩ := eq_top_or_exists_le_coatom (A ⊔ S.toSubgroup)
  · exact (local_join_ne_top A S hA hlocal htop).elim
  · exact ⟨M, hM, le_sup_left.trans hle, le_sup_right.trans hle⟩
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
