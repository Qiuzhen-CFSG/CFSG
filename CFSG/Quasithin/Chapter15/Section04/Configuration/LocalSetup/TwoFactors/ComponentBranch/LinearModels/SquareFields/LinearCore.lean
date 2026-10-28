module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels.Setup
public import GorensteinWalter.PGL2InnerAction
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The two-core obstruction in the projective fixed group

Over an odd finite field with more than three elements, PGL₂ has trivial
two-core. Its normal simple PSL₂ subgroup meets that core trivially, so
normality forces the two-core to centralize PSL₂; the latter centralizer
is trivial. Consequently a PGL₂ group of characteristic two can only have
field order three.

This is the terminal obstruction after identifying the coefficient-fixed
subgroup in the square-field cases of the component argument.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163, using the PSL₂ alternatives of F.6.18, pp.309–310.
-/

public section
noncomputable section
open GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields

/-- Above field order three, the odd projective general linear group has trivial two-core. -/
theorem pgl2_twoCore_eq_bot (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F) :
    pCore 2 (PGL2 F) = ⊥ := by
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let toPGL : PSL2 F →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hinj : Function.Injective toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let O := pCore 2 (PGL2 F)
  let L := toPGL.range
  have hLn : L.Normal := by
    dsimp [L, toPGL]
    rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hlarge]
    infer_instance
  let N := O.comap toPGL
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance _
  have hNp : IsPGroup 2 N := pCore_isPGroup.comap_of_injective toPGL hinj
  have hN : N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hNn with hbot | htop
    · exact hbot
    · have hp : IsPGroup 2 (PSL2 F) :=
        hNp.of_equiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      let : Group.IsNilpotent (PSL2 F) := hp.isNilpotent
      have hc : Subgroup.center (PSL2 F) = ⊤ := Subgroup.center_eq_top
      rw [psl2_center_eq_bot F] at hc
      exact (bot_ne_top hc).elim
  have hdis : Disjoint O L := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    rintro y ⟨hyO, x, rfl⟩
    have hx : x ∈ N := hyO
    rw [hN] at hx
    have hx1 : x = 1 := Subgroup.mem_bot.mp hx
    simp [hx1]
  apply le_bot_iff.mp
  intro x hx
  have hcent : x ∈ Subgroup.centralizer (L : Set (PGL2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.commute_of_normal_of_disjoint O L inferInstance hLn hdis x y hx hy).symm.eq
  rw [show Subgroup.centralizer (L : Set (PGL2 F)) = ⊥ from
    pgl2_psl2Range_centralizer_eq_bot F hF] at hcent
  exact hcent

/-- An odd PGL₂ model with a self-centralizing two-core has field order three. -/
theorem pgl2_card_eq_three_of_characteristicTwo (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (hc : HasCharacteristicTwo (PGL2 F)) : Nat.card F = 3 := by
  have h3 : 3 ≤ Nat.card F := by
    rcases hF with ⟨p, n, hp, hpo, hn, he⟩
    have hp3 : 3 ≤ p := by
      have hp2 := hp.two_le
      have hpne : p ≠ 2 := by
        intro h
        exact hpo.not_two_dvd_nat (by simp [h])
      omega
    rw [he]
    exact hp3.trans (Nat.le_pow (by omega))
  by_contra hne
  have hlarge : 3 < Nat.card F := by omega
  have hcore := pgl2_twoCore_eq_bot F hF hlarge
  have helem (x : PGL2 F) : x = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hcore]
    apply hc
    rw [hcore, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y = 1 := Subgroup.mem_bot.mp hy
    simp [hy1]
  have htriv : Subsingleton (PGL2 F) :=
    ⟨fun x y => (helem x).trans (helem y).symm⟩
  let : Subsingleton (PGL2 F) := htriv
  have hinj : Function.Injective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let : Subsingleton (PSL2 F) := hinj.subsingleton
  let : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (PSL2 F)
  exact hxy (Subsingleton.elim x y)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.LinearModels.SquareFields
