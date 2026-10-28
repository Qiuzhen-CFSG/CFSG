module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Six.Sylow
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Fitting and relative normality in the exceptional Singer branch

A fixed-point-free order-seven actor centralizes every other prime core by
A.1.12's earlier fixed-vector input. The actual abelian seven-subgroups of
GL₆(2) give centralization of the seven-core too, hence of the Fitting group.
If its centralizer in Y is X, Fitting self-centralization puts W in F(Y)
and F(Y) in the cyclic X. Conjugation on a cyclic group preserves all its
subgroups. Consequently W is normal, is exactly O₇(Y), and X is normal in Y.

The centralizer equality remains an explicit premise of this reduction;
the GL₂(8) realization and Dickson bound must supply it in final assembly.
Source: Aschbacher–Smith A.1.12, printed p.22.
-/

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Singer.Six

private theorem normal_of_centralizes_fitting {G : Type*} [Group G] [Finite G]
    (X W : Subgroup G) [IsCyclic X] (hsolv : Group.IsSolvable G)
    (hWF : W ≤ centralizer (fittingSubgroup G : Set G))
    (hCW : centralizer (W : Set G) = X) : W.Normal ∧ X.Normal := by
  have hWF' : W ≤ fittingSubgroup G := hWF.trans
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  have hFX : fittingSubgroup G ≤ X := by
    rw [← hCW]
    exact (Subgroup.le_centralizer_iff).mp hWF
  let : IsCyclic (fittingSubgroup G) := Subgroup.isCyclic_of_le hFX
  have hWnorm : W.Normal := by
    constructor
    intro w hw g
    obtain ⟨n, hn⟩ := (MulAut.conjNormal (H := fittingSubgroup G) g).toMonoidHom.map_cyclic
    have he := congrArg (fun z : fittingSubgroup G => (z : G)) (hn ⟨w, hWF' hw⟩)
    change g * w * g⁻¹ = w ^ n at he
    rw [he]
    exact W.zpow_mem hw n
  let : W.Normal := hWnorm
  refine ⟨hWnorm, ?_⟩
  rw [← hCW]
  infer_instance

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The source's Fitting-centralization step, using the actual abelian
seven-subgroups and the shared fixed-vector theorem. -/
public theorem seven_le_centralizer_fitting
    (hn : Module.finrank (ZMod 2) V = 6)
    (X Y W : Subgroup (V ≃ₗ[ZMod 2] V))
    (hreg : LinearGroup.IsRegularOnNonzero X) (hXY : X ≤ Y)
    (hWX : W ≤ X) (hW : Nat.card W = 7)
    (hfp : PrimeFixedPointCentralization Y) :
    W.subgroupOf Y ≤ centralizer (fittingSubgroup Y : Set Y) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Finite (V ≃ₗ[ZMod 2] V) := Nat.finite_of_card_ne_zero (by
    rw [card_linearGroup hn]; decide)
  have hWY : W ≤ Y := hWX.trans hXY
  have hW7 : Nat.card (W.subgroupOf Y) = 7 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv).trans hW
  have hpW : IsPGroup 7 (W.subgroupOf Y) :=
    IsPGroup.of_card (n := 1) hW7
  apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
  intro q
  have hq : Nat.Prime q.val.val := Nat.prime_of_mem_primeFactors q.val.property
  by_cases heq : q.val.val = 7
  · rw [heq]
    obtain ⟨S, hWS⟩ := hpW.exists_le_sylow
    have hOS := fitting_pCore_le_sylow S
    let T : Subgroup (V ≃ₗ[ZMod 2] V) := (S : Subgroup Y).map Y.subtype
    let : IsMulCommutative T := seven_subgroup_commutative hn T
      (S.isPGroup'.map Y.subtype)
    intro w hw
    apply mem_centralizer_iff.mpr
    intro a ha
    apply Subtype.ext
    exact congrArg (fun t : T => (t : V ≃ₗ[ZMod 2] V)) (mul_comm
      (⟨a, Subgroup.mem_map_of_mem Y.subtype (hOS ha)⟩ : T)
      ⟨w, Subgroup.mem_map_of_mem Y.subtype (hWS hw)⟩)
  · intro w hw
    apply mem_centralizer_iff.mpr
    intro a ha
    by_cases hw1 : w = 1
    · simp [hw1]
    have hw7 : orderOf w = 7 := orderOf_eq_prime (by
      have h := pow_card_eq_one' (x := (⟨w, hw⟩ : W.subgroupOf Y))
      rw [hW7] at h
      exact congrArg Subtype.val h) hw1
    have hfixed (v : V) (hv : (w : V ≃ₗ[ZMod 2] V) v = v) : v = 0 := by
      by_contra hv0
      have hh := hreg.eq_one_of_apply_eq_self (⟨w, hWX hw⟩ : X) hv0 hv
      exact hw1 (Subtype.ext (congrArg (fun x : X => (x : V ≃ₗ[ZMod 2] V)) hh))
    exact (hfp q.val.val 7 hq (by decide) heq (pCore q.val.val Y)
      inferInstance pCore_isPGroup w hw7 hfixed ⟨a, ha⟩).symm.eq

/-- Once the centralizer is identified, W is exactly the relative seven-core
and the Singer subgroup is normal in the specified overgroup. -/
public theorem seven_core_and_normal_of_centralizer_eq
    (hn : Module.finrank (ZMod 2) V = 6)
    (X Y W : Subgroup (V ≃ₗ[ZMod 2] V)) [IsCyclic X]
    (hreg : LinearGroup.IsRegularOnNonzero X) (hXY : X ≤ Y)
    (hWX : W ≤ X) (hW : Nat.card W = 7) (hsolv : Group.IsSolvable Y)
    (hfp : PrimeFixedPointCentralization Y)
    (hCW : centralizer (W.subgroupOf Y : Set Y) = X.subgroupOf Y) :
    W.subgroupOf Y = pCore 7 Y ∧ (X.subgroupOf Y).Normal := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Finite (V ≃ₗ[ZMod 2] V) := Nat.finite_of_card_ne_zero (by
    rw [card_linearGroup hn]; decide)
  let : IsCyclic (X.subgroupOf Y) :=
    (Subgroup.subgroupOfEquivOfLe hXY).isCyclic.mpr inferInstance
  have hWF := seven_le_centralizer_fitting hn X Y W hreg hXY hWX hW hfp
  obtain ⟨hWnorm, hXnorm⟩ := normal_of_centralizes_fitting
    (X.subgroupOf Y) (W.subgroupOf Y) hsolv hWF hCW
  have hW7 : Nat.card (W.subgroupOf Y) = 7 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hWX.trans hXY)).toEquiv).trans hW
  have hWO : W.subgroupOf Y ≤ pCore 7 Y :=
    le_sSup ⟨hWnorm, IsPGroup.of_card (n := 1) hW7⟩
  have hFX : fittingSubgroup Y ≤ X.subgroupOf Y := by
    rw [← hCW]
    exact Subgroup.le_centralizer_iff.mp hWF
  have hOX : pCore 7 Y ≤ X.subgroupOf Y := (pCore_le_fitting Y 7).trans hFX
  have hX63 : Nat.card (X.subgroupOf Y) = 63 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv).trans (card_regular hn hreg)
  have hd : Nat.card (pCore 7 Y) ∣ 9 * 7 := by
    simpa only [hX63] using Subgroup.card_dvd_of_le hOX
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 7) (G := Y)).exists_card_eq
  have hcop : Nat.Coprime (Nat.card (pCore 7 Y)) 9 := by
    rw [hn]
    exact (show Nat.Coprime 7 9 by decide).pow_left n
  have hbound := Nat.le_of_dvd (by decide : 0 < 7) (hcop.dvd_of_dvd_mul_left hd)
  exact ⟨Subgroup.eq_of_le_of_card_ge hWO (by simpa only [hW7] using hbound), hXnorm⟩

/-- The order bound supplied by GL₂(8) turns the evident Singer containment
into equality with the centralizer in Y. -/
public theorem centralizer_eq_of_card_le
    (hn : Module.finrank (ZMod 2) V = 6)
    (X Y W : Subgroup (V ≃ₗ[ZMod 2] V)) [IsCyclic X]
    (hreg : LinearGroup.IsRegularOnNonzero X) (hXY : X ≤ Y) (hWX : W ≤ X)
    (hbound : Nat.card (centralizer (W.subgroupOf Y : Set Y)) ≤ 63) :
    centralizer (W.subgroupOf Y : Set Y) = X.subgroupOf Y := by
  let : Finite (V ≃ₗ[ZMod 2] V) := Nat.finite_of_card_ne_zero (by
    rw [card_linearGroup hn]; decide)
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · intro x hx
    apply mem_centralizer_iff.mpr
    intro w hw
    exact Subtype.ext (congrArg (fun x : X => (x : V ≃ₗ[ZMod 2] V))
      (mul_comm (⟨w, hWX hw⟩ : X) ⟨x, hx⟩))
  · have hc : Nat.card (X.subgroupOf Y) = 63 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv).trans
        (card_regular hn hreg)
    simpa only [hc] using hbound

end CFSG.Quasithin.ChapterA.Singer.Six
