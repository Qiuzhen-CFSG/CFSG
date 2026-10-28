module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore.Preparation
public import Theory.GroupTheory.CComponent.CentralInvolution
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# From ordinary-layer centralization to plane odd-core containment

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The common Sylow subgroup puts O₂(C_G(W)) inside T, so the fixed involution
z centralizes that core. Inversion of both odd cores makes the smaller
odd core lie in [C_G(W),z]; those commutators centralize the odd core and
the Fitting subgroup. If the smaller core also centralizes the ordinary
layer, it lies in C(F*). This normal abelian subgroup absorbs it into the
ambient odd core. All normality here is inside the actual plane centralizer.

Only the ordinary-layer centralization remains an explicit premise.
Source: Aschbacher–Smith, 12.4.8, printed p.816.
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
open Section02 SmallFusion ChapterE ChapterE.Section06
universe u

private theorem inverted_odd_le_commutator {H : Type*} [Group H] [Finite H]
    (R : Subgroup H) (ho : Nat.Coprime 2 (Nat.card R)) (z : H)
    (hi : ∀ x ∈ R, z * x * z⁻¹ = x⁻¹) :
    R ≤ ⁅(⊤ : Subgroup H), zpowers z⁆ := by
  intro x hx
  obtain ⟨y, hy⟩ := ho.symm.pow_left_bijective.surjective (⟨x, hx⟩ : R)
  have hs : (y : H) ^ 2 = ⁅(y : H), z⁆ := by
    calc
      _ = (y : H) * (z * (y : H)⁻¹ * z⁻¹) := by
        rw [hi _ (R.inv_mem y.property), inv_inv, pow_two]
      _ = _ := by simp only [commutatorElement_def, mul_assoc]
  have hm := commutator_mem_commutator (mem_top (y : H)) (mem_zpowers z)
  rw [← hs] at hm
  simpa only [← Subgroup.coe_pow, hy] using hm

private theorem odd_le_core_of_centralizes_fStar {H : Type*} [Group H] [Finite H]
    (R : Subgroup H) (ho : Nat.Coprime 2 (Nat.card R))
    (hc : R ≤ centralizer (generalizedFitting H : Set H)) : R ≤ pPrimeCore 2 H := by
  let C := centralizer (generalizedFitting H : Set H)
  have hCC : C ≤ centralizer (C : Set H) := by
    intro x hx y hy
    exact hx y (centralizer_generalizedFitting_le H hy)
  let : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp hCC
  let : CommGroup C := IsMulCommutative.instCommGroup
  let e : R.subgroupOf C ≃* R := subgroupOfEquivOfLe hc
  have hR : R.subgroupOf C ≤ pPrimeCore 2 C := le_sSup ⟨inferInstance, by
    rwa [Nat.card_congr e.toEquiv]⟩
  calc
    R = (R.subgroupOf C).map C.subtype := (map_subgroupOf_eq_of_le hc).symm
    _ ≤ (pPrimeCore 2 C).map C.subtype := map_mono hR
    _ ≤ pPrimeCore 2 H := pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 C

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The exact plane containment, conditional only on centralization of its
ordinary layer. Inversion and centralization of the two cores are derived. -/
theorem core_le_plane_core_of_layer (c : Configuration T L V U)
    (W : Subgroup G) (hWU : W ≤ U) (hcor : subgroupCorank U W = 1)
    (hlayer : core U ≤ centralizer
      ((componentLayer (centralizer (W : Set G))).map
        (centralizer (W : Set G)).subtype : Set G)) :
    core U ≤ core W := by
  let H := centralizer (W : Set G)
  let R := (core U).subgroupOf H
  have hRH : core U ≤ H := (map_subtype_le _).trans (centralizer_le hWU)
  let eR : R ≃* core U := subgroupOfEquivOfLe hRH
  have hodd : Nat.Coprime 2 (Nat.card R) := by
    rw [Nat.card_congr eR.toEquiv]
    exact core_odd U
  obtain ⟨z, hz, hfix, hM, hiU, _, hiW⟩ := simultaneous_inversion c
  have hzV : z ∈ V := (show fixedSubgroup L V ≤ V from inf_le_left)
    (hfix.symm ▸ mem_zpowers z)
  let _ := c.chosen.elementary
  have hzH : z ∈ H := (centralizer_le (hWU.trans c.le_module)) (le_centralizer V hzV)
  let zH : H := ⟨z, hzH⟩
  have hiR : ∀ x ∈ R, zH * x * zH⁻¹ = x⁻¹ := by
    intro x hx
    exact Subtype.ext (hiU x hx)
  obtain ⟨S, hS⟩ := c.sylow_centralizers.2 W hWU hcor
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    exact (pCoreIn_le_sylow H S).trans (hS ▸ (show
      sylowCentralizer (T : Subgroup G) V ≤ (T : Subgroup G) from inf_le_left))
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hzcore : ∀ x ∈ pCore 2 H, x * zH = zH * x := by
    intro x hx
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hM ▸ hE.sylow_le
      (hcoreT (mem_map_of_mem H.subtype hx)))
  have hiO : ∀ x ∈ pPrimeCore 2 H, zH * x * zH⁻¹ = x⁻¹ := by
    intro x hx
    exact Subtype.ext ((hiW W hWU hcor).1 x (mem_map_of_mem H.subtype hx))
  have hRF : R ≤ centralizer (fittingSubgroup H : Set H) :=
    (inverted_odd_le_commutator R hodd zH hiR).trans
      (commutator_top_le_centralizer_fitting zH hzcore hiO)
  have hRE : R ≤ centralizer (componentLayer H : Set H) := by
    intro x hx y hy
    exact Subtype.ext (hlayer hx y (mem_map_of_mem H.subtype hy))
  have hRstar : R ≤ centralizer (generalizedFitting H : Set H) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hRF) (le_centralizer_iff.mp hRE)
  have hRcore := odd_le_core_of_centralizes_fStar R hodd hRstar
  intro x hx
  exact mem_map_of_mem H.subtype (hRcore (show (⟨x, hRH hx⟩ : H) ∈ R from hx))

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.OddCore
