module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.QuotientLifting
public import Theory.GroupTheory.ConjugacyClassSize
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# The quotient two-central obstruction in the linear branch

An involution of J cannot have two-central image in M/A. Its centralizer
lies in N_M(L), whose index is q². The inverse image of the centralizer of
its quotient image has odd index. Its conjugacy orbit in the fiber has at
most |A|=q elements, forcing q² to divide a positive integer at most q.
This is the centralizer-index contradiction in GLS IV, Chapter 2, Lemma
15.4, using the literal distinguished quotient M/A.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open Theory.GroupTheory.DoubleCoverCentralizer

private theorem centralizer_fiber_index_le
    {E Q : Type*} [Group E] [Group Q] [Finite E]
    (f : E →* Q) (v : E) :
    (centralizer ({v} : Set E)).relIndex
      ((centralizer ({f v} : Set Q)).comap f) ≤ Nat.card f.ker := by
  let H := (centralizer ({f v} : Set Q)).comap f
  have hvH : v ∈ H := mem_centralizer_singleton_iff.mpr rfl
  let w : H := ⟨v, hvH⟩
  have hC : centralizer ({w} : Set H) = (centralizer ({v} : Set E)).subgroupOf H := by
    ext a
    simp only [mem_centralizer_singleton_iff, mem_subgroupOf]
    exact Subtype.ext_iff
  have hmap (x : (ConjClasses.mk w).carrier) : f (x : H) = f v := by
    have hc : IsConj w (x : H) := x.property
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    have he := congrArg (fun a : H => f a) hg
    have hcomm := mem_centralizer_singleton_iff.mp g.property
    change f ((g : E) * v * (g : E)⁻¹) = f (x : H) at he
    rw [map_mul, map_mul, map_inv, hcomm, mul_inv_cancel_right] at he
    exact he.symm
  let j : (ConjClasses.mk w).carrier → f.ker := fun x =>
    ⟨(x : H) * v⁻¹, by change f ((x : H) * v⁻¹) = 1; rw [map_mul, map_inv, hmap x, mul_inv_cancel]⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun a : f.ker => (a : E)) he
    exact mul_right_cancel hh
  have hb := Nat.card_le_card_of_injective j hj
  rwa [ConjClasses.nat_card_carrier_eq_index_centralizer, hC] at hb

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d
local notation "A" => closure (Z ∩ (M : Set G))
local notation "L" => residualGenerated M z t
local notation "J" => centralizer (L : Set G)

/-- The image in M/A of an actual centralizer involution is never two-central. -/
public theorem Context.centralizer_involution_image_not_twoCentral
    (v : M) (hvJ : (v : G) ∈ J) (hv : PFAppendixIII.IsInvolution v) :
    let : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
    ¬ TwoCentral (QuotientGroup.mk' ((A).subgroupOf M) v) := by
  let : ((A).subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let q := QuotientGroup.mk' ((A).subgroupOf M)
  let C := centralizer ({v} : Set M)
  let H := (centralizer ({q v} : Set (M ⧸ (A).subgroupOf M))).comap q
  let N := (normalizer (L : Set G)).subgroupOf M
  dsimp only
  intro htc
  have hC : C ≤ H := by
    intro c hc
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg q (mem_centralizer_singleton_iff.mp hc)
  have hCN : C ≤ N := by
    intro c hc
    exact d.involution_centralizer_le hvJ
      (BenderSuzuki.IsInvolution.map_of_injective hv M.subtype M.subtype_injective)
      (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mem_centralizer_singleton_iff.mp hc)))
  have hNi : N.index = (2 ^ n) ^ 2 := by
    change (normalizer (L : Set G)).relIndex M = _
    rw [← inf_relIndex_right, inf_comm]
    exact d.point_normalizer_index
  have hHi : ¬ 2 ∣ H.index := by
    rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact htc.not_dvd_centralizer_index
  have hd : (2 ^ n) ^ 2 ∣ C.relIndex H := by
    have hh : (2 ^ n) ^ 2 ∣ C.relIndex H * H.index := by
      rw [relIndex_mul_index hC, ← hNi]
      exact index_dvd_of_le hCN
    have hcop : Nat.Coprime ((2 ^ n) ^ 2) H.index :=
      ((Nat.prime_two.coprime_iff_not_dvd.mpr hHi).pow_left n).pow_left 2
    exact hcop.dvd_of_dvd_mul_right hh
  have hb : C.relIndex H ≤ 2 ^ n := by
    have hh := centralizer_fiber_index_le q v
    rw [QuotientGroup.ker_mk', Nat.card_congr
      (subgroupOfEquivOfLe (show A ≤ M from distinguishedClosure_le)).toEquiv,
      d.distinguished_elementary_card.2] at hh
    exact hh
  have hp : 0 < C.relIndex H := Nat.pos_of_ne_zero (C.subgroupOf H).index_ne_zero_of_finite
  have hpow : (2 ^ n) ^ 2 ≤ 2 ^ n := (Nat.le_of_dvd hp hd).trans hb
  have hn : 2 ≤ n := d.parameter
  have hq : 1 < 2 ^ n := Nat.one_lt_pow (by omega) (by decide)
  nlinarith

end BenderSuzuki.ZD.LinearExclusion
