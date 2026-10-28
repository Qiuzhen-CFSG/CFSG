module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelGeometry
public import Theory.SpecificGroups.SL2.TwoCoreBorel

/-!
# Sylow and odd-subgroup fixers of a natural block

An automorphism fixing a Sylow subgroup of a natural L₂ block has
its displacement in the full U-layer. Averaging the displacement cocycle
over the odd Sylow index makes it inner by a vector in U. Fixing any
nontrivial odd subgroup then makes that vector central. The ambient
version retains only normalization of the block by the actor.

The actual Sylow Borel also has an odd subgroup of order 2ⁿ−1, obtained
by lifting its diagonal quotient through the two-group kernel. These
facts apply to central covers and supply the marked-torus argument in
original 15.1.20(2a), printed pp.1094--1095; the cover geometry is I.2.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow subgroup and any nontrivial odd subgroup detect every automorphism. -/
theorem IsL2EvenBlock.sylow_odd_fixer {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L) (D : Subgroup L)
    (ho : Odd (Nat.card D)) (hne : D ≠ ⊥) (a : MulAut L)
    (hP : ∀ x ∈ P, a x = x) (hD : ∀ x ∈ D, a x = x) : a = 1 := by
  let U := blockU L
  let : IsElementaryAbelian 2 U := hb.2.1.elementary
  have hU (u : L) (hu : u ∈ U) : a u = u :=
    hP u (pCore_isPGroup.le_sylow_of_normal P (blockU_le_core hu))
  have hdcore (x : L) : a x * x⁻¹ ∈ pCore 2 L := by
    have hh := hb.2.1.centralizer_blockU.le
      (Theory.GroupAction.NormalizerGeneratingFixer.displacement_mem_centralizer U a
        hU x⁻¹ (by rw [normalizer_eq_top]; trivial))
    simpa only [inv_inv,map_inv,mul_inv_rev] using (pCore 2 L).inv_mem hh
  have hd (x : L) : a x * x⁻¹ ∈ U := by
    have he := DFunLike.congr_fun (hb.2.1.quotient_blockU_aut_eq_one a hdcore)
      (QuotientGroup.mk' U x)
    rw [quotientAut_apply_mk] at he
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  let c (x : L) : U := ⟨a x * x⁻¹,hd x⟩
  let ρ : L →* MulAut U := MulAut.conjNormal
  have hc (x y : L) : c (x*y) = c x * ρ x (c y) := by
    apply Subtype.ext
    change a (x*y)*(x*y)⁻¹ = (a x*x⁻¹)*(x*(a y*y⁻¹)*x⁻¹)
    simp only [map_mul,mul_inv_rev]
    group
  obtain ⟨v,hv⟩ := binary_cocycle_trivial_of_sylow ρ c hc
    (fun u => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (u : L) u.property)) P
    (fun x hx => Subtype.ext (by change a x*x⁻¹=1; rw [hP x hx,mul_inv_cancel]))
  have hvC : (v : L) ∈ centralizer (D : Set L) := by
    intro x hx
    have he := congrArg Subtype.val (hv x)
    change (x*(v : L)*x⁻¹)*(a x*x⁻¹)=(v : L) at he
    rw [hD x hx,mul_inv_cancel,mul_one] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hvZ : (v : L) ∈ center L := hb.blockU_odd_fixed_le_center D ho hne ⟨v.property,hvC⟩
  ext x
  have he := congrArg Subtype.val (hv x)
  change (x*(v : L)*x⁻¹)*(a x*x⁻¹)=(v : L) at he
  rw [mem_center_iff.mp hvZ x,mul_inv_cancel_right] at he
  have he' : a x*x⁻¹=1 := mul_left_cancel (he.trans (mul_one (v : L)).symm)
  exact mul_inv_eq_one.mp he'

/-- Normalizing actors fixing a full Sylow and a nontrivial odd subgroup fix the block. -/
theorem IsL2EvenBlock.centralizes_of_sylow_odd_fixed (K V D : Subgroup G)
    {n : ℕ} (hb : IsL2EvenBlock K n) (P : Sylow 2 K)
    (hn : V ≤ normalizer (K : Set G))
    (hP : (P : Subgroup K).map K.subtype ≤ centralizer (V : Set G))
    (hDK : D ≤ K) (ho : Odd (Nat.card D)) (hne : D ≠ ⊥)
    (hD : D ≤ centralizer (V : Set G)) : K ≤ centralizer (V : Set G) := by
  have ho' : Odd (Nat.card (D.subgroupOf K)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv]
  have hne' : D.subgroupOf K ≠ ⊥ := by
    intro he
    apply hne
    simpa only [map_subgroupOf_eq_of_le hDK,Subgroup.map_bot] using congrArg (map K.subtype) he
  intro k hk v hv
  let a := K.normalizerMonoidHom ⟨v,hn hv⟩
  have he : a = 1 := hb.sylow_odd_fixer P (D.subgroupOf K) ho' hne' a
    (by
      intro x hx
      apply Subtype.ext
      change v*(x : G)*v⁻¹=(x : G)
      exact mul_inv_eq_iff_eq_mul.mpr ((hP (mem_map_of_mem K.subtype hx)) v hv))
    (by
      intro x hx
      apply Subtype.ext
      change v*(x : G)*v⁻¹=(x : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hD hx v hv))
  have he' := congrArg Subtype.val (DFunLike.congr_fun he (⟨k,hk⟩ : K))
  change v*k*v⁻¹=k at he'
  exact mul_inv_eq_iff_eq_mul.mp he'

/-- An odd complement of the actual Sylow Borel has the full torus order. -/
theorem IsL2EvenBlock.exists_odd_borel_torus {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hb : IsL2EvenBlock L n) (P : Sylow 2 L) :
    ∃ D : Subgroup L, D ≤ normalizer (P : Set L) ∧ Odd (Nat.card D) ∧
      Nat.card D = 2 ^ n - 1 := by
  obtain ⟨hn,_,F,_,_,hF,_,r,⟨m⟩,_⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup L) := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  obtain ⟨f,hf,hker⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal q hq P hk
  let N := normalizer (P : Set L)
  have hp : IsPGroup 2 f.ker := by
    have heK : f.ker = (P : Subgroup L).subgroupOf N := by
      ext x
      exact hker x
    rw [heK]
    exact P.isPGroup'.comap_subtype
  have ho : Odd (Nat.card (⊤ : Subgroup Fˣ)) := by
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_units,hF]
    exact Nat.Even.sub_odd (by have := Nat.one_le_pow n 2 (by decide); omega)
      (even_two.pow_of_ne_zero (by omega)) odd_one
  obtain ⟨D,_,_,hcard,_⟩ := f.exists_odd_subgroup_lift hf hp ⊤ ho
  refine ⟨D.map N.subtype,map_subtype_le _,?_,?_⟩
  · rwa [card_map_of_injective N.subtype_injective,hcard]
  · rw [card_map_of_injective N.subtype_injective,hcard,
      Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_units,hF]

end CFSG.Quasithin.ChapterC
