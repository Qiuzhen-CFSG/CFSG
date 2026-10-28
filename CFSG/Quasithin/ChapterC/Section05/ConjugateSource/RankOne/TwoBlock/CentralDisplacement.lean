module
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.PPerfectHom
public import Theory.ElementaryAbelian.Basic

/-!
# Averaging displacement through the genuine central cover

For P centralizing the binary module U and [K,P]≤U, three subgroups gives
[P,P]≤C(K). If a Sylow actor of K agrees modulo P with an actor fixing c,
its displacement on c is therefore central in K. Averaging the induced
cocycle on U/C_U(K) gives a fixed coset. Two-perfection kills the remaining
central displacement, yielding an actual K-fixed representative in Uc.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160 (the second
Gaschütz step). This formulation keeps the literal central cover.
-/
public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G W : Type*} [Group G] [CommGroup W]

/-- Sylow-fixed quotient displacement lifts to an actually fixed U-coset. -/
theorem fixed_coset_mod_central_kernel_of_sylow
    (K U P : Subgroup G) [Finite K] [IsElementaryAbelian 2 U]
    (hKU : K ≤ normalizer (U : Set G)) (hK : IsPPerfect 2 K)
    (hPU : P ≤ centralizer (U : Set G)) (hKP : ⁅K,P⁆ ≤ U)
    (q : U →* W) (hq : Function.Surjective q)
    (hk : ∀ u : U, q u = 1 ↔ (u : G) ∈ centralizer (K : Set G))
    (ρ : K →* MulAut W)
    (hρ : ∀ k u, ρ k (q u) = q (U.normalizerMonoidHom (inclusion hKU k) u))
    (T : Sylow 2 K) (c : G) (hc : c ∈ P)
    (hmatch : ∀ k : K, k ∈ T → ∃ v : G, Commute v c ∧ (k : G) * v⁻¹ ∈ P) :
    ∃ u ∈ U, u * c ∈ centralizer (K : Set G) := by
  have htriple : ⁅⁅K,P⁆,P⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hKP.trans (le_centralizer_iff.mp hPU))
  have hPP : ⁅P,P⁆ ≤ centralizer (K : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (commutator_commutator_eq_bot_of_rotate
      (by rwa [commutator_comm P K]) htriple)
  let d : K → U := fun k => ⟨⁅(k : G),c⁆,hKP (commutator_mem_commutator k.property hc)⟩
  let τ : K →* MulAut U := U.normalizerMonoidHom.comp (inclusion hKU)
  have hτρ (k : K) (u : U) : ρ k (q u) = q (τ k u) := hρ k u
  have hd (k l : K) : d (k*l) = d k * τ k (d l) := by
    apply Subtype.ext
    have he := mul_comm (d k) (τ k (d l))
    rw [he]
    change ((k : G)*(l : G))*c*((k : G)*(l : G))⁻¹*c⁻¹ =
      ((k : G)*((l : G)*c*(l : G)⁻¹*c⁻¹)*(k : G)⁻¹)*((k : G)*c*(k : G)⁻¹*c⁻¹)
    group
  have hdq (k l : K) : q (d (k*l)) = q (d k) * ρ k (q (d l)) := by
    rw [hd,map_mul,← hτρ]
  have hT (k : K) (hkT : k ∈ T) : q (d k) = 1 := by
    apply (hk _).mpr
    obtain ⟨v,hvc,hv⟩ := hmatch k hkT
    have he : ⁅(k : G),c⁆ = ⁅(k : G)*v⁻¹,c⁆ := by
      have hh := hvc.inv_left.eq
      simp only [commutatorElement_def,mul_inv_rev,inv_inv]
      calc
        _ = (k : G)*(v⁻¹*c*v)*(k : G)⁻¹*c⁻¹ := by rw [hh]; group
        _ = _ := by group
    change ⁅(k : G),c⁆ ∈ centralizer (K : Set G)
    rw [he]
    exact hPP (commutator_mem_commutator hv hc)
  have hW (w : W) : w^2=1 := by
    obtain ⟨u,rfl⟩ := hq w
    rw [← map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 U) u,map_one]
  obtain ⟨w,hw⟩ := binary_cocycle_trivial_of_sylow ρ (fun k => q (d k)) hdq hW T hT
  obtain ⟨u,hu⟩ := hq w
  let z := (u : G)*c
  have hdz (k : K) : ⁅(k : G),z⁆ ∈ U := by
    have he : ⁅(k : G),z⁆ = (τ k u : U) * d k * u⁻¹ := by
      change (k : G)*((u : G)*c)*(k : G)⁻¹*((u : G)*c)⁻¹ =
        ((k : G)*(u : G)*(k : G)⁻¹)*((k : G)*c*(k : G)⁻¹*c⁻¹)*(u : G)⁻¹
      group
    rw [he]
    exact (τ k u * d k * u⁻¹).property
  let dz : K → U := fun k => ⟨⁅(k : G),z⁆,hdz k⟩
  have hform (k : K) : dz k = τ k u * d k * u⁻¹ := by
    apply Subtype.ext
    change (k : G)*((u : G)*c)*(k : G)⁻¹*((u : G)*c)⁻¹ =
      ((k : G)*(u : G)*(k : G)⁻¹)*((k : G)*c*(k : G)⁻¹*c⁻¹)*(u : G)⁻¹
    group
  have hcentral (k : K) : (dz k : G) ∈ centralizer (K : Set G) := by
    apply (hk _).mp
    rw [hform,map_mul,map_mul,map_inv,← hτρ,hu,hw,mul_inv_cancel]
  let f : K →* U := {
    toFun := dz
    map_one' := by apply Subtype.ext; simp [dz,commutatorElement_def]
    map_mul' := by
      intro k l
      apply Subtype.ext
      have hh := hcentral l k k.property
      change (k : G)*((l : G)*z*(l : G)⁻¹*z⁻¹) = ((l : G)*z*(l : G)⁻¹*z⁻¹)*(k : G) at hh
      change ((k : G)*(l : G))*z*((k : G)*(l : G))⁻¹*z⁻¹ =
        ((k : G)*z*(k : G)⁻¹*z⁻¹)*((l : G)*z*(l : G)⁻¹*z⁻¹)
      have hcU := mul_comm (dz k) (dz l)
      rw [show ((k : G)*z*(k : G)⁻¹*z⁻¹)*((l : G)*z*(l : G)⁻¹*z⁻¹) =
        ((l : G)*z*(l : G)⁻¹*z⁻¹)*((k : G)*z*(k : G)⁻¹*z⁻¹) from congrArg Subtype.val hcU]
      calc
        _ = ((k : G)*((l : G)*z*(l : G)⁻¹*z⁻¹))*(k : G)⁻¹*((k : G)*z*(k : G)⁻¹*z⁻¹) := by group
        _ = _ := by rw [hh]; group }
  have hf := hK.hom_eq_one_of_isPGroup (IsElementaryAbelian.isPGroup (p := 2) (G := U)) f
  refine ⟨u,u.property,?_⟩
  intro k hkK
  have he := congrArg Subtype.val (DFunLike.congr_fun hf (⟨k,hkK⟩ : K))
  exact commutatorElement_eq_one_iff_mul_comm.mp he
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
