module
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Centralizer detection by a cyclic omega center

A nontrivial normal subgroup of a finite p-group contains a central subgroup
of order p. If the first omega subgroup of the center has order p, it is
therefore contained in every nontrivial normal subgroup. A normalized actor
which does not centralize that omega subgroup has trivial centralizer.

For a subgroup L, apply this argument in its literal faithful normalizer
quotient N(L)/C(L). It identifies C_S(Y) with C_S(L), provided the first
omega subgroup of the center of N_S(L)'s image has order two and is not
centralized by Y's image. When L is an ordinary component, the needed
normalization by C_S(Y) follows from component commutation; S need not
normalize L.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.1.22(**), printed p.1099. The source consumer supplies the
actual model's omega-center order and residual noncentralization.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Every nontrivial normal subgroup contains the first omega center when
that omega center has prime order. -/
theorem omega_center_le_normal_of_card_eq_prime {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (hcard : Nat.card (omega₁ (center G) (p := p)) = p)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) :
    (omega₁ (center G) (p := p)).map (center G).subtype ≤ N := by
  let : Fact (IsPGroup p G) := ⟨hp⟩
  obtain ⟨Z, _, hZN, hZcard, hZc⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := p) N
      ((nontrivial_iff_ne_bot N).mpr hne)
  have hZO : Z ≤ (omega₁ (center G) (p := p)).map (center G).subtype := by
    intro z hz
    refine ⟨⟨z, hZc hz⟩, subset_closure ?_, rfl⟩
    change (⟨z, hZc hz⟩ : center G) ^ (p ^ 1) = 1
    apply Subtype.ext
    change z ^ (p ^ 1) = 1
    have he := congrArg Z.subtype (pow_card_eq_one' (x := (⟨z,hz⟩ : Z)))
    change z ^ Nat.card Z = 1 at he
    simpa only [hZcard, pow_one] using he
  have he := eq_of_le_of_card_ge hZO (by
    rw [card_map_of_injective (center G).subtype_injective, hcard, hZcard])
  exact he ▸ hZN

/-- A normalized actor moving a prime-order omega center has trivial
centralizer in the finite p-group. -/
theorem inf_centralizer_eq_bot_of_omega_center_escape {p : ℕ} [Fact p.Prime]
    (S Y : Subgroup G) (hp : IsPGroup p S)
    (hSY : S ≤ normalizer (Y : Set G))
    (hcard : Nat.card (omega₁ (center S) (p := p)) = p)
    (hescape : ¬ ((omega₁ (center S) (p := p)).map (center S).subtype).map
      S.subtype ≤ centralizer (Y : Set G)) :
    S ⊓ centralizer (Y : Set G) = ⊥ := by
  let D := (centralizer (Y : Set G)).subgroupOf S
  let n : S →* normalizer (Y : Set G) := inclusion hSY
  let : D.Normal :=
    (normal_subgroupOf_centralizer_normalizer (Y : Set G)).comap n
  have hD : D = ⊥ := by
    by_contra hne
    have hO := omega_center_le_normal_of_card_eq_prime hp hcard D hne
    apply hescape
    rintro _ ⟨x, hx, rfl⟩
    exact hO hx
  apply bot_unique
  rintro x ⟨hxS,hxY⟩
  have hx : (⟨x,hxS⟩ : S) ∈ D := hxY
  rw [hD, mem_bot] at hx
  exact congrArg Subtype.val hx
end Subgroup

namespace Subgroup.NormalizerAction
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The normalizer-quotient centralizer argument with the exact
normalization needed for the subgroup being killed. -/
theorem centralizer_eq_of_omega_center_escape
    (L S Y : Subgroup G) (hS : IsPGroup 2 S)
    (hDn : S ⊓ centralizer (Y : Set G) ≤ normalizer (L : Set G))
    (hSY : S ⊓ normalizer (L : Set G) ≤ normalizer (Y : Set G)) (hYL : Y ≤ L)
    (hcard : Nat.card (omega₁ (center (sylowImage L S)) (p := 2)) = 2)
    (hescape : ¬ ((omega₁ (center (sylowImage L S)) (p := 2)).map
      (center (sylowImage L S)).subtype).map (sylowImage L S).subtype ≤
      centralizer ((Y.subgroupOf (normalizer (L : Set G))).map (quotient L) :
        Set (Star L))) :
    S ⊓ centralizer (Y : Set G) = S ⊓ centralizer (L : Set G) := by
  let Ystar := (Y.subgroupOf (normalizer (L : Set G))).map (quotient L)
  have hSp : IsPGroup 2 (sylowImage L S) :=
    (hS.comap_of_injective (normalizer (L : Set G)).subtype
      (normalizer (L : Set G)).subtype_injective).map (quotient L)
  have hSn : sylowImage L S ≤ normalizer (Ystar : Set (Star L)) := by
    have hn : S.subgroupOf (normalizer (L : Set G)) ≤
        (normalizer (Y : Set G)).subgroupOf (normalizer (L : Set G)) :=
      fun x hx => hSY ⟨hx,x.property⟩
    exact (map_mono (hn.trans (le_normalizer_comap _))).trans (le_normalizer_map _)
  have hbot := inf_centralizer_eq_bot_of_omega_center_escape
    (sylowImage L S) Ystar hSp hSn hcard hescape
  apply le_antisymm
  · rintro x ⟨hxS, hxY⟩
    refine ⟨hxS, ?_⟩
    let xN : normalizer (L : Set G) := ⟨x,hDn ⟨hxS,hxY⟩⟩
    apply (quotient_eq_one_iff L xN).mp
    have hx : quotient L xN ∈ sylowImage L S ⊓ centralizer (Ystar : Set (Star L)) := by
      refine ⟨⟨xN,hxS,rfl⟩,mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨y,hy,rfl⟩
      have he : y * xN = xN * y := Subtype.ext ((mem_centralizer_iff.mp hxY) y.val hy)
      simpa only [map_mul] using congrArg (quotient L) he
    rwa [hbot,mem_bot] at hx
  · exact inf_le_inf_left S (centralizer_le hYL)
end Subgroup.NormalizerAction

namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G]

/-- Centralizing a subgroup noncentral in an ordinary component forces
normalization of that component. -/
theorem IsComponent.centralizer_le_normalizer_of_noncentral
    {L : Subgroup G} (hL : IsComponent G L) (Y : Subgroup G)
    (hYL : Y ≤ L) (hYc : ¬ Y ≤ centralizer (L : Set G)) :
    centralizer (Y : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro x hxY
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hconj := hL.map_conj x
  have hc := hL.commutator_eq_bot_of_ne hconj (Ne.symm hne)
  apply hYc
  apply le_centralizer_iff.mp
  apply (commutator_eq_bot_iff_le_centralizer.mp hc).trans
  apply centralizer_le
  intro y hy
  have hf : MulAut.conj x y = y := by
    change x * y * x⁻¹ = y
    rw [← mem_centralizer_iff.mp hxY y hy, mul_inv_cancel_right]
  exact hf ▸ mem_map_of_mem (MulAut.conj x).toMonoidHom (hYL hy)
end Theory.GroupTheory

namespace Subgroup.NormalizerAction
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- An ordinary component supplies the centralizer normalization in the
faithful-image argument, without requiring S to normalize the component. -/
theorem component_centralizer_eq_of_omega_center_escape
    (L S Y : Subgroup G) (hL : IsComponent G L)
    (hS : IsPGroup 2 S)
    (hSY : S ⊓ normalizer (L : Set G) ≤ normalizer (Y : Set G)) (hYL : Y ≤ L)
    (hcard : Nat.card (omega₁ (center (sylowImage L S)) (p := 2)) = 2)
    (hescape : ¬ ((omega₁ (center (sylowImage L S)) (p := 2)).map
      (center (sylowImage L S)).subtype).map (sylowImage L S).subtype ≤
      centralizer ((Y.subgroupOf (normalizer (L : Set G))).map (quotient L) :
        Set (Star L))) :
    S ⊓ centralizer (Y : Set G) = S ⊓ centralizer (L : Set G) := by
  have hYc : ¬ Y ≤ centralizer (L : Set G) := by
    intro hc
    apply hescape
    intro a _
    apply mem_centralizer_iff.mpr
    rintro _ ⟨y,hy,rfl⟩
    rw [(quotient_eq_one_iff L y).mpr (hc hy),one_mul,mul_one]
  exact centralizer_eq_of_omega_center_escape L S Y hS
    (inf_le_right.trans (hL.centralizer_le_normalizer_of_noncentral Y hYL hYc))
    hSY hYL hcard hescape
end Subgroup.NormalizerAction
