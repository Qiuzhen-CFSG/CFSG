module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Cardinality
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ExceptionalArithmetic
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.AbelianFrobeniusDegree
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.ActionContract
public import FeitThompson.PFsection6.PFsection6_5_a

/-!
# Excluding the Frobenius branch of the odd normalizer

A nontrivial abelian prime-power kernel acted on freely by the split torus
forces the faithful binary degree to be at least q-1. The actual Sylow
quotient has degree 2n+1, so q=8. Orbit counting then contradicts the
prime-power divisor sieve in the source point stabilizer.

The faithful action and the kernel must be constructed by the odd-normalizer
argument; this module supplies its terminal contradiction.
Source: GLS4, Chapter 2, Lemma 14.9, final two paragraphs,
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section

open Subgroup
open scoped IsMulCommutative
namespace BenderSuzuki.ZD.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem Context.no_frobenius_action
    (d : Context Z M z t m)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294)
    {H V : Type*} [Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) H V) (hrho : Function.Injective rho)
    (hcardV : Nat.card V = (2 ^ (2 * m + 1)) ^ 2 * 2)
    (hcardH : Nat.card H ∣ Nat.card M)
    (R K : Subgroup H) [IsMulCommutative R]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hR : IsPGroup p R) (hne : R ≠ ⊥)
    (hK : Nat.card K = 2 ^ (2 * m + 1) - 1)
    (hnorm : K ≤ normalizer (R : Set H))
    (hfree : ∀ k : K, k ≠ 1 → ∀ r : R,
      (k : H) * r * (k : H)⁻¹ = r → r = 1) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  have ha0 : 0 < a := by
    have hc := Finite.one_lt_card (α := R)
    rw [ha] at hc
    by_contra hn
    simp [show a = 0 by omega] at hc
  have hodd : Odd (Nat.card R) := by
    rw [ha]
    exact (hp.odd_of_ne_two hp2).pow
  have horder : (Nat.card R : ZMod 2) ≠ 0 := by
    intro hzero
    have heven := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr heven)
  have hdeg := Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field
    rho R K hrho horder hnorm hfree
  have hdim : Module.finrank (ZMod 2) V = 2 * (2 * m + 1) + 1 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod, hcardV] at hc
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ Module.finrank (ZMod 2) V = 2 ^ (2 * (2 * m + 1) + 1)
    calc
      2 ^ Module.finrank (ZMod 2) V = (2 ^ (2 * m + 1)) ^ 2 * 2 := hc.symm
      _ = 2 ^ ((2 * m + 1) * 2) * 2 := by rw [pow_mul]
      _ = 2 ^ ((2 * m + 1) * 2 + 1) := by rw [pow_add, pow_one]
      _ = 2 ^ (2 * (2 * m + 1) + 1) := by congr 1; omega
  rw [hK, hdim] at hdeg
  have hm : m = 1 := parameter_eq_one_of_degree_bound d.parameter_pos hdeg
  subst m
  let : MulDistribMulAction K R := conjMulDistribMulActionOfLeNormalizer K R hnorm
  have hcong := Section6.natCard_actor_dvd_group_card_sub_one (fun k hk r hr =>
    hfree k hk r (congrArg Subtype.val hr))
  rw [hK, ha] at hcong
  norm_num at hcong
  exact d.no_odd_primePower_congruence_at_eight (hD8 rfl) hp hp2 ha0
    (ha ▸ R.card_subgroup_dvd_card.trans hcardH) hcong

/-- The Frobenius contradiction applied to the actual normalizer quotient
and its conjugation action on the actual image of S. -/
public theorem Context.no_quotient_frobenius_kernel
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294)
    (a : OddNormalizer.ActionData d g)
    (R : Subgroup (OddNormalizer.quotient g)) [IsMulCommutative R]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hR : IsPGroup p R) (hne : R ≠ ⊥)
    (hnorm : OddNormalizer.torusImage g ≤ normalizer (R : Set (OddNormalizer.quotient g)))
    (hfree : ∀ k : OddNormalizer.torusImage g, k ≠ 1 → ∀ r : R,
      (k : OddNormalizer.quotient g) * r * (k : OddNormalizer.quotient g)⁻¹ = r → r = 1) :
    False := by
  let E := OddNormalizer.sylowImage d g
  let : IsElementaryAbelian 2 E := he
  let autLinear : MulAut E →* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun b => { b.toAdditive with map_smul' := ZMod.map_smul b.toAdditive }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  let rho : Representation (ZMod 2) (OddNormalizer.quotient g) (Additive E) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (autLinear.comp a.action)
  have hfaith : Function.Injective rho := by
    intro x y hxy
    apply a.faithful
    ext v
    exact congrArg (fun w : Additive E => (w.toMul : OddNormalizer.pointQuotient d))
      (LinearMap.congr_fun hxy (Additive.ofMul v))
  have hcard : Nat.card (Additive E) = (2 ^ (2 * m + 1)) ^ 2 * 2 := by
    change Nat.card (OddNormalizer.sylowImage d g) = _
    exact (d.card_quotient_S g s).trans (by rw [hU])
  exact d.no_frobenius_action hD8 rho hfaith hcard (OddNormalizer.quotient_card_dvd g)
    R (OddNormalizer.torusImage g) hp hp2 hR hne a.torus_card hnorm hfree

end BenderSuzuki.ZD.SuzukiExclusion
