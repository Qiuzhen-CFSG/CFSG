module
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LeviSemilinear
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Extensions
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Detecting two-elements by their triality local action

The positive Sylow subgroup lies in each root-defined local residual.
Frattini's argument and its proved Borel normalizer identify the normalizer
of that residual with its actual parabolic. Inner–coefficient coverage thus
has its inner factor in this parabolic whenever it stabilizes the residual.

On the arms quotient an inner coefficient action is trivial; on the central
quotient its cube is trivial. Consequently every local-inner two-element is
inner on the whole carrier. Centerlessness lifts its two-power relation, and
the prime-to-two residual absorbs the resulting parabolic two-element.
This proves containment in the actual local conjugation image, including
q = 2, without assuming the desired core equality.

Source: Aschbacher–Smith F.1.12, printed p.264 (`refs/quasithin.pdf`);
GLS3 2.5.12 and §2.6 (`refs/KGroup/GLS3/chapter2.tex`). The coefficient field
remains GF(q³); the order-three central kernel is removed only for two-elements.
-/

public section
noncomputable section
namespace Triality.Standard.ParabolicOuterTwo
open Parabolics OuterOdd Subgroup

/-- The local residual has precisely its root parabolic as carrier normalizer. -/
theorem normalizer_localFactor (P : Parameters) (hp : P.prime = 2) (a : Node) :
    normalizer (localFactor P a) = parabolic P a := by
  apply le_antisymm
  · have h := le_normalizer_sylow_sup (localFactor P a) (normalizer (localFactor P a))
      (localFactor P a).le_normalizer le_rfl
      ((unipotentSylow P hp).subtype (unipotentSylow_le_localFactor P hp a))
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (unipotentSylow_le_localFactor P hp a),
      coe_unipotentSylow, ConcreteBruhat.normalizer_unipotent_eq_borel P hp] at h
    exact h.trans (sup_le (borel_le_parabolic P a) (localFactor_le_parabolic P a))
  · exact (normal_subgroupOf_iff_le_normalizer (localFactor_le_parabolic P a)).mp
      (localFactor_normal P a)

/-- Coverage with its inner factor in the actual parabolic. -/
theorem localStabilizer_inner_coefficient (n : ℕ) (hn : 0 < n) (a : Node)
    (σ : localStabilizer (binaryParameters n hn) a) :
    ∃ g : parabolic (binaryParameters n hn) a,
      ∃ e : CoefficientAut (binaryParameters n hn),
        σ = parabolicInner _ a g * coefficientStabilizer _ a e := by
  let P := binaryParameters n hn
  obtain ⟨g, e, he⟩ := Coverage.binary_inner_coefficient n hn σ.val
  have hg : g ∈ parabolic P a := by
    rw [← normalizer_localFactor P rfl a]
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      (localFactor P a).map (MulAut.conj g).toMonoidHom =
          ((localFactor P a).map (coefficientAction P e).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by
              rw [show (localFactor P a).map (coefficientAction P e).toMonoidHom =
                localFactor P a from coefficient_localFactor P e a]
      _ = (localFactor P a).map σ.val.toMonoidHom := by
        rw [map_map, he]
        rfl
      _ = localFactor P a := σ.property
  exact ⟨⟨g, hg⟩, e, Subtype.ext he⟩

/-- The local inner-action kernel has odd outer image, with the cubic convention retained. -/
theorem local_inner_outer_cube (n : ℕ) (hn : 0 < n) (a : Node)
    (σ : localStabilizer (binaryParameters n hn) a)
    (h : localQuotientAction _ a σ ∈ MulAut.innerSubgroup (LocalTwoQuotient _ a)) :
    (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier n hn)) σ.val) ^ 3 = 1 := by
  let P := binaryParameters n hn
  obtain ⟨g, e, he⟩ := localStabilizer_inner_coefficient n hn a σ
  have he3 : e ^ 3 = 1 := by
    rw [he] at h
    cases a with
    | arms => rw [coefficient_eq_one_of_parabolic_mul_arms_inner P rfl g e h, one_pow]
    | central => exact coefficient_cube_eq_one_of_parabolic_mul_central_inner P rfl g e h
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Carrier P))
  have hq : q σ.val = outerCoefficientAction P e := by
    have hg : q (MulAut.conj g.val) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g.val, rfl⟩
    change q σ.val = q (coefficientAction P e)
    have hv := congrArg Subtype.val he
    change σ.val = MulAut.conj g.val * coefficientAction P e at hv
    rw [hv, map_mul, hg, one_mul]
  change q σ.val ^ 3 = 1
  rw [hq, ← map_pow, he3, map_one]

/-- A two-element inducing an inner local action is conjugation by a local element. -/
theorem local_inner_twoElement (n : ℕ) (hn : 0 < n) (a : Node)
    (σ : localStabilizer (binaryParameters n hn) a) (k : ℕ)
    (hσ : σ ^ (2 ^ k) = 1)
    (h : localQuotientAction _ a σ ∈ MulAut.innerSubgroup (LocalTwoQuotient _ a)) :
    σ ∈ (localInner (binaryParameters n hn) a).range := by
  let P := binaryParameters n hn
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Carrier P))
  have htwo : q σ.val ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    exact (congrArg q (congrArg Subtype.val hσ)).trans (map_one q)
  have hthree := local_inner_outer_cube n hn a σ h
  have hq : q σ.val = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left k)
      (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hthree))
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff σ.val).mp hq
  have hgp : g ∈ parabolic P a := by
    rw [← normalizer_localFactor P rfl a]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hg]
    exact σ.property
  have hinj : Function.Injective (MulAut.conj : Carrier P →* MulAut (Carrier P)) := by
    intro x y hxy
    apply carrierEmbedding_injective n hn ⊤ le_top
    exact Subtype.ext hxy
  have hpow : g ^ (2 ^ k) = 1 := by
    apply hinj
    rw [map_pow, hg, map_one]
    exact congrArg Subtype.val hσ
  have hgl := mem_localFactor_of_pow P a g hgp k hpow
  exact ⟨⟨g, hgl⟩, Subtype.ext hg⟩

end Triality.Standard.ParabolicOuterTwo
