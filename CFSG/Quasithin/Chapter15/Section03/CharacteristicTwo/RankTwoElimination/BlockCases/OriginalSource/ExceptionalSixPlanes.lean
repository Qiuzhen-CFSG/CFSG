module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Ahat6
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.ElementaryAbelian.Injective
public import Mathlib.Data.Fintype.Perm
public import Theory.Representation.TripleSixFixedSpace
public import Theory.Representation.GeneralLinearNatural

/-!
# The marked four-groups in an exceptional Â₆ block

A nontrivial central cubic has no fixed vector on the actual U. A four-group
invariant under that cubic is therefore centralized by every commuting actor
whose fourth power is trivial. The faithful three-dimensional F₄ restriction
then shows that a quotient element of order four fixes at most four vectors.
Every component Sylow contains a lift of such an element.

The original15.3.21 consumer applies these facts to its two definite planes;
all quotient maps and conjugation actions remain the actual block actions.
Source: Aschbacher–Smith15.3.21,p.1127; C.1.22,p.129.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC ChapterC.ExceptionalRestrictions
variable {G : Type*} [Group G] [Finite G]

private theorem klein_four_cubic_centralizer {E : Type*} [Group E] [IsKleinFour E]
    (a b : MulAut E) (ha : a ^ 3 = 1) (hne : a ≠ 1) (hb : b ^ 4 = 1)
    (hab : Commute a b) : b = 1 := by
  let e := IsKleinFour.autEquivPermThree E
  have hsmall : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 ∧ a ≠ 1 ∧ b ^ 4 = 1 ∧
      a * b = b * a → b = 1 := by decide +kernel
  apply e.injective
  rw [map_one]
  exact hsmall (e a) (e b) ⟨by rw [←map_pow,ha,map_one],
    fun he => hne (e.injective (by simpa only [map_one] using he)),
    by rw [←map_pow,hb,map_one], by rw [←map_mul,←map_mul,hab.eq]⟩

omit [Finite G] in
private theorem scalar_cubic_fixed_free (h : IsExceptionalAhat6Block G)
    (z : G ⧸ pCore 2 G) (hz : z ∈ center _) (hne : z ≠ 1) (hz3 : z ^ 3 = 1)
    (u : blockU G) (hu : uAut h.1 z u = u) : u = 1 := by
  let := h.1.elementary
  have hfix : uRepresentation h.1 z (Additive.ofMul u) = Additive.ofMul u := hu
  have hh := LinearMap.congr_fun (central_cubic_quadratic h z hz hne hz3) (Additive.ofMul u)
  change uRepresentation h.1 z (uRepresentation h.1 z (Additive.ofMul u)) +
    uRepresentation h.1 z (Additive.ofMul u) + Additive.ofMul u = 0 at hh
  have htwo : Additive.ofMul u + Additive.ofMul u = 0 := by
    apply Additive.toMul.injective
    change u * u = 1
    rw [←pow_two]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (blockU G)) u
  rw [hfix,hfix,htwo,zero_add] at hh
  exact hh

/-- A two-element modulo the core fixes each four-group invariant under a
nontrivial central cubic. The quotient action and both normalizers are literal. -/
theorem exceptionalSix_cubic_plane_fixed (h : IsExceptionalAhat6Block G)
    (V : Subgroup G) (hVU : V ≤ blockU G) (hc : Nat.card V = 4)
    (y t : G) (hy : y ∈ normalizer (V : Set G)) (ht : t ∈ normalizer (V : Set G))
    (hz : QuotientGroup.mk' (pCore 2 G) y ∈ center _)
    (hne : QuotientGroup.mk' (pCore 2 G) y ≠ 1)
    (hy3 : (QuotientGroup.mk' (pCore 2 G) y) ^ 3 = 1)
    (ht4 : (QuotientGroup.mk' (pCore 2 G) t) ^ 4 = 1) :
    t ∈ centralizer (V : Set G) := by
  let := h.1.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective (inclusion hVU)
    (inclusion_injective hVU)
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour V := ⟨hc,IsElementaryAbelian.exponent_eq_prime⟩
  let q := QuotientGroup.mk' (pCore 2 G)
  let j : V →* blockU G := inclusion hVU
  let a := V.normalizerMonoidHom ⟨y,hy⟩
  let b := V.normalizerMonoidHom ⟨t,ht⟩
  have hi (s : G) (hs : s ∈ normalizer (V : Set G)) (v : V) :
      j (V.normalizerMonoidHom ⟨s,hs⟩ v) = uAut h.1 (q s) (j v) := by
    apply Subtype.ext
    rfl
  have hip (s : G) (hs : s ∈ normalizer (V : Set G)) (n : ℕ) (v : V) :
      j ((V.normalizerMonoidHom ⟨s,hs⟩ ^ n) v) = uAut h.1 ((q s) ^ n) (j v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' (V.normalizerMonoidHom ⟨s,hs⟩) n, pow_succ' (q s) n,map_mul]
      change j (V.normalizerMonoidHom ⟨s,hs⟩ ((V.normalizerMonoidHom ⟨s,hs⟩ ^ n) v)) =
        uAut h.1 (q s) (uAut h.1 ((q s)^n) (j v))
      rw [hi,ih]
  have ha3 : a ^ 3 = 1 := by
    apply MulEquiv.ext
    intro v
    apply inclusion_injective hVU
    change j ((a^3) v) = j v
    rw [hip,hy3,map_one]
    rfl
  have hane : a ≠ 1 := by
    intro he
    have hv (v : V) : v = 1 := by
      apply inclusion_injective hVU
      change j v = 1
      apply scalar_cubic_fixed_free h (q y) hz hne hy3
      rw [←hi y hy v,show V.normalizerMonoidHom ⟨y,hy⟩ = 1 from he]
      rfl
    have : Subsingleton V := ⟨fun x y => (hv x).trans (hv y).symm⟩
    have hh : Nat.card V = 1 := Nat.card_unique
    omega
  have hb4 : b ^ 4 = 1 := by
    apply MulEquiv.ext
    intro v
    apply inclusion_injective hVU
    change j ((b^4) v) = j v
    rw [hip,ht4,map_one]
    rfl
  have hab : Commute a b := by
    change a * b = b * a
    apply MulEquiv.ext
    intro v
    apply inclusion_injective hVU
    change j (a (b v)) = j (b (a v))
    rw [hi,hi,hi,hi]
    change (uAut h.1 (q y) * uAut h.1 (q t)) (j v) =
      (uAut h.1 (q t) * uAut h.1 (q y)) (j v)
    rw [←(uAut h.1).map_mul,←(uAut h.1).map_mul,
      (mem_center_iff.mp hz (q t)).symm]
  have hb := klein_four_cubic_centralizer a b ha3 hane hb4 hab
  have hk : (⟨t,ht⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker := hb
  rw [normalizerMonoidHom_ker] at hk
  exact hk

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource


open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC ChapterC.ExceptionalRestrictions
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A lift of an element of order four in the actual quotient fixes at most
four elements of the original U. -/
theorem exceptionalSix_four_fixed_card (h : IsExceptionalAhat6Block G)
    (t : G) (ht : orderOf (QuotientGroup.mk' (pCore 2 G) t) = 4)
    (V : Subgroup G) (hVU : V ≤ blockU G) (hfix : t ∈ centralizer (V : Set G)) :
    Nat.card V ≤ 4 := by
  let := h.1.elementary
  obtain ⟨F,hfield,hfinite,hF,hAlg,m,htower,f,e,hf,he⟩ := h.natural_restriction
  let := hfield
  let := hfinite
  let := hAlg
  let := m
  let := htower
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let q := QuotientGroup.mk' (pCore 2 G)
  let ρ := (specialLinearNatural 3 (k := F)).comp f
  have hρ : Function.Injective ρ := (specialLinearNatural_injective 3).comp hf
  have ht4 : (q t)^4 = 1 := ht ▸ pow_orderOf_eq_one (q t)
  have ht2 : (q t)^2 ≠ 1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [ht] at hd
    norm_num at hd
  let W := (ρ (q t) - 1).ker
  have hW : Module.finrank F W ≤ 1 := TripleSixFixedSpace.fixed_rank_le_one
    (by simp) (ρ (q t)) (by rw [←map_pow,ht4,map_one])
    (fun hh => ht2 (hρ (by simpa only [map_pow,map_one] using hh)))
  have hcW : Nat.card W ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := F),hF]
    exact (Nat.pow_le_pow_right (by decide : 0 < 4) hW).trans_eq (by norm_num)
  let j : V → W := fun v => ⟨e (Additive.ofMul (inclusion hVU v)),by
    change ρ (q t) (e (Additive.ofMul (inclusion hVU v))) -
      e (Additive.ofMul (inclusion hVU v)) = 0
    apply sub_eq_zero.mpr
    change specialLinearNatural 3 (f (q t)) _ = _
    rw [←he]
    apply congrArg e
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change t * (v : G) * t⁻¹ = (v : G)
    rw [←hfix v v.property,mul_inv_cancel_right]⟩
  have hj : Function.Injective j := by
    intro x y hh
    apply inclusion_injective hVU
    apply Additive.ofMul.injective
    apply e.injective
    exact congrArg Subtype.val hh
  exact (Nat.card_le_card_of_injective j hj).trans hcW

/-- Every actual component Sylow has an element of order four modulo its
core, using only the genuine triple cover of A₆. -/
theorem exceptionalSix_sylow_four (h : IsExceptionalAhat6Block G) (P : Sylow 2 G) :
    ∃ t : G, t ∈ (P : Subgroup G) ∧
      orderOf (QuotientGroup.mk' (pCore 2 G) t) = 4 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  obtain ⟨e⟩ := h.2.2.2.1
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (G ⧸ pCore 2 G)))
  obtain ⟨x,hx⟩ := TripleSixFixedSpace.cover_has_four f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers,hx]
    decide
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  let Pbar := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let v : Pbar := Q.equiv Pbar ⟨x,hQ (mem_zpowers x)⟩
  have hv : orderOf (v : G ⧸ pCore 2 G) = 4 := by
    rw [orderOf_coe]
    exact ((Q.equiv Pbar).orderOf_eq _).trans (by simpa only [←Subgroup.orderOf_coe] using hx)
  obtain ⟨t,ht,heq⟩ := v.property
  exact ⟨t,ht,heq ▸ hv⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
