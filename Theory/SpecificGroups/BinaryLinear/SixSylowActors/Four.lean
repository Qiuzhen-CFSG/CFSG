module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Defs
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Four.FixedEmbedding
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Permutation
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# A two-central actor in binary degree four

The elementary group of eight actors has cyclic outer image of order two.
Triviality of the binary linear center therefore lifts its four inner actors
to a subgroup of the fixed group of the selected outer involution. Extend the
natural four-space by a line to embed that actual fixed group in S₆. Transport
the supplied A₆ and its pointwise fixed Sylow subgroup through the same map.

The permutation Sylow-centralizer calculation finds a transposition in the
image of those four inner actors. Its inverse image is a transvection on the
original four-space, and transvection conjugacy supplies an actual ambient
Sylow two-subgroup centralized by its inner automorphism. This automorphism
belongs to the original E and is nonidentity.

This proves the intrinsic degree-four calculation used in Aschbacher–Smith,
E.6.23, printed p.254 (PDF p.265) of `refs/quasithin.pdf`, from the full
`Configuration` contract, without additional model or action premises.
-/

open Subgroup
open scoped IsMulCommutative
namespace BinaryLinear.SixSylowActors
open OuterCyclic

private instance : Finite (LinearGroup 4) :=
  Finite.of_injective (fun g : LinearGroup 4 => (g : Space 4 → Space 4))
    DFunLike.coe_injective

private theorem four_center_eq_bot : center (LinearGroup 4) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h := ((centerCongr (slEquivLinear 4)).symm ⟨x, hx⟩).property
  change (slEquivLinear 4).symm x ∈ center _ at h
  rw [binary_center_eq_bot (by decide : 0 < 4), mem_bot] at h
  exact mem_bot.mpr ((slEquivLinear 4).symm.map_eq_one_iff.mp h)

private theorem transvection_fixes_sylow {t : LinearGroup 4} (ht : IsTransvection t) :
    ∃ P : Sylow 2 (LinearGroup 4), ∀ x ∈ P, MulAut.conj t x = x := by
  have hV : 2 ∣ Nat.card (Space 4) := by
    simp [Space]
  obtain ⟨w, f, hw, hf, hfw, rfl⟩ := ht
  let W := Submodule.span (ZMod 2) {w}
  have htW : transvection w f hfw ∈ radical W :=
    transvection_mem (Submodule.mem_span_singleton_self w)
      (Submodule.span_le.mpr (by simpa using hfw))
  obtain ⟨P, hP⟩ := (radical_two W).exists_le_sylow
  let : Nontrivial P := (Subgroup.nontrivial_iff_exists_ne_one (P : Subgroup _)).mpr
    ⟨transvection w f hfw, hP htW, transvection_ne_one hw hf hfw⟩
  let : Nontrivial (Subgroup.center P) := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  have hz1 : (z.val.val : LinearGroup 4) ≠ 1 := by
    intro he
    exact hz (Subtype.ext (Subtype.ext he))
  have hzc : ∀ x : LinearGroup 4, x ∈ P → x * z.val.val = z.val.val * x := by
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property (⟨x, hx⟩ : P))
  have hzt := isTransvection_of_central_sylow hV (by simp [Space]) P hz1 hzc
  obtain ⟨g, hg⟩ := transvections_conjugate hzt ⟨w, f, hw, hf, hfw, rfl⟩
  let b := MulAut.conj g
  refine ⟨P.mapSurjective (f := b.toMonoidHom) b.surjective, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  apply mul_inv_eq_iff_eq_mul.mpr
  change transvection w f hfw * b y = b y * transvection w f hfw
  rw [← hg]
  exact (map_mul b _ _).symm.trans ((congrArg b (hzc y hy).symm).trans (map_mul b _ _))

private theorem inner_four_in_fixed
    (E : Subgroup (MulAut (LinearGroup 4))) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (τ : MulAut (LinearGroup 4)) (hτE : τ ∈ E)
    (hτ : τ ∉ MulAut.innerSubgroup (LinearGroup 4)) :
    ∃ B : Subgroup τ.fixedSubgroup, Nat.card B = 4 ∧
      ∀ b ∈ B, MulAut.conj (b : LinearGroup 4) ∈ E := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (LinearGroup 4))
  let f := q.comp E.subtype
  let : IsCyclic (MulAut.Outer (LinearGroup 4)) := linear_outer_isCyclic (Or.inl rfl)
  have hpow : ∀ x : f.range, x ^ 2 = 1 := by
    rintro ⟨x, a, rfl⟩
    apply Subtype.ext
    change f a ^ 2 = 1
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) a, map_one]
  have hdiv : Nat.card f.range ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  have hne : Nat.card f.range ≠ 1 := by
    intro he
    have hb : f.range = ⊥ := Subgroup.card_eq_one.mp he
    have hx : f ⟨τ, hτE⟩ = 1 := mem_bot.mp (hb ▸ (show f ⟨τ, hτE⟩ ∈ f.range from ⟨⟨τ, hτE⟩, rfl⟩))
    exact hτ ((QuotientGroup.eq_one_iff _).mp hx)
  have hr : Nat.card f.range = 2 := (Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hne
  have hk : Nat.card f.ker = 4 := by
    have hm := f.ker.card_mul_index
    rw [Subgroup.index_ker, hr, hE] at hm
    omega
  let e : LinearGroup 4 ≃* MulAut.innerSubgroup (LinearGroup 4) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot four_center_eq_bot)
  let k : f.ker →* MulAut.innerSubgroup (LinearGroup 4) :=
    { toFun := fun x => ⟨x.1.1, (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g := e.symm.toMonoidHom.comp k
  have hg (x : f.ker) : MulAut.conj (g x) = x.1.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply (k x))
  have hfixed (x : f.ker) : g x ∈ τ.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply MulAut.conj_injective_of_center_eq_bot four_center_eq_bot
    have he : MulAut.conj (τ (g x)) = τ * MulAut.conj (g x) * τ⁻¹ := by
      ext y
      simp
    rw [he, hg]
    have hc : τ * x.1.1 = x.1.1 * τ :=
      congrArg Subtype.val (mul_comm (⟨τ, hτE⟩ : E) x.1)
    rw [hc, mul_inv_cancel_right]
  let j : f.ker →* τ.fixedSubgroup := g.codRestrict _ hfixed
  have hj : Function.Injective j := by
    intro x y hxy
    have h := congrArg (fun z : τ.fixedSubgroup => MulAut.conj (z : LinearGroup 4)) hxy
    change MulAut.conj (g x) = MulAut.conj (g y) at h
    rw [hg, hg] at h
    exact Subtype.ext (Subtype.ext h)
  refine ⟨j.range, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, hk]
  · rintro b ⟨x, rfl⟩
    change MulAut.conj (g x) ∈ E
    rw [hg]
    exact x.1.property

/-- The supplied elementary actor group in GL₄(2) contains a nonidentity
actor fixing an actual ambient Sylow two-subgroup pointwise. -/
public theorem four_hasTwoCentralActor : HasTwoCentralActor (LinearGroup 4) := by
  intro E D h
  let : IsElementaryAbelian 2 E := h.elementary
  obtain ⟨τ, hτ, hτnot⟩ : ∃ τ ∈ E ⊓ fixingSubgroup (MulAut (LinearGroup 4)) (D : Set (LinearGroup 4)),
      τ ∉ MulAut.innerSubgroup (LinearGroup 4) := by
    by_contra hh
    apply h.fixer_outer
    intro a ha
    by_contra hn
    exact hh ⟨a, ha, hn⟩
  obtain ⟨k, hk, hkt⟩ := Four.exists_fixedEmbedding τ (elemPow_eq_one_of_isElementaryAbelian τ hτ.1) hτnot
  obtain ⟨B, hBcard, hBE⟩ := inner_four_in_fixed E h.card τ hτ.1 hτnot
  obtain ⟨eD⟩ := h.six
  obtain ⟨Q, hQ⟩ := h.sylow
  have hDF (x : D) : (x : LinearGroup 4) ∈ τ.fixedSubgroup :=
    (MulAut.mem_fixedSubgroup τ x).mpr
      ((mem_fixingSubgroup_iff _).mp hτ.2 x x.property)
  let j : D →* τ.fixedSubgroup := D.subtype.codRestrict _ hDF
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : τ.fixedSubgroup => (z : LinearGroup 4)) he)
  let ι := k.comp (j.comp eD.symm.toMonoidHom)
  have hι : Function.Injective ι := hk.comp (hj.comp eD.symm.injective)
  let Q₆ := Q.mapSurjective (f := eD.toMonoidHom) eD.surjective
  let B₆ := B.map k
  have hB₆ : Nat.card B₆ = 4 := by
    rw [Subgroup.card_map_of_injective hk, hBcard]
  have hfix : ∀ b ∈ B₆, ∀ x ∈ (Q₆ : Subgroup (alternatingGroup (Fin 6))),
      Commute b (ι x) := by
    rintro b ⟨b₀, hb₀, rfl⟩ x ⟨y, hy, rfl⟩
    change k b₀ * k (j (eD.symm (eD y))) =
      k (j (eD.symm (eD y))) * k b₀
    rw [eD.symm_apply_apply, ← map_mul, ← map_mul]
    apply congrArg k
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp (hQ (MulAut.conj (b₀ : LinearGroup 4)) (hBE b₀ hb₀) y hy)
  obtain ⟨b, hb, hswap⟩ := Five.permutationSylowSwap ι hι Q₆ B₆ hB₆ hfix
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have ht : IsTransvection (b₀ : LinearGroup 4) := by
    exact hkt b₀ hswap
  refine ⟨MulAut.conj (b₀ : LinearGroup 4), hBE b₀ hb₀, ?_, transvection_fixes_sylow ht⟩
  intro he
  apply ht.ne_one
  apply MulAut.conj_injective_of_center_eq_bot four_center_eq_bot
  simpa only [map_one] using he

end BinaryLinear.SixSylowActors
