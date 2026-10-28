module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Defs
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Contracts
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Permutation
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The degree-five two-central actor calculation

The elementary group of eight actors has cyclic outer image, hence exactly
four inner actors. Triviality of the binary linear center lifts them faithfully
to a subgroup of order four in the fixed group of the selected outer involution.
The supplied A₆ and its Sylow subgroup are transported through that same fixed
model. A transposition in the centralizing four-group then gives a transvection
whose inner automorphism belongs to the original actor group.

Every binary transvection centralizes a Sylow two-subgroup: a nontrivial Sylow
center supplies one transvection, and conjugacy supplies the others. Thus this
last step produces the actual Sylow witness required by `HasTwoCentralActor`.

The conditional assembly `five_hasTwoCentralActor_of_calculations` keeps the
two calculations explicit. The theorem `five_hasTwoCentralActor` discharges
both premises using the compatible outer-involution fixed model and the
permutation centralizer calculation. Source: Aschbacher–Smith, E.6.23,
printed p.254 (PDF p.265).
-/

open Subgroup
open scoped IsMulCommutative
namespace BinaryLinear.SixSylowActors
open OuterCyclic

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
    DFunLike.coe_injective

private theorem five_center_eq_bot : center (LinearGroup 5) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h := ((centerCongr (slEquivLinear 5)).symm ⟨x, hx⟩).property
  change (slEquivLinear 5).symm x ∈ center _ at h
  rw [binary_center_eq_bot (by decide : 0 < 5), mem_bot] at h
  exact mem_bot.mpr ((slEquivLinear 5).symm.map_eq_one_iff.mp h)

private theorem transvection_fixes_sylow {t : LinearGroup 5} (ht : IsTransvection t) :
    ∃ P : Sylow 2 (LinearGroup 5), ∀ x ∈ P, MulAut.conj t x = x := by
  have hV : 2 ∣ Nat.card (Space 5) := by
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
  have hz1 : (z.val.val : LinearGroup 5) ≠ 1 := by
    intro he
    exact hz (Subtype.ext (Subtype.ext he))
  have hzc : ∀ x : LinearGroup 5, x ∈ P → x * z.val.val = z.val.val * x := by
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
    (E : Subgroup (MulAut (LinearGroup 5))) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (τ : MulAut (LinearGroup 5)) (hτE : τ ∈ E)
    (hτ : τ ∉ MulAut.innerSubgroup (LinearGroup 5)) :
    ∃ B : Subgroup τ.fixedSubgroup, Nat.card B = 4 ∧
      ∀ b ∈ B, MulAut.conj (b : LinearGroup 5) ∈ E := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (LinearGroup 5))
  let f := q.comp E.subtype
  let : IsCyclic (MulAut.Outer (LinearGroup 5)) := linear_outer_isCyclic (Or.inr rfl)
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
  let e : LinearGroup 5 ≃* MulAut.innerSubgroup (LinearGroup 5) :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot five_center_eq_bot)
  let k : f.ker →* MulAut.innerSubgroup (LinearGroup 5) :=
    { toFun := fun x => ⟨x.1.1, (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let g := e.symm.toMonoidHom.comp k
  have hg (x : f.ker) : MulAut.conj (g x) = x.1.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply (k x))
  have hfixed (x : f.ker) : g x ∈ τ.fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply MulAut.conj_injective_of_center_eq_bot five_center_eq_bot
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
    have h := congrArg (fun z : τ.fixedSubgroup => MulAut.conj (z : LinearGroup 5)) hxy
    change MulAut.conj (g x) = MulAut.conj (g y) at h
    rw [hg, hg] at h
    exact Subtype.ext (Subtype.ext h)
  refine ⟨j.range, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, hk]
  · rintro b ⟨x, rfl⟩
    change MulAut.conj (g x) ∈ E
    rw [hg]
    exact x.1.property

/-- Conditional assembly: both the compatible fixed-group model and the
permutation Sylow calculation remain explicit mathematical premises. -/
public theorem five_hasTwoCentralActor_of_calculations
    (hmodel : ∀ τ : MulAut (LinearGroup 5), τ ^ 2 = 1 →
      τ ∉ MulAut.innerSubgroup (LinearGroup 5) → Nonempty (Five.FixedModel τ))
    (hperm : Five.PermutationSylowSwap) : HasTwoCentralActor (LinearGroup 5) := by
  intro E D h
  let : IsElementaryAbelian 2 E := h.elementary
  obtain ⟨τ, hτ, hτnot⟩ : ∃ τ ∈ E ⊓ fixingSubgroup (MulAut (LinearGroup 5)) (D : Set (LinearGroup 5)),
      τ ∉ MulAut.innerSubgroup (LinearGroup 5) := by
    by_contra hh
    apply h.fixer_outer
    intro a ha
    by_contra hn
    exact hh ⟨a, ha, hn⟩
  obtain ⟨m⟩ := hmodel τ (elemPow_eq_one_of_isElementaryAbelian τ hτ.1) hτnot
  obtain ⟨B, hBcard, hBE⟩ := inner_four_in_fixed E h.card τ hτ.1 hτnot
  obtain ⟨eD⟩ := h.six
  obtain ⟨Q, hQ⟩ := h.sylow
  have hDF (x : D) : (x : LinearGroup 5) ∈ τ.fixedSubgroup :=
    (MulAut.mem_fixedSubgroup τ x).mpr
      ((mem_fixingSubgroup_iff _).mp hτ.2 x x.property)
  let j : D →* τ.fixedSubgroup := D.subtype.codRestrict _ hDF
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : τ.fixedSubgroup => (z : LinearGroup 5)) he)
  let ι := m.equiv.toMonoidHom.comp (j.comp eD.symm.toMonoidHom)
  have hι : Function.Injective ι := m.equiv.injective.comp (hj.comp eD.symm.injective)
  let Q₆ := Q.mapSurjective (f := eD.toMonoidHom) eD.surjective
  let B₆ := B.map m.equiv.toMonoidHom
  have hB₆ : Nat.card B₆ = 4 := by
    rw [Subgroup.card_map_of_injective m.equiv.injective, hBcard]
  have hfix : ∀ b ∈ B₆, ∀ x ∈ (Q₆ : Subgroup (alternatingGroup (Fin 6))),
      Commute b (ι x) := by
    rintro b ⟨b₀, hb₀, rfl⟩ x ⟨y, hy, rfl⟩
    change m.equiv b₀ * m.equiv (j (eD.symm (eD y))) =
      m.equiv (j (eD.symm (eD y))) * m.equiv b₀
    rw [eD.symm_apply_apply, ← map_mul, ← map_mul]
    apply congrArg m.equiv
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp (hQ (MulAut.conj (b₀ : LinearGroup 5)) (hBE b₀ hb₀) y hy)
  obtain ⟨b, hb, hswap⟩ := hperm ι hι Q₆ B₆ hB₆ hfix
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have ht : IsTransvection (b₀ : LinearGroup 5) := by
    simpa only [MulEquiv.symm_apply_apply] using m.swap_isTransvection (m.equiv b₀) hswap
  refine ⟨MulAut.conj (b₀ : LinearGroup 5), hBE b₀ hb₀, ?_, transvection_fixes_sylow ht⟩
  intro he
  apply ht.ne_one
  apply MulAut.conj_injective_of_center_eq_bot five_center_eq_bot
  simpa only [map_one] using he

/-- In the binary degree-five model, the supplied elementary actor group contains
a nonidentity automorphism fixing an actual ambient Sylow two-subgroup pointwise. -/
public theorem five_hasTwoCentralActor : HasTwoCentralActor (LinearGroup 5) :=
  five_hasTwoCentralActor_of_calculations Five.exists_fixedModel Five.permutationSylowSwap

end BinaryLinear.SixSylowActors
