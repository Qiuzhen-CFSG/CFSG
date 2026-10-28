module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.MainConverse.AlternatingSections.SmallDegrees
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankCubeFree
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.Fin

/-!
# An irreducible E₉:C₄ inside A₆

On six points let a = (0 1 2), b = (3 4 5), and
 t = (0 3 1 4)(2 5). The subgroup P = ⟨a,b⟩ has order nine and
 t induces (x,y) ↦ (-y,x) on its actual two ternary coordinates.
Every nonzero vector together with its image spans the plane, so the
conjugation action is irreducible, including on the Frattini quotient.
The finite coordinate identities are checked by the kernel.

With X = P, T = ⟨t⟩ and H = L = A₆, all fields of the published
`XiEmbedding.LocalInput 3 T X P H` hold. The component is normal,
quasisimple modulo its two-core, and satisfies [L,P] = L. A₆ has
three-rank two and is an SQTK group for the constructed catalogue.
Here O₂(X) = 1 and T is not Sylow in H.

This is the input obstruction to the proposed intrinsic formulation of
Aschbacher–Smith, Proposition 1.3.4, printed pp.509–511 of
`refs/quasithin.pdf` (1 March 2004 manuscript). It is not a counterexample
to the proposition with its full standing hypotheses. The companion
`InvariantThree.Obstruction` proves that none of the proposed output
models has the order of A₆, and packages the complete counterexample.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Equiv
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Obstruction

abbrev A6 := alternatingGroup (Fin 6)
abbrev V := Multiplicative (ZMod 3 × ZMod 3)
def a : A6 := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by change Perm.sign _ = 1; decide⟩
def b : A6 := ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by change Perm.sign _ = 1; decide⟩
def t : A6 := ⟨Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 2 5,
  by change Perm.sign _ = 1; decide⟩
def embed : V →* A6 where
  toFun v := a ^ v.toAdd.1.val * b ^ v.toAdd.2.val
  map_one' := by decide
  map_mul' := by decide +kernel

theorem embed_injective : Function.Injective embed := by decide +kernel

def P : Subgroup A6 := embed.range
def T : Subgroup A6 := zpowers t

def rotation (v : V) : V := Multiplicative.ofAdd (-v.toAdd.2, v.toAdd.1)
theorem conjugate_embed (v : V) : t * embed v * t⁻¹ = embed (rotation v) := by
  revert v
  decide +kernel

theorem rotation_surjective : Function.Surjective rotation := by decide +kernel

theorem generating_rotation : ∀ v : V, v ≠ 1 → ∀ w : V,
    ∃ i j : Fin 3, w = v ^ i.val * rotation v ^ j.val := by decide +kernel

theorem t_four : t ^ 4 = 1 := by decide +kernel

theorem t_order : orderOf t = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime
  · decide
  · exact t_four
  · intro q hq hdiv
    have hq2 : q = 2 := Nat.prime_eq_prime_of_dvd_pow hq (by decide : Nat.Prime 2)
      (show q ∣ 2 ^ 2 from hdiv)
    subst q
    decide +kernel

noncomputable def coordinates : V ≃* P := MonoidHom.ofInjective embed_injective

theorem p_card : Nat.card P = 9 := by
  rw [← Nat.card_congr coordinates.toEquiv]
  change Nat.card (ZMod 3 × ZMod 3) = 9
  simp

instance p_elementary : IsElementaryAbelian 3 P := by
  let : IsElementaryAbelian 3 V := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel) }
  exact IsElementaryAbelian.of_surjective coordinates.toMonoidHom coordinates.surjective

instance p_three_group : Fact (IsPGroup 3 P) := ⟨IsPGroup.of_card (n := 2) p_card⟩

theorem t_normalizes : t ∈ normalizer P := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨rotation v, (conjugate_embed v).symm⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := rotation_surjective v
    refine ⟨w, ?_⟩
    have hh : t * embed w * t⁻¹ = t * x * t⁻¹ := (conjugate_embed w).trans hv
    exact mul_left_cancel (mul_right_cancel hh)

theorem normalizes : T ≤ normalizer P := zpowers_le.mpr t_normalizes

theorem t_two : IsPGroup 2 T := by
  apply IsPGroup.of_card (n := 2)
  rw [T, Nat.card_zpowers, t_order]
  decide

-- Every nonzero vector and its rotation span the plane.
theorem action_irreducible (A : Subgroup P)
    (hA : ∀ s : (T ⊓ normalizer P : Subgroup A6), ∀ v ∈ A,
      P.normalizerMonoidHom ⟨s, s.property.2⟩ v ∈ A) : A = ⊥ ∨ A = ⊤ := by
  by_cases hb : A = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hb)
  have hv1 : v ≠ 1 := fun h => hv1 (h ▸ (⊥ : Subgroup P).one_mem)
  obtain ⟨v, rfl⟩ := coordinates.surjective v
  have hvn : v ≠ 1 := by intro h; apply hv1; rw [h, map_one]
  have hrot : coordinates (rotation v) ∈ A := by
    have hh := hA ⟨t, mem_zpowers t, t_normalizes⟩ (coordinates v) hv
    convert hh using 1
    apply Subtype.ext
    exact (conjugate_embed v).symm
  apply top_unique
  intro w _
  obtain ⟨w, rfl⟩ := coordinates.surjective w
  obtain ⟨i, j, rfl⟩ := generating_rotation v hvn w
  rw [map_mul, map_pow, map_pow]
  exact A.mul_mem (A.pow_mem hv _) (A.pow_mem hrot _)


theorem frattini_irreducible (A : Subgroup (P ⧸ frattini P))
    (hA : ∀ s : (T ⊓ normalizer P : Subgroup A6), ∀ v ∈ A,
      frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s v ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  let q := QuotientGroup.mk' (frattini P)
  have hstable : ∀ s : (T ⊓ normalizer P : Subgroup A6), ∀ v ∈ A.comap q,
      P.normalizerMonoidHom ⟨s, s.property.2⟩ v ∈ A.comap q := by
    intro s v hv
    have hh := hA s (q v) hv
    change q (P.normalizerMonoidHom ⟨s, s.property.2⟩ v) ∈ A
    have he : frattiniConjugationAction (T ⊓ normalizer P) P inf_le_right s (q v) =
        q (P.normalizerMonoidHom ⟨s, s.property.2⟩ v) := by
      dsimp only [frattiniConjugationAction, MonoidHom.comp_apply, q]
      rw [quotientAut_apply_mk]
      congr 1

    exact he ▸ hh
  have hqr : q.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

  rcases action_irreducible (A.comap q) hstable with hb | ht
  · left
    have hh := congrArg (Subgroup.map q) hb
    simpa only [map_comap_eq, hqr, top_inf_eq, Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map q) ht
    simpa only [map_comap_eq, hqr, top_inf_eq, ← MonoidHom.range_eq_map] using hh

theorem p_core : pCore 2 P = ⊥ := by
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 P) ⊤
    pCore_isPGroup ((IsElementaryAbelian.isPGroup 3 P).to_subgroup ⊤)
  simpa only [disjoint_top] using hd

theorem p_coreIn : P.pCoreIn 2 = ⊥ := by
  simp only [pCoreIn, p_core, Subgroup.map_bot]

theorem p_perfect : IsPPerfect 2 P := by
  intro N hN hp
  let := hN
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hc : Nat.card (P ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 9 2).pow_right n)
    (by simpa only [p_card] using card_quotient_dvd_card N) hn.dvd
  exact Subgroup.index_eq_one.mp ((Subgroup.index_eq_card N).trans hc)

theorem a6_card : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

instance a6_simple : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)

theorem a6_core : pCore 2 A6 = ⊥ := by
  rcases (inferInstance : (pCore 2 A6).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 A6 := (h ▸ pCore_isPGroup (p := 2) (G := A6)).of_equiv topEquiv
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hd : 3 ∣ 2 ^ n := by rw [← hn, a6_card]; decide
    exact False.elim ((by decide : ¬ 3 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide)) hd))


theorem top_coreIn : (⊤ : Subgroup A6).pCoreIn 2 = ⊥ :=
  (pCore_map_iso 2 (topEquiv : (⊤ : Subgroup A6) ≃* A6)).trans a6_core

noncomputable def p_quotient_equiv : XiQuotient P ≃* P :=
  (QuotientGroup.quotientMulEquivOfEq p_core).trans QuotientGroup.quotientBot

theorem p_odd_quotient : XiOddQuotient 3 (XiQuotient P) :=
  (show XiOddQuotient 3 P from Or.inl ⟨inferInstance, p_card⟩).of_mulEquiv
    p_quotient_equiv.symm

theorem local_input : LocalInput 3 T P P ⊤ := by
  refine {
    prime := by decide
    odd := by decide
    overgroup := le_top
    two_group := t_two
    invariant := normalizes
    perfect := p_perfect
    quotient := p_odd_quotient
    sylow := isSylowIn_iff.mpr ⟨Fact.out, le_rfl, fun U _ hPU hUP => le_antisymm hUP hPU⟩
    complement := by rw [p_coreIn, bot_sup_eq]
    disjoint := by rw [p_coreIn]; exact disjoint_bot_left
    generation := ?_
    core_commutator := by rw [p_coreIn, Subgroup.commutator_bot_left]
    normalizer_factor := by rw [p_coreIn, bot_sup_eq, inf_eq_left.mpr normalizes]
    irreducible := frattini_irreducible
    frattini_commutator := ?_
    residual := ?_ }
  · have hset : {g : A6 | ∃ n ∈ P.pCoreIn 2, ∃ a ∈ P, n * a * n⁻¹ = g} = (P : Set A6) := by
      ext g
      constructor
      · rintro ⟨n, hn, a, ha, he⟩
        have hn1 : n = 1 := Subgroup.mem_bot.mp (p_coreIn ▸ hn)
        subst n
        simpa only [one_mul, inv_one, mul_one] using he ▸ ha
      · intro hg
        exact ⟨1, P.pCoreIn 2 |>.one_mem, g, hg, by simp⟩
    rw [hset, Subgroup.closure_eq]
  · exact XiAction.eq_commutator_frattini_of_irreducible (p := 3) P (T ⊓ normalizer P)
      inf_le_right (t_two.to_le inf_le_left) Fact.out
      ((show XiOddQuotient 3 P from Or.inl ⟨inferInstance, p_card⟩).not_isCyclic)
      frattini_irreducible
  · rw [top_coreIn, bot_sup_eq, (pResidual_eq_top_iff 2 P).mpr p_perfect]
    rw [← MonoidHom.range_eq_map, range_subtype]

theorem pt_eq_tp : (P : Set A6) * T = (T : Set A6) * P :=
  (set_mul_normalizer_comm (T : Set A6) P normalizes).symm

theorem a6_stronglyQuasithin : IsStronglyQuasithin A6 := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [a6_card]
  intro hd
  have hpd : p ∣ 360 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
  have hfac : 360 = 2 ^ 3 * (3 ^ 2 * 5) := by decide
  rw [hfac, hp.dvd_mul, hp.dvd_mul] at hpd
  rcases hpd with h2 | h3 | h5
  · have he : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp (by decide) h2
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2)
  · have he : p = 3 := Nat.prime_eq_prime_of_dvd_pow hp (by decide) h3
    subst p
    norm_num at hd
  · have he : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h5
    subst p
    norm_num at hd

theorem a6_center : center A6 = ⊥ := alternatingGroup.center_eq_bot (by simp)

instance a6_perfect : Group.IsPerfect A6 := by
  constructor
  rcases (inferInstance : (_root_.commutator A6).Normal).eq_bot_or_eq_top with hb | ht
  · have hc := (commutator_eq_bot_iff A6).mp hb
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
    norm_num at hh
  · exact ht

instance a6_quasisimple : IsQuasisimple A6 where
  simple := by
    let e : A6 ⧸ center A6 ≃* A6 :=
      (QuotientGroup.quotientMulEquivOfEq a6_center).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance


theorem a6_sqtk : IsSQTK CFSG.KnownSimple.IsConstructedCarrier A6 :=
  ⟨a6_stronglyQuasithin, MainConverse.alternatingSix_isKGroup_constructed (MulEquiv.refl _)⟩

theorem top_core : pCore 2 (⊤ : Subgroup A6) = ⊥ := by
  apply map_injective (f := (topEquiv : (⊤ : Subgroup A6) ≃* A6).toMonoidHom) topEquiv.injective
  rw [pCore_map_iso, a6_core, Subgroup.map_bot]

noncomputable def component_quotient_equiv : XiQuotient (⊤ : Subgroup A6) ≃* A6 :=
  ((QuotientGroup.quotientMulEquivOfEq top_core).trans QuotientGroup.quotientBot).trans topEquiv

theorem component_quotient_quasisimple : IsQuasisimple (XiQuotient (⊤ : Subgroup A6)) :=
  IsQuasisimple.of_mulEquiv component_quotient_equiv.symm

theorem top_cComponent : (⊤ : Subgroup A6) ∈ cComponentsIn ⊤ := by
  refine ⟨le_rfl, ?_⟩
  rw [top_subgroupOf]
  have hq : IsQuasisimple (⊤ : Subgroup (⊤ : Subgroup A6)) :=
    IsQuasisimple.of_mulEquiv ((topEquiv : (⊤ : Subgroup A6) ≃* A6).symm.trans topEquiv.symm)
  exact component_isCComponent ⟨Subgroup.Normal.isSubnormal inferInstance, hq⟩

theorem component_commutator : ⁅(⊤ : Subgroup A6), P⁆ = ⊤ := by
  have hn : (⁅(⊤ : Subgroup A6), P⁆).Normal := normalizer_eq_top_iff.mp
    (top_unique (normalizer_commutator_ge_left ⊤ P))
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have ha : a ∈ P := ⟨Multiplicative.ofAdd (1, 0), by decide⟩
    have hmem := commutator_mem_commutator (mem_top t) ha
    have hone : ⁅t, a⁆ = 1 := Subgroup.mem_bot.mp (hb ▸ hmem)
    exact False.elim ((by decide +kernel : ⁅t, a⁆ ≠ 1) hone)
  · exact ht

theorem p_not_normal : ¬ P.Normal := by
  intro hn
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have hc := congrArg (fun U : Subgroup A6 => Nat.card U) hb
    rw [p_card, Subgroup.card_bot] at hc
    omega
  · have hc := congrArg (fun U : Subgroup A6 => Nat.card U) ht
    rw [p_card, Nat.card_congr (topEquiv : (⊤ : Subgroup A6) ≃* A6).toEquiv, a6_card] at hc
    omega


/-- The excluded example already has the exact rank used by the source sieve. -/
theorem a6_three_rank : primeRank 3 A6 = 2 := by
  exact le_antisymm (a6_stronglyQuasithin 3 (by decide) (by decide))
    (IsElementaryAbelian.primeRank_ge_of_card P (p := 3) (n := 2) p_card)

/-- The actor has order four, whereas a Sylow two-subgroup of A₆ has order eight. -/
theorem t_not_sylow : ¬ IsSylowIn 2 T (⊤ : Subgroup A6) := by
  intro h
  obtain ⟨S, hS⟩ := t_two.exists_le_sylow
  have he : (S : Subgroup A6) = T := (isSylowIn_iff.mp h).2.2 _ S.isPGroup' hS le_top
  have hc := S.card_eq_multiplicity
  have hT : Nat.card T = 4 := (Nat.card_zpowers t).trans t_order
  rw [he, hT, a6_card] at hc
  have hf : Nat.factorization 360 2 = 3 := by
    rw [show 360 = 2 ^ 3 * 45 from rfl,
      Nat.factorization_mul_apply_of_coprime (by decide),
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
  rw [hf] at hc
  norm_num at hc

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Obstruction
