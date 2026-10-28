module
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
import all Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.SylowAutomorphismPGroup
/-!
# Normal two-actors in an A₅ Sylow stabilizer

The automorphism stabilizer of an A₅ Sylow four-group fixes its Borel's
point in the five-letter action. If an odd actor belongs to a normal
two-subgroup, commutators force every even actor to square to one.
Consequently a nontrivial two-perfect subgroup excludes such an odd actor,
so the normal two-subgroup acts by inner automorphisms.

The relative quotient theorem keeps the given quotient map and its actual
conjugation action. This is the group-theoretic radical step of
Aschbacher–Smith 13.7.4(1), printed p.937. It makes no false assertion that
the whole A₅ Sylow automorphism stabilizer is a two-group.
-/

public section
open Subgroup
open scoped commutatorElement Pointwise
namespace Theory.SpecificGroups.Alternating.FiveSylowRadical
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

theorem sylow_stabilizer_fixes_point (S : Sylow 2 A5) :
    ∃ i : Fin 5, ∀ a : MulAut A5,
      (S : Subgroup A5).map a.toMonoidHom = S →
      FiveExtensionAction.symmetricAutEquiv.symm a i = i := by
  obtain ⟨i,hi⟩ := FiveBorelOvergroups.sylow_normalizer_eq_stabilizer S
  refine ⟨i, ?_⟩
  intro a ha
  let t := FiveExtensionAction.symmetricAutEquiv.symm a
  have ht : (MulAut.conjNormal t : MulAut A5) = a := by
    exact FiveExtensionAction.symmetricAutEquiv.apply_symm_apply a
  have hB : (normalizer (S : Set A5)).map a.toMonoidHom = normalizer (S : Set A5) := by
    change (normalizer ((S : Subgroup A5) : Set A5)).map a.toMonoidHom = _
    rw [map_equiv_normalizer_eq, ha]
    rfl
  have hhom : (MulAut.conj t).toMonoidHom.comp (A5).subtype =
      (A5).subtype.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change t * x.val * t⁻¹ = (a x).val
    rw [← ht]
    rfl
  have hm : (normalizer (S : Set A5)).map (A5).subtype =
      A5 ⊓ MulAction.stabilizer S5 i := by
    rw [hi]
    ext x
    exact ⟨fun ⟨y, hy, he⟩ => he ▸ ⟨y.property, hy⟩,
      fun ⟨ha, hx⟩ => ⟨⟨x, ha⟩, hx, rfl⟩⟩
  have hn : t ∈ normalizer (((normalizer (S : Set A5)).map (A5).subtype) : Set S5) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ((normalizer (S : Set A5)).map (A5).subtype).map (MulAut.conj t).toMonoidHom = _
    rw [map_map,hhom,←map_map,hB]
  rw [hm,FiveBorelCentralFactor.even_stabilizer_normalizer] at hn
  exact hn

private theorem cubic_commutator_check_at_four :
    ∀ (b : {b : S5 // b 4 = 4 ∧ b.sign = 1})
    (t : {t : S5 // t 4 = 4 ∧ t.sign ≠ 1}),
    b.val ^ 2 ≠ 1 → ⁅b.val,t.val⁆ ^ 3 = 1 ∧ ⁅b.val,t.val⁆ ≠ 1 := by
  decide +kernel

private theorem cubic_commutator_check (i : Fin 5)
    (b : {b : S5 // b i = i ∧ b.sign = 1})
    (t : {t : S5 // t i = i ∧ t.sign ≠ 1}) :
    b.val ^ 2 ≠ 1 → ⁅b.val,t.val⁆ ^ 3 = 1 ∧ ⁅b.val,t.val⁆ ≠ 1 := by
  intro hnot
  let s : S5 := Equiv.swap i 4
  let e := MulAut.conj s
  have hbfix : e b.val 4 = 4 := by
    change s (b.val (s⁻¹ 4)) = 4
    simp only [s, Equiv.swap_inv,Equiv.swap_apply_right,b.property.1,
      Equiv.swap_apply_left]
  have htfix : e t.val 4 = 4 := by
    change s (t.val (s⁻¹ 4)) = 4
    simp only [s, Equiv.swap_inv,Equiv.swap_apply_right,t.property.1,
      Equiv.swap_apply_left]
  have hbsgn : (e b.val).sign = 1 := by
    simp [e,MulAut.conj_apply,b.property.2]
  have htsgn : (e t.val).sign ≠ 1 := by
    simpa [e,MulAut.conj_apply,mul_comm,mul_left_comm,mul_assoc] using t.property.2
  have hnot' : (e b.val)^2 ≠ 1 := by
    intro hh
    apply hnot
    apply e.injective
    simpa using hh
  obtain ⟨hpow,hne⟩ := cubic_commutator_check_at_four
    ⟨e b.val,hbfix,hbsgn⟩ ⟨e t.val,htfix,htsgn⟩ hnot'
  constructor
  · apply e.injective
    simpa only [map_pow,map_commutatorElement,map_one] using hpow
  · intro hh
    apply hne
    rw [←map_commutatorElement,hh,map_one]

variable {E : Type*} [Group E]

theorem point_radical_even (f : E →* S5) (i : Fin 5)
    (hfix : ∀ x, f x i = i) (D R : Subgroup E) [R.Normal]
    (hD : IsPPerfect 2 D) (hR : IsPGroup 2 R)
    (hne : ∃ d : D, f d ≠ 1) :
    ∀ r : R, (f r).sign = 1 := by
  let g : D →* S5 := f.comp D.subtype
  have htwo : IsPGroup 2 (S5 ⧸ A5) := by
    apply IsPGroup.of_card (n := 1)
    rw [← (A5).index_eq_card, alternatingGroup.index_eq_two]
    rfl
  have heven (d : D) : (g d).sign = 1 := by
    have hh := hD.hom_eq_one_of_isPGroup htwo ((QuotientGroup.mk' A5).comp g)
    exact Equiv.Perm.mem_alternatingGroup.mp ((QuotientGroup.eq_one_iff _).mp
      (DFunLike.congr_fun hh d))
  intro r
  by_contra hodd
  have hpow (d : D) : (g d) ^ 2 = 1 := by
    by_contra hnot
    obtain ⟨hc3,hcne⟩ := cubic_commutator_check i ⟨g d,hfix d,heven d⟩
      ⟨f r,hfix r,hodd⟩ hnot
    have hcR : ⁅(d : E),(r : E)⁆ ∈ R := by
      exact R.mul_mem ((inferInstance : R.Normal).conj_mem _ r.property d)
        (R.inv_mem r.property)
    let c : R := ⟨⁅(d : E),(r : E)⁆,hcR⟩
    have hcim : f c = ⁅g d,f r⁆ := map_commutatorElement f (d : E) (r : E)
    obtain ⟨n,hn⟩ := hR c
    have hhpow : (⁅g d,f r⁆) ^ (2 ^ n) = 1 := by
      rw [←hcim,←map_pow,←Subgroup.coe_pow,hn]
      exact map_one f
    have hcop : Nat.Coprime (2 ^ n) 3 := (by decide : Nat.Coprime 2 3).pow_left n
    have hc1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hhpow)
        (orderOf_dvd_of_pow_eq_one hc3))
    exact hcne hc1
  have hp : IsPGroup 2 g.range := by
    rintro ⟨x,d,rfl⟩
    exact ⟨1,Subtype.ext (by simpa using hpow d)⟩
  have hg := hD.hom_eq_one_of_isPGroup hp g.rangeRestrict
  obtain ⟨d,hd⟩ := hne
  exact hd (congrArg Subtype.val (DFunLike.congr_fun hg d))

/-- A normal two-subgroup acts inner on A₅ when it shares a Sylow-preserving
actor with a nontrivial two-perfect subgroup. -/
theorem normal_two_action_inner (S : Sylow 2 A5) (a : E →* MulAut A5)
    (hS : ∀ x, (S : Subgroup A5).map (a x).toMonoidHom = S)
    (D R : Subgroup E) [R.Normal] (hD : IsPPerfect 2 D) (hR : IsPGroup 2 R)
    (hne : ∃ d : D, a d ≠ 1) :
    ∀ r : R, a r ∈ MulAut.innerSubgroup A5 := by
  let f : E →* S5 := FiveExtensionAction.symmetricAutEquiv.symm.toMonoidHom.comp a
  obtain ⟨i,hi⟩ := sylow_stabilizer_fixes_point S
  have hfix (x : E) : f x i = i := hi _ (hS x)
  have hne' : ∃ d : D, f d ≠ 1 := by
    obtain ⟨d,hd⟩ := hne
    refine ⟨d,fun hh => hd ?_⟩
    apply FiveExtensionAction.symmetricAutEquiv.symm.injective
    exact hh.trans (map_one _).symm
  intro r
  have hr := point_radical_even f i hfix D R hD hR hne' r
  let k : A5 := ⟨f r,Equiv.Perm.mem_alternatingGroup.mpr hr⟩
  refine ⟨k,?_⟩
  change MulAut.conjNormal (f r) = a r
  exact FiveExtensionAction.symmetricAutEquiv.apply_symm_apply (a r)

/-- The two-core of a Sylow overgroup acts inner on the actual A₅ quotient
whenever a two-perfect subgroup acts nontrivially there. -/
theorem pCore_action_inner {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (K P B : Subgroup G)
    (hPK : P ≤ normalizer (K : Set G)) (hTP : (T : Subgroup G) ≤ P)
    (hKP : IsPGroup 2 (K ⊓ P : Subgroup G)) (hBP : B ≤ P) (hB : IsPPerfect 2 B)
    (q : K →* A5) (hq : Function.Surjective q) (a : P →* MulAut A5)
    (ha : ∀ (x : P) (k : K), a x (q k) =
      q (K.normalizerMonoidHom ⟨x, hPK x.property⟩ k))
    (hnon : ∃ b : B, a (inclusion hBP b) ≠ 1) :
    ∀ r : pCore 2 P, a r ∈ MulAut.innerSubgroup A5 := by
  obtain ⟨S,hS⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K (hTP.trans hPK)
  have hPtwo : IsPGroup 2 (P.subgroupOf K) := by
    rw [← inf_subgroupOf_left P K]
    exact hKP.comap_subtype
  have hPS : P.subgroupOf K = (S : Subgroup K) :=
    S.is_maximal' hPtwo (by rw [hS]; exact comap_mono hTP)
  let S' := S.mapSurjective hq
  have haS (x : P) : (S' : Subgroup A5).map (a x).toMonoidHom = S' := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (a x).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change a x (q k) ∈ (S' : Subgroup A5)
    rw [ha]
    apply mem_map_of_mem
    rw [← hPS] at hk ⊢
    change (x : G) * (k : G) * (x : G)⁻¹ ∈ P
    exact P.mul_mem (P.mul_mem x.property hk) (P.inv_mem x.property)
  let D := B.subgroupOf P
  let eD : D ≃* B := subgroupOfEquivOfLe hBP
  have hD : IsPPerfect 2 D := hB.of_surjective eD.symm.toMonoidHom eD.symm.surjective
  have hDnon : ∃ b : D, a b ≠ 1 := by
    obtain ⟨b,hb⟩ := hnon
    exact ⟨⟨⟨b,hBP b.property⟩,b.property⟩,hb⟩
  exact normal_two_action_inner S' a haS D (pCore 2 P) hD pCore_isPGroup hDnon

end Theory.SpecificGroups.Alternating.FiveSylowRadical
