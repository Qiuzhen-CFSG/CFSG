module
public import Theory.SpecificGroups.PSL2.CubicActorCentralizer
public import Theory.SpecificGroups.Alternating.FourPairCore
/-!
# Faithful alternating-four actors on prime-field PSL₂

A faithful two-perfect A₄ actor has inner image. Its two-core is a Klein four
and its center is trivial, so the prime-field cubic-actor centralizer theorem
makes its full automorphism centralizer trivial. Consequently, an element
commuting with such an actor also centralizes a normal component on which
that actor acts faithfully.

The actual consumer is the secondary involution centralizer in the proof of
Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

/-- The full automorphism centralizer of a faithful two-perfect A4 actor is trivial. -/
theorem faithful_alternating_four_actor_centralizer_trivial
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {L K : Type*} [_root_.Group L] [Finite L] [_root_.Group K] [Finite K]
    (eK : K ≃* PSL(2,ZMod p)) (hL : IsPPerfect 2 L)
    (eA : L ≃* alternatingGroup (Fin 4))
    (f : L →* MulAut K) (hf : Function.Injective f)
    (β : MulAut K) (hc : ∀ l : L, β*f l=f l*β) : β=1 := by
  let X := PSL(2,ZMod p)
  let g : L →* MulAut X := (MulAut.congr eK).toMonoidHom.comp f
  have hg : Function.Injective g := (MulAut.congr eK).injective.comp hf
  let B := g.range
  have hB : IsPPerfect 2 B := hL.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hi : B ≤ (MulAut.conj : X →* MulAut X).range :=
    Theory.PSL2.prime_twoPerfect_le_inner hp5 B hB
  let eBA : B ≃* alternatingGroup (Fin 4) := (MonoidHom.ofInjective hg).symm.trans eA
  let eC : pCore 2 B ≃* pCore 2 (alternatingGroup (Fin 4)) :=
    (eBA.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 eBA))
  let eE : B.pCoreIn 2 ≃* alternatingGroup.kleinFour (Fin 4) :=
    ((pCore 2 B).equivMapOfInjective B.subtype B.subtype_injective).symm.trans
      (eC.trans (MulEquiv.subgroupCongr AlternatingFourPair.twoCore_eq_kleinFour))
  let hk := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
  let : IsKleinFour (B.pCoreIn 2) := {
    card_four := (Nat.card_congr eE.toEquiv).trans hk.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans hk.exponent_two }
  have hz : center B=⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    have hh : eBA b∈center (alternatingGroup (Fin 4)) := (centerCongr eBA ⟨b,hb⟩).property
    rw [alternatingGroup.center_eq_bot (by norm_num : 4≤Nat.card (Fin 4)),mem_bot] at hh
    exact eBA.map_eq_one_iff.mp hh
  let γ := MulAut.congr eK β
  have hγ : γ∈centralizer (B : Set (MulAut X)) := by
    rintro b ⟨l,rfl⟩
    exact (show γ*g l=g l*γ from by
      simpa only [γ,g,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul]
        using congrArg (MulAut.congr eK) (hc l)).symm
  rw [Theory.PSL2.prime_cubic_actor_centralizer_eq_bot hp5 B hi hz,mem_bot] at hγ
  exact (MulAut.congr eK).map_eq_one_iff.mp hγ

/-- An element commuting with the faithful residual A4 also centralizes a normal prime-field component. -/
theorem normal_alternating_four_actor_centralizer_le
    {C : Type*} [_root_.Group C] [Finite C]
    {p : ℕ} [Fact p.Prime] (hp5 : 5≤p)
    (L K : Subgroup C) [K.Normal]
    (eK : K≃*PSL(2,ZMod p)) (hL : IsPPerfect 2 L)
    (eA : L≃*alternatingGroup (Fin 4))
    (hn : L≤normalizer (K : Set C))
    (hf : Function.Injective (K.normalizerMonoidHom.comp (inclusion hn))) :
    centralizer (L : Set C)≤centralizer (K : Set C) := by
  intro v hv
  have hvn : v∈normalizer (K : Set C) := by rw [normalizer_eq_top]; trivial
  let vn : normalizer (K : Set C) := ⟨v,hvn⟩
  let f := K.normalizerMonoidHom.comp (inclusion hn)
  have hb : K.normalizerMonoidHom vn=1 := by
    apply faithful_alternating_four_actor_centralizer_trivial hp5 eK hL eA f hf
    intro l
    change K.normalizerMonoidHom vn*K.normalizerMonoidHom (inclusion hn l)=
      K.normalizerMonoidHom (inclusion hn l)*K.normalizerMonoidHom vn
    rw [←map_mul,←map_mul]
    apply congrArg K.normalizerMonoidHom
    apply Subtype.ext
    exact (hv l l.property).symm
  have hker : vn∈K.normalizerMonoidHom.ker := hb
  rw [normalizerMonoidHom_ker] at hker
  exact hker

end Theory.PSL2
