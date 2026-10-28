module
public import CFSG.Quasithin.Chapter13.Section02.A5Local.FullAction
public import Theory.Representation.BinaryPermutation.FiveEvenDisplacement
public import Theory.SpecificGroups.SymmetricFive.SylowNormalIntersection
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Commutators of Sylow-normalized actors on the original natural module

A nontrivial subgroup of S₅ normalized by a full Sylow two-subgroup meets
A₅ nontrivially. Cauchy supplies an even involution in that intersection;
its displacement on the natural sixteen has order four. Transfer along
the original equivariant module embedding bounds the actual commutator.
When the module lies in the actor subgroup, this elementary commutator
lies in its derived subgroup and rules out cyclicity of that derived group.

The commuting-core application retains both original contexts and both
local markings in OriginalCentralization/CommutingCoreDerived.
Source: Aschbacher--Smith 13.2.8(1), p.880, using the natural module of
13.2.3--4, pp.878--879. This is a local obstruction, not the full n(H)>1 step.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)

/-- A noncentral Sylow-normalized actor moves at least a four-group. -/
theorem four_le_card_commutator_of_sylow_normal
    (J P : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (hPT : P ≤ (T : Subgroup G))
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (q : J →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V.subgroupOf J : Set J))
    (he : ∀ j : J, ∀ v : BinaryPermutation.core (Fin 5),
      j.val * d.flag.module.map (Multiplicative.ofAdd v) * j.val⁻¹ =
        d.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q j) v)))
    (hm : ¬ P ≤ centralizer (V : Set G)) :
    4 ≤ Nat.card (⁅P,V⁆ : Subgroup G) := by
  let S := T.subtype hTJ
  let B := (P.subgroupOf J).map q
  have hVJ : V ≤ J := d.chosen.le_sylow.trans hTJ
  have hB : B ≠ ⊥ := by
    intro hb
    apply hm
    intro p hp v hv
    have hpq : (⟨p,hTJ (hPT hp)⟩ : J) ∈ q.ker := (Subgroup.map_eq_bot_iff _).mp hb hp
    rw [hk] at hpq
    exact congrArg J.subtype (hpq ⟨v,hVJ hv⟩ hv)
  have hn : ((S.mapSurjective hq) : Subgroup (Equiv.Perm (Fin 5))) ≤
      normalizer (B : Set (Equiv.Perm (Fin 5))) := by
    apply (map_mono (f := q) ?_).trans ((P.subgroupOf J).le_normalizer_map q)
    intro t ht
    apply mem_normalizer_iff.mpr
    intro p
    exact mem_normalizer_iff.mp (hTP ht) p.val
  have hBP : B ≤ ((S.mapSurjective hq) : Subgroup (Equiv.Perm (Fin 5))) :=
    map_mono (fun _ hx => hPT hx)
  let E := B ⊓ alternatingGroup (Fin 5)
  have hE : E ≠ ⊥ :=
    Theory.SpecificGroups.SymmetricFive.SylowNormalIntersection.inf_alternating_ne_bot
      (S.mapSurjective hq) B hB hn
  have hEp : IsPGroup 2 E := (S.mapSurjective hq).isPGroup'.to_le (inf_le_left.trans hBP)
  have hEd : 2 ∣ Nat.card E := by
    obtain ⟨n,hn⟩ := hEp.exists_card_eq
    have hpos : 0 < n := by
      by_contra! hz
      have hc : Nat.card E ≤ 1 := by rw [hn,show n=0 by omega];simp
      exact hE (eq_bot_of_card_le E hc)
    rw [hn]
    exact dvd_pow_self 2 (Nat.ne_of_gt hpos)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 hEd
  have hap : (a : Equiv.Perm (Fin 5)) ^ 2 = 1 :=
    congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
  have han : (a : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro hz
    have hz' : a=1 := Subtype.ext hz
    simp [hz'] at ha
  obtain ⟨p,hp,hpa⟩ := a.property.1
  have hh := BinaryPermutation.FiveEvenDisplacement.four_le_card_commutator
    d.flag.module.map d.flag.module.injective p.val (q p)
    (hpa.symm ▸ han) (hpa.symm ▸ hap) (hpa.symm ▸ a.property.2)
    (fun v => (he p v.toAdd).symm)
  rw [d.flag.module.range_eq] at hh
  exact hh.trans (card_le_of_le (commutator_mono (zpowers_le.mpr hp) le_rfl))

/-- If the natural module is inside the actor, its derived subgroup is noncyclic. -/
theorem noncyclic_derived_of_sylow_normal
    (J P : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (hVP : V ≤ P) (hPT : P ≤ (T : Subgroup G))
    (hTP : (T : Subgroup G) ≤ normalizer (P : Set G))
    (q : J →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V.subgroupOf J : Set J))
    (he : ∀ j : J, ∀ v : BinaryPermutation.core (Fin 5),
      j.val * d.flag.module.map (Multiplicative.ofAdd v) * j.val⁻¹ =
        d.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q j) v)))
    (hm : ¬ P ≤ centralizer (V : Set G)) : ¬ IsCyclic (⁅P,P⁆ : Subgroup G) := by
  intro hc
  let := hc
  let C := ⁅P,V⁆
  have hCV : C ≤ V := le_normalizer_iff_commutator_le_right.mp
    (hPT.trans d.flag.T_normalizes)
  let := d.elementary
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCV
  let : IsCyclic C := isCyclic_of_injective
    (inclusion (commutator_mono le_rfl hVP)) (inclusion_injective _)
  have hsmall : Nat.card C ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [←IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 C
  have hlarge := d.four_le_card_commutator_of_sylow_normal J P hTJ hPT hTP q hq hk he hm
  change Nat.card (⁅P,V⁆ : Subgroup G) ≤ 2 at hsmall
  omega
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
