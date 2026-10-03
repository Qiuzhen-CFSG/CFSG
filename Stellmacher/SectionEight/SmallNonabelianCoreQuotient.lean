module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionThree.ElementaryOddPrimitiveSLTwo
public import Stellmacher.UniqueMaximalContainingMap
public import Theory.GroupTheory.OddSubgroupLift
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphisms
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# Recognition from a small nonabelian two-core

A solvable characteristic-two-type member of the local P-family has quotient
`SL₂(2)` by its ordinary two-core when its Sylow two-subgroup has order at
most 64 and its nonabelian core has order at most 32. At core order 32, the
source supplies a single elementary abelian subgroup of order eight; this
excludes the exceptional order-five automorphism action.

The core embeds into the displayed Sylow subgroup with index at least two.
Conjugation embeds every odd local subgroup into the automorphism group of
the self-centralizing core. The small-core automorphism theorem makes these
actors elementary abelian at three, of order at most three unless the core
has order 32. Schur–Zassenhaus lifts odd actors from the literal core quotient,
and subgroup correspondence transfers the unique maximal subgroup above its
Sylow image. In the order-32 case that image has order two. These alternatives
are exactly the hypotheses of the proved elementary-odd primitive recognition.
The final homomorphism retains the literal ordinary two-core as its kernel.

This supplies the small-index recognition in Stellmacher (8.6),
Journal of Algebra 190 (1997), printed p.42, paragraph ending in (6).
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven
open scoped IsMulCommutative

universe u

public theorem small_nonabelian_two_group_card
    {Q : Type u} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hbound : Nat.card Q ≤ 32) :
    Nat.card Q = 8 ∨ Nat.card Q = 16 ∨ Nat.card Q = 32 := by
  obtain ⟨exponent, hcard⟩ := htwo.exists_card_eq
  have hupper : exponent ≤ 5 := by
    by_contra hnot
    have hpower : 2 ^ 6 ≤ 2 ^ exponent :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hcard] at hpower
    norm_num at hpower
    omega
  have hlower : 3 ≤ exponent := by
    by_contra hnot
    have hsmall : exponent ≤ 2 := by omega
    interval_cases exponent
    · let : IsCyclic Q := isCyclic_of_card_dvd_prime (p := 2) (by
        rw [hcard]
        norm_num)
      exact hnoncomm inferInstance
    · let : IsCyclic Q := isCyclic_of_card_dvd_prime (p := 2) (by
        rw [hcard]
        norm_num)
      exact hnoncomm inferInstance
    · exact hnoncomm (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard)
  interval_cases exponent <;> norm_num at hcard ⊢ <;> omega

public theorem small_nonabelian_core_card
    {G : Type u} [Group G] [Finite G] (localGroup : Subgroup G)
    (hnoncomm : ¬ IsMulCommutative (twoCoreIn localGroup))
    (hbound : Nat.card (twoCoreIn localGroup) ≤ 32) :
    Nat.card (twoCoreIn localGroup) = 8 ∨
      Nat.card (twoCoreIn localGroup) = 16 ∨
      Nat.card (twoCoreIn localGroup) = 32 :=
  small_nonabelian_two_group_card
    ((pCore_isPGroup (p := 2) (G := localGroup)).map localGroup.subtype)
    hnoncomm hbound

public theorem pFamily_core_sylow_index_bounds
    {G : Type u} [Group G] [Finite G] (sylow localGroup : Subgroup G)
    (hlocal : localGroup ∈ PFamily (⊤ : Subgroup G) sylow)
    (hsylow : Nat.card sylow ≤ 64) :
    twoCoreIn localGroup ≤ sylow ∧
      2 ≤ (twoCoreIn localGroup).relIndex sylow ∧
      (Nat.card (twoCoreIn localGroup) = 32 →
        (twoCoreIn localGroup).relIndex sylow = 2 ∧ Nat.card sylow = 64) := by
  obtain ⟨_, localSylow, hmap⟩ := hlocal.1.2.1
  have hle : twoCoreIn localGroup ≤ sylow := by
    rw [← hmap]
    exact Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := localGroup)).le_sylow_of_normal localSylow)
  have hcard := ((twoCoreIn localGroup).subgroupOf sylow).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  have hpos : 0 < (twoCoreIn localGroup).relIndex sylow := by
    have hpositive : 0 < Nat.card sylow := Nat.card_pos
    change 0 < ((twoCoreIn localGroup).subgroupOf sylow).index
    nlinarith
  have hnotone : (twoCoreIn localGroup).relIndex sylow ≠ 1 := by
    intro hone
    exact hlocal.1.2.2.2 (le_antisymm (Subgroup.relIndex_eq_one.mp hone) hle)
  have hlower : 2 ≤ (twoCoreIn localGroup).relIndex sylow := by omega
  refine ⟨hle, hlower, ?_⟩
  intro hcore
  change (twoCoreIn localGroup).relIndex sylow *
    Nat.card (twoCoreIn localGroup) = Nat.card sylow at hcard
  rw [hcore] at hcard
  constructor <;> omega

public theorem odd_subgroup_core_conjugation_injective
    {K : Type u} [Group K] [Finite K]
    (core : Subgroup K) [core.Normal] (htwo : IsPGroup 2 core)
    (hcentralizer : Subgroup.centralizer (core : Set K) ≤ core)
    (actor : Subgroup K) (hodd : Odd (Nat.card actor)) :
    Function.Injective ((MulAut.conjNormal (H := core)).comp actor.subtype) := by
  obtain ⟨exponent, hcard⟩ := htwo.exists_card_eq
  have hcoprime : Nat.Coprime (Nat.card actor) (Nat.card core) := by
    rw [hcard]
    exact hodd.coprime_two_right.pow_right exponent
  have hdisjoint : Disjoint actor core :=
    Subgroup.disjoint_of_coprime_natCard hcoprime
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro element helement
  apply Subtype.ext
  apply hdisjoint.le_bot
  refine ⟨element.property, hcentralizer ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro member hmember
  have hfix := congrArg (fun automorphism : MulAut core =>
    (automorphism ⟨member, hmember⟩ : K)) helement
  change (element : K) * member * (element : K)⁻¹ = member at hfix
  calc
    member * (element : K) =
        ((element : K) * member * (element : K)⁻¹) * (element : K) := by rw [hfix]
    _ = (element : K) * member := by simp [mul_assoc]

public theorem characteristic_two_odd_subgroup_core_image
    {G : Type u} [Group G] [Finite G] (localGroup : Subgroup G)
    (hcharacteristic : IsCharacteristicTwoType localGroup)
    (actor : Subgroup localGroup) (hodd : Odd (Nat.card actor)) :
    ∃ image : Subgroup (MulAut (pCore 2 localGroup)),
      Odd (Nat.card image) ∧ Nonempty (actor ≃* image) := by
  let action : actor →* MulAut (pCore 2 localGroup) :=
    (MulAut.conjNormal (H := pCore 2 localGroup)).comp actor.subtype
  have hinjective : Function.Injective action :=
    odd_subgroup_core_conjugation_injective (pCore 2 localGroup)
      pCore_isPGroup hcharacteristic actor hodd
  let equiv : actor ≃* action.range := MonoidHom.ofInjective hinjective
  refine ⟨action.range, ?_, ⟨equiv⟩⟩
  rwa [← Nat.card_congr equiv.toEquiv]

private theorem elementary_of_injective
    {P X : Type*} [Group P] [Group X] {p : ℕ}
    (f : P →* X) (hf : Function.Injective f) [IsElementaryAbelian p X] :
    IsElementaryAbelian p P := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact IsMulCommutative.of_comm fun a b => hf (by simp [mul_comm])
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply hf
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p X) _

public theorem small_nonabelian_core_quotient_sl2Two
    {G : Type u} [Group G] [Finite G] (sylow localGroup : Subgroup G)
    (hlocal : localGroup ∈ PFamily (⊤ : Subgroup G) sylow)
    (hsolvable : Group.IsSolvable localGroup)
    (hcharacteristic : IsCharacteristicTwoType localGroup)
    (hsylow : Nat.card sylow ≤ 64)
    (hnoncomm : ¬ IsMulCommutative (twoCoreIn localGroup))
    (hbound : Nat.card (twoCoreIn localGroup) ≤ 32)
    (heights : Nat.card (twoCoreIn localGroup) = 32 →
      ∃ elementary : Subgroup G, elementary ≤ twoCoreIn localGroup ∧
        IsElementaryAbelianSubgroup 2 elementary ∧ Nat.card elementary = 8) :
    QuotientIsModel localGroup (twoCoreIn localGroup) SL2Two := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := hsolvable
  let Q := pCore 2 localGroup
  let X := localGroup ⧸ Q
  let projection : localGroup →* X := QuotientGroup.mk' Q
  have hsurj : Function.Surjective projection := QuotientGroup.mk'_surjective Q
  have hker : projection.ker = Q := QuotientGroup.ker_mk' Q
  let eQ : Q ≃* twoCoreIn localGroup :=
    Q.equivMapOfInjective localGroup.subtype localGroup.subtype_injective
  have hQcard : Nat.card Q = Nat.card (twoCoreIn localGroup) := Nat.card_congr eQ.toEquiv
  have hQnoncomm : ¬ IsMulCommutative Q := by
    intro hcomm
    let _ := hcomm
    exact hnoncomm (Subgroup.map_isMulCommutative (H := Q) (f := localGroup.subtype))
  have hQheight : Nat.card Q = 32 → ∃ E : Subgroup Q,
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 := by
    intro hc
    obtain ⟨E, hE, helem, hcard⟩ := heights (hQcard.symm.trans hc)
    let _ : IsElementaryAbelian 2 E := helem
    let E0 := E.subgroupOf (twoCoreIn localGroup)
    let _ : IsElementaryAbelian 2 E0 := IsElementaryAbelian.subgroupOf hE
    refine ⟨E0.map eQ.symm.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
    rw [Subgroup.card_map_of_injective eQ.symm.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv).trans hcard
  have hactors : ∀ D : Subgroup X, Odd (Nat.card D) →
      IsElementaryAbelian 3 D ∧
        Nat.card D ∣ (if Nat.card Q = 32 then 9 else 3) := by
    intro D hD
    obtain ⟨E, hEimage, _, hEcard, _⟩ := projection.exists_odd_subgroup_lift hsurj
      (hker.symm ▸ pCore_isPGroup) D hD
    have hEodd : Odd (Nat.card E) := hEcard.symm ▸ hD
    obtain ⟨A, hAodd, ⟨eA⟩⟩ :=
      characteristic_two_odd_subgroup_core_image localGroup hcharacteristic E hEodd
    obtain ⟨hAelem, hAcard⟩ :=
      SmallNonabelianTwoGroup.small_nonabelian_two_group_odd_automorphisms
        pCore_isPGroup hQnoncomm (hQcard ▸ hbound) hQheight A hAodd
    let _ := hAelem
    let _ : IsElementaryAbelian 3 E := elementary_of_injective eA.toMonoidHom eA.injective
    refine ⟨hEimage ▸ IsElementaryAbelian.map projection, ?_⟩
    rwa [← Nat.card_congr eA.toEquiv, hEcard] at hAcard
  obtain ⟨hSP, T, hT⟩ := hlocal.1.2.1
  have hTnative : (T : Subgroup localGroup) = sylow.subgroupOf localGroup := by
    apply Subgroup.map_injective localGroup.subtype_injective
    rw [hT, Subgroup.map_subgroupOf_eq_of_le hSP]
  have hQT : Q ≤ (T : Subgroup localGroup) := pCore_isPGroup.le_sylow_of_normal T
  let Tbar := T.mapSurjective hsurj
  have hTbarCard : Nat.card Tbar = (twoCoreIn localGroup).relIndex sylow := by
    rw [Sylow.coe_mapSurjective, ← Subgroup.relIndex_ker, hker]
    rw [← Subgroup.relIndex_map_map_of_injective Q (T : Subgroup localGroup)
      localGroup.subtype_injective, hT]
    rfl
  have hindices := pFamily_core_sylow_index_bounds sylow localGroup hlocal hsylow
  have hTbarNontriv : (Tbar : Subgroup X) ≠ ⊥ := by
    intro hbot
    have hc : Nat.card Tbar = 1 := by
      rw [hbot, Subgroup.card_bot]
    have := hindices.2.1
    omega
  obtain ⟨_, M, hM, hSM, hMunique⟩ := hlocal.2
  have hTM : (T : Subgroup localGroup) ≤ M := hTnative ▸ hSM
  have hTunique : IsUniqueMaximalContaining (T : Subgroup localGroup) ⊤ := by
    apply (uniqueMaximalContaining_top_iff _).mpr
    refine ⟨M, hM, hTM, ?_⟩
    intro N hN hTN
    exact hMunique N hN (hTnative ▸ hTN)
  have hTbarProper : (T : Subgroup localGroup).map projection ≠ ⊤ := by
    intro htop
    have heq : (T : Subgroup localGroup) = ⊤ := by
      have hh : projection.ker ≤ (T : Subgroup localGroup) := by simpa only [hker] using hQT
      calc
        (T : Subgroup localGroup) =
            ((T : Subgroup localGroup).map projection).comap projection :=
          (Subgroup.comap_map_eq_self hh).symm
        _ = ⊤ := by rw [htop, Subgroup.comap_top]
    exact hM.ne_top (top_unique (heq ▸ hTM))
  obtain ⟨Mbar, hMbar, hTMbar, hMbarUnique⟩ :=
    (uniqueMaximalContaining_top_iff _).mp
      (uniqueMaximalContaining_map_of_ne_top projection hsurj _ hTunique hTbarProper)
  have hXcore : pCore 2 X = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup 2 Q pCore_isPGroup]
    exact QuotientGroup.map_mk'_self Q
  have hsmall : Nat.card Tbar = 2 ∨
      ∀ D : Subgroup X, Odd (Nat.card D) → Nat.card D ≤ 3 := by
    by_cases hc : Nat.card Q = 32
    · exact Or.inl (hTbarCard.trans (hindices.2.2 (hQcard.symm.trans hc)).1)
    · right
      intro D hD
      have hh := (hactors D hD).2
      simp only [if_neg hc] at hh
      exact Nat.le_of_dvd (by decide) hh
  obtain ⟨eX⟩ := SectionThree.elementary_odd_primitive_sl2Two
    inferInstance hXcore Tbar hTbarNontriv Mbar hMbar hTMbar hMbarUnique
    (fun D hD => (hactors D hD).1) hsmall
  refine ⟨eX.toMonoidHom.comp projection, eX.surjective.comp hsurj, ?_⟩
  rw [MonoidHom.ker_comp_of_injective projection eX.toMonoidHom eX.injective, hker]
  change Q = (Q.map localGroup.subtype).subgroupOf localGroup
  exact (Subgroup.comap_map_eq_self_of_injective localGroup.subtype_injective Q).symm


end Stellmacher.SectionEight
