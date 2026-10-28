module

public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.FixedPointFree
public import Stellmacher.LaterDefs

/-!
# Elementary odd subgroups in a solvable primitive group

The unique maximal subgroup above a nontrivial Sylow two-subgroup is
core-free when the two-core vanishes and every odd subgroup is elementary
abelian of exponent three. The solvable primitive theorem identifies its
normal core with the Frattini subgroup of an odd residual; that Frattini
subgroup is trivial.

In the resulting elementary normal complement, either the assumed odd-order
bound gives order three directly, or the Sylow subgroup has order two. In
the latter case, irreducibility and faithfulness make its involution
fixed-point-free, hence inverting. Every cyclic subgroup of the complement
is then invariant, so the complement has order three. Its automorphism
group has order two, forcing the Sylow order to be two in both cases.
The faithful action on three cosets identifies the whole group with
`SL₂(2)`.

Source: Stellmacher, Journal of Algebra 190 (1997), (3.3)–(3.6), printed
pp.21–22, and the application on printed p.42 ending (6),
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionThree

open scoped IsMulCommutative

universe u

private theorem complement_action_injective
    {Ambient : Type u} [Group Ambient] (kernel complement : Subgroup Ambient) [kernel.Normal]
    (hgen : kernel ⊔ complement = ⊤) (hcore : complement.normalCore = ⊥) :
    Function.Injective ((MulAut.conjNormal : Ambient →* MulAut kernel).comp complement.subtype) := by
  let centralizing := complement ⊓ Subgroup.centralizer (kernel : Set Ambient)
  have hn : centralizing.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    apply sup_le
    · apply Subgroup.le_normalizer_iff.mpr
      intro kernelElement hk centralizingElement hc
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 kernelElement hk
      rw [hcomm, mul_inv_cancel_right]
      exact hc
    · apply Subgroup.le_normalizer_iff.mpr
      intro complementElement hs centralizingElement hc
      exact ⟨complement.mul_mem (complement.mul_mem hs hc.1) (complement.inv_mem hs),
        (inferInstance : (Subgroup.centralizer (kernel : Set Ambient)).Normal).conj_mem
          centralizingElement hc.2 complementElement⟩
  have hC : centralizing = ⊥ := by
    have hle : centralizing ≤ complement.normalCore :=
      @Subgroup.normal_le_normalCore Ambient _ complement centralizing hn |>.mpr inf_le_left
    exact bot_unique (hle.trans_eq hcore)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro complementElement hs
  have hsC : (complementElement : Ambient) ∈ centralizing := by
    refine ⟨complementElement.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro kernelElement hk
    have heq := congrArg Subtype.val (DFunLike.congr_fun hs (⟨kernelElement, hk⟩ : kernel))
    change (complementElement : Ambient) * kernelElement *
      (complementElement : Ambient)⁻¹ = kernelElement at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hh : (complementElement : Ambient) ∈ (⊥ : Subgroup Ambient) := hC ▸ hsC
  exact Subtype.ext hh

private theorem elementary_three_orderOf
    {kernel : Type*} [Group kernel] [IsElementaryAbelian 3 kernel]
    (element : kernel) (hne : element ≠ 1) : orderOf element = 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime _ hne
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 3 kernel) element

private theorem irreducible_involution_complement_card_three
    {Ambient : Type u} [Group Ambient] [Finite Ambient]
    (kernel complement : Subgroup Ambient) [kernel.Normal] [IsElementaryAbelian 3 kernel]
    (hK : kernel ≠ ⊥) (hcard : Nat.card complement = 2)
    (hgen : kernel ⊔ complement = ⊤) (hcore : complement.normalCore = ⊥)
    (hirr : ∀ line : Subgroup Ambient, line ≤ kernel →
      (∀ actorElement : complement, ∀ element : Ambient, element ∈ line →
        (actorElement : Ambient) * element * (actorElement : Ambient)⁻¹ ∈ line) →
      line = ⊥ ∨ line = kernel) : Nat.card kernel = 3 := by
  classical
  let conjugation : complement →* MulAut kernel :=
    (MulAut.conjNormal : Ambient →* MulAut kernel).comp complement.subtype
  have hfaith : Function.Injective conjugation :=
    complement_action_injective kernel complement hgen hcore
  obtain ⟨complementElement, hs, hcases⟩ := (Nat.card_eq_two_iff' (1 : complement)).mp hcard
  have hfixed : MonoidHom.FixedPointFree (conjugation complementElement) := by
    let line := kernel ⊓ Subgroup.centralizer ({(complementElement : Ambient)} : Set Ambient)
    have hAs : ∀ actorElement : complement, ∀ element : Ambient, element ∈ line →
        (actorElement : Ambient) * element * (actorElement : Ambient)⁻¹ ∈ line := by
      intro actorElement element ha
      by_cases ht : actorElement = 1
      · simpa [ht] using ha
      · have ht := hcases actorElement ht
        subst actorElement
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp ha.2
        simpa [← hcomm] using ha
    have hAbot : line = ⊥ := by
      rcases hirr line inf_le_left hAs with hb | heq
      · exact hb
      · apply (hs ?_).elim
        apply hfaith
        rw [map_one]
        apply MulEquiv.ext
        intro kernelElement
        apply Subtype.ext
        have hk : (kernelElement : Ambient) ∈ line := by rw [heq]; exact kernelElement.property
        have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hk.2
        change (complementElement : Ambient) * (kernelElement : Ambient) *
          (complementElement : Ambient)⁻¹ = kernelElement
        rw [← hcomm, mul_inv_cancel_right]
    intro kernelElement hk
    apply Subtype.ext
    have heq := congrArg Subtype.val hk
    change (complementElement : Ambient) * (kernelElement : Ambient) *
      (complementElement : Ambient)⁻¹ = kernelElement at heq
    have hkA : (kernelElement : Ambient) ∈ line := by
      refine ⟨kernelElement.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    have hh : (kernelElement : Ambient) ∈ (⊥ : Subgroup Ambient) := hAbot ▸ hkA
    exact hh
  have hinvert : ∀ kernelElement : kernel,
      conjugation complementElement kernelElement = kernelElement⁻¹ := by
    have hss : complementElement * complementElement = 1 := by
      have hh : complementElement ^ Nat.card complement = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard complementElement)
      simpa only [hcard, pow_two] using hh
    have hinvol : Function.Involutive (conjugation complementElement) := by
      intro kernelElement
      change (conjugation complementElement * conjugation complementElement)
        kernelElement = kernelElement
      rw [← map_mul, hss, map_one]
      rfl
    exact congrFun (hfixed.coe_eq_inv_of_involutive hinvol)
  let _ : Nontrivial kernel := (Subgroup.nontrivial_iff_ne_bot kernel).mpr hK
  obtain ⟨kernelElement, hk⟩ := exists_ne (1 : kernel)
  let line := Subgroup.zpowers (kernelElement : Ambient)
  have hAK : line ≤ kernel := Subgroup.zpowers_le.mpr kernelElement.property
  have hAs : ∀ actorElement : complement, ∀ element : Ambient, element ∈ line →
      (actorElement : Ambient) * element * (actorElement : Ambient)⁻¹ ∈ line := by
    intro actorElement element ha
    by_cases ht : actorElement = 1
    · simpa [ht] using ha
    · have ht := hcases actorElement ht
      subst actorElement
      have heq := congrArg Subtype.val (hinvert (⟨element, hAK ha⟩ : kernel))
      change (complementElement : Ambient) * element * (complementElement : Ambient)⁻¹ = element⁻¹ at heq
      rw [heq]
      exact line.inv_mem ha
  have hAeq : line = kernel := by
    rcases hirr line hAK hAs with hb | heq
    · have hh : (kernelElement : Ambient) ∈ (⊥ : Subgroup Ambient) :=
        hb ▸ Subgroup.mem_zpowers (kernelElement : Ambient)
      exact (hk (Subtype.ext hh)).elim
    · exact heq
  rw [← hAeq, Nat.card_zpowers]
  exact (orderOf_injective kernel.subtype Subtype.val_injective kernelElement).trans
    (elementary_three_orderOf kernelElement hk)

/-- The elementary-odd primitive configuration under the stated smallness
alternative is the nonabelian group `SL₂(2)`. -/
public theorem elementary_odd_primitive_sl2Two
    {X : Type u} [Group X] [Finite X]
    (hsolvable : Group.IsSolvable X) (hcore : pCore 2 X = ⊥)
    (sylow : Sylow 2 X) (hnontriv : (sylow : Subgroup X) ≠ ⊥)
    (maximal : Subgroup X) (hmaximal : IsCoatom maximal)
    (hcontains : (sylow : Subgroup X) ≤ maximal)
    (hunique : ∀ other : Subgroup X, IsCoatom other →
      (sylow : Subgroup X) ≤ other → other = maximal)
    (hodd : ∀ actor : Subgroup X, Odd (Nat.card actor) →
      IsElementaryAbelian 3 actor)
    (hsmall : Nat.card sylow = 2 ∨
      ∀ actor : Subgroup X, Odd (Nat.card actor) → Nat.card actor ≤ 3) :
    Nonempty (X ≃* Stellmacher.Later.SL2Two) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨prime, hprime, hprimeOdd, hresidual, hfrattini, _⟩ :=
    solvable_primitive_two_local (sylow : Subgroup X) maximal sylow rfl
      hmaximal hcontains hunique hcore hsolvable
  have hmaxCore : maximal.normalCore = ⊥ := by
    let residual := twoResidualAmbient (⊤ : Subgroup X)
    let _ : Fact prime.Prime := ⟨hprime⟩
    have hresidualOdd : Odd (Nat.card residual) := by
      obtain ⟨power, hpower⟩ := hresidual.exists_card_eq
      rw [hpower]
      exact hprimeOdd.pow
    let _ : IsElementaryAbelian 3 residual := hodd residual hresidualOdd
    let _ : Fact (IsPGroup 3 residual) := ⟨IsElementaryAbelian.isPGroup 3 residual⟩
    rw [hfrattini]
    change (frattini residual).map residual.subtype = ⊥
    rw [frattini_eq_bot_of_isElementaryAbelian (p := 3), Subgroup.map_bot]
  obtain ⟨prime, kernel, hprime, hprimeOdd, hnormal, helementary,
      hintersection, hgen, hirreducible⟩ :=
    coreFree_uniqueSylowMaximal (sylow : Subgroup X) maximal sylow rfl
      hmaximal hcontains hunique hmaxCore hsolvable
  let _ : kernel.Normal := hnormal
  have hkernelOdd : Odd (Nat.card kernel) := by
    let _ : Fact prime.Prime := ⟨hprime⟩
    let _ : IsElementaryAbelian prime kernel := helementary
    obtain ⟨power, hpower⟩ := (IsElementaryAbelian.isPGroup prime kernel).exists_card_eq
    rw [hpower]
    exact hprimeOdd.pow
  let _ : IsElementaryAbelian 3 kernel := hodd kernel hkernelOdd
  have hkernelNe : kernel ≠ ⊥ := by
    intro hbot
    have hsylowTop : (sylow : Subgroup X) = ⊤ := by simpa [hbot] using hgen
    exact hmaximal.ne_top (top_unique (hsylowTop ▸ hcontains))
  have hsylowCore : (sylow : Subgroup X).normalCore = ⊥ := by
    apply bot_unique
    have hle : (sylow : Subgroup X).normalCore ≤ maximal.normalCore :=
      Subgroup.normal_le_normalCore.mpr
        ((sylow : Subgroup X).normalCore_le.trans hcontains)
    exact hle.trans_eq hmaxCore
  have hkernelCard : Nat.card kernel = 3 := by
    rcases hsmall with hsylowCard | hbound
    · exact irreducible_involution_complement_card_three kernel sylow hkernelNe
        hsylowCard hgen hsylowCore hirreducible
    · have hle := hbound kernel hkernelOdd
      let _ : Nontrivial kernel := (Subgroup.nontrivial_iff_ne_bot kernel).mpr hkernelNe
      obtain ⟨element, hne⟩ := exists_ne (1 : kernel)
      have hdiv := orderOf_dvd_natCard element
      rw [elementary_three_orderOf element hne] at hdiv
      exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdiv)
  have hfaith := complement_action_injective kernel sylow hgen hsylowCore
  have hsylowCard : Nat.card sylow = 2 := by
    let _ : IsCyclic kernel := isCyclic_of_prime_card hkernelCard
    have haut : Nat.card (MulAut kernel) = 2 := by
      rw [IsCyclic.card_mulAut, hkernelCard]
      decide
    have hle := Nat.card_le_card_of_injective _ hfaith
    rw [haut] at hle
    have hgt := (sylow : Subgroup X).one_lt_card_iff_ne_bot.mpr hnontriv
    omega
  have hdisjoint : Disjoint kernel (sylow : Subgroup X) := by
    apply disjoint_iff.mpr
    exact bot_unique ((inf_le_inf_left kernel hcontains).trans_eq hintersection)
  have hcomplement : kernel.IsComplement' (sylow : Subgroup X) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjoint
    rw [← Subgroup.normal_mul, hgen]
    rfl
  have hcard : Nat.card X = 6 := by
    have heq := hcomplement.card_mul_card
    rw [hkernelCard, hsylowCard] at heq
    omega
  let cosets := X ⧸ (sylow : Subgroup X)
  let action : X →* Equiv.Perm cosets := MulAction.toPermHom X cosets
  have haction : Function.Injective action := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    exact (Subgroup.normalCore_eq_ker (sylow : Subgroup X)).symm.trans hsylowCore
  have hcosets : Nat.card cosets = 3 := by
    exact (Subgroup.index_eq_card (sylow : Subgroup X)).symm.trans
      (hcomplement.index_eq_card.trans hkernelCard)
  let _ : Fintype cosets := Fintype.ofFinite cosets
  let numbering : cosets ≃ Fin 3 := Fintype.equivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hcosets)
  let permutationAction : X →* Equiv.Perm (Fin 3) :=
    numbering.permCongrHom.toMonoidHom.comp action
  have hbijective : Function.Bijective permutationAction := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨numbering.permCongrHom.injective.comp haction, ?_⟩
    rw [hcard, Nat.card_perm, Nat.card_fin]
    decide
  obtain ⟨model⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨(MulEquiv.ofBijective permutationAction hbijective).trans model.symm⟩

end Stellmacher.SectionThree
