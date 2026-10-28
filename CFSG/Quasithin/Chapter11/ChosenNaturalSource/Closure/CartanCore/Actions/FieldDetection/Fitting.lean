module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.NilpotentSylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Even
public import Theory.GroupTheory.Fitting.TwoCoreMonotonicity
public import Theory.GroupTheory.Fitting.Equiv

/-!
# Cartan component actions modulo the actual Fitting preimage

The complete component sieve leaves only the nilpotent-by-SL₂(5) row
when the Cartan fails to centralize a component modulo O₂(Y). A coprime
actor fixes this row's SL₂(5) Fitting quotient. Transporting that identity
through the literal isomorphism from I/O₂(I) to its image in G₁/O₂(G₁)
puts [I,X] in the inverse image of F(I/O₂(I)).

For the surviving row, relative normality in G₁ gives normality in Y.
Fitting functoriality then puts the same commutator in the inverse image
of F(Y/O₂(Y)). All other rows already satisfy the stronger two-core bound.
The final marked consumer combines both field parities and derives the
three-rank bound from the preceding geometry. Extraspecial primary factors
and arbitrary homocyclic exponents remain included.

This completes the Fitting-quotient reduction, not source 11.5.6(3): the
remaining odd-radical scalar action must still be excluded to replace these
Fitting preimages by O₂. That exclusion and the original CartanCore assembly
remain with qt-d-1222-natural-closure-cartan. The parent
qt-d-1222-natural-closure retains discharge of the preceding marked geometry.
Source: Aschbacher--Smith A.3.6(4), pp.43--45, and 11.5.6(3), pp.780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Transport the fixed Fitting-quotient action back to the actual component. -/
theorem nilpotent_component_fitting_commutator (hp : E.point ≠ ⊥)
    (hX : E.X ≤ E.G₁) (hodd : Odd (Nat.card E.X))
    (hcop : Nat.Coprime (Nat.card E.X) (Nat.card E.Y))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))
    (hc : A36Common
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)))) :
    ⁅I,E.X⁆ ≤ (twoFittingCore I).map I.subtype := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let e := E.componentImageQuotientEquiv hI
  let q := QuotientGroup.mk' (pCore 2 I)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx i hi
  let x' : normalizer (I : Set G) :=
    ⟨x,E.cartan_normalizes_component hp hX hodd hI hx⟩
  let i' : I := ⟨i,hi⟩
  let a : MulAut B := MulAut.congr e (coreQuotientAction I x')
  have hd : orderOf a ∣ Nat.card E.X := by
    apply ((orderOf_map_dvd (MulAut.congr e).toMonoidHom _).trans
      (orderOf_map_dvd (coreQuotientAction I) x')).trans
    rw [← Subgroup.orderOf_coe x']
    exact E.X.orderOf_dvd_natCard hx
  have hB : Nat.card B ∣ Nat.card E.Y := by
    rw [← Nat.card_congr e.toEquiv]
    exact (pCore 2 I).card_quotient_dvd_card.trans (card_dvd_of_le hI.1)
  have he := DFunLike.congr_fun
    (nilpotent_quotient_actor_eq_one hn hc a (hcop.of_dvd hd hB))
      (QuotientGroup.mk' (fittingSubgroup B) (e (q i')))
  rw [quotientAut_apply_mk] at he
  change QuotientGroup.mk' (fittingSubgroup B) (a (e (q i'))) =
    QuotientGroup.mk' (fittingSubgroup B) (e (q i')) at he
  have hfit : a (e (q i')) * (e (q i'))⁻¹ ∈ fittingSubgroup B := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (fittingSubgroup B)
      (a (e (q i')) * (e (q i'))⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  let j := I.normalizerMonoidHom x' i' * i'⁻¹
  have hj : e (q j) ∈ fittingSubgroup B := by
    convert hfit using 1
    dsimp only [j]
    rw [map_mul,map_inv,map_mul,map_inv]
    congr 1
    change e (q (I.normalizerMonoidHom x' i')) =
      e (coreQuotientAction I x' (e.symm (e (q i'))))
    rw [e.symm_apply_apply,coreQuotientAction_apply_mk]
  have hj' : q j ∈ fittingSubgroup (I ⧸ pCore 2 I) := by
    have hm := mem_map_of_mem e.symm.toMonoidHom hj
    rw [map_fitting_equiv] at hm
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hm
  exact ⟨j,hj',rfl⟩

/-- After the full component sieve, every Cartan commutator lies in the
literal intrinsic Fitting preimage. This holds in either field parity. -/
theorem cartan_component_fitting_action_of_small_rank (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    ⁅I,E.X⁆ ≤ (twoFittingCore I).map I.subtype ∧
      ⁅I,E.X⁆ ≤ (twoFittingCore E.Y).map E.Y.subtype := by
  classical
  by_cases hgood : ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2
  · have hcomm : ⁅I,E.X⁆ ≤ I := le_normalizer_iff_commutator_le_left.mp
      (E.cartan_normalizes_component hp hX hcart.odd hI)
    exact ⟨((le_inf hcomm hgood).trans (inf_pCoreIn_le_of_le 2 hI.1)).trans
      (map_mono twoCore_le_twoFittingCore),
      hgood.trans (map_mono twoCore_le_twoFittingCore)⟩
  · have hodd : Odd E.input.field.degree := by
      apply Nat.not_even_iff_odd.mp
      intro he
      exact hgood ((E.cartan_actions_of_even_marked hp hT hX c hcart hXR hCX hz hNG he).1 I hI)
    obtain ⟨hn,hc,_⟩ := E.moved_component_nilpotent_fitting_case hp hT hX c
      hcart hXR hCX hz hNG hr hodd hI hgood
    have hcop := E.cartan_coprime_of_local_action hp hX hcart.odd
      (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
    have hi := E.nilpotent_component_fitting_commutator hp hX hcart.odd
      (E.cartan_coprime_Y_of_split_marking (c.cartanTorusEquiv hcart) hcop) hI hn hc
    refine ⟨hi,hi.trans ?_⟩
    let J := I.subgroupOf E.Y
    let eJ : J ≃* I := subgroupOfEquivOfLe hI.1
    have hnormal : E.G₁ ≤ normalizer (I : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (hI.1.trans E.Y_le_G₁)).mp
        (E.nilpotent_component_relative_normal hp hI hn)
    let : J.Normal := (normal_subgroupOf_iff_le_normalizer hI.1).mpr
      (E.Y_le_G₁.trans hnormal)
    rintro _ ⟨i,hi,rfl⟩
    have hj : eJ.symm i ∈ twoFittingCore J :=
      twoFittingCore_map_equiv_le eJ.symm (mem_map_of_mem eJ.symm.toMonoidHom hi)
    exact mem_map_of_mem E.Y.subtype
      (twoFittingCore_map_subtype_le_of_normal J (mem_map_of_mem J.subtype hj))

/-- The original marked consumer derives the rank bound from the preceding
local component geometry. No primary-actor or component-action premise is added. -/
theorem cartan_component_fitting_action_of_marked (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    ⁅I,E.X⁆ ≤ (twoFittingCore I).map I.subtype ∧
      ⁅I,E.X⁆ ≤ (twoFittingCore E.Y).map E.Y.subtype := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  exact E.cartan_component_fitting_action_of_small_rank hp hT hX c hcart hXR hCX hz hNG
    (E.three_rank_Y_le_one hp hc hexception hz hthree) hI

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
