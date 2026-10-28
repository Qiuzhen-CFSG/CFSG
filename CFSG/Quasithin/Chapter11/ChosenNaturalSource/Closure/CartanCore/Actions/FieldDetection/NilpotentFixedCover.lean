module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.Fitting
public import Theory.GroupAction.SubgroupPerfectFixedCover

/-!
# A Cartan-fixed perfect cover in the remaining component row

The proved Fitting commutator bound and coprimality show that the actual
centralizer C_I(X) maps onto I/O₂,F(I). Perfectness of I gives the same
surjectivity for the solvable residual of C_I(X), and the residual times
the Fitting preimage is exactly I. This holds in both field parities.

In the surviving moved-component row, the literal equivalence
I/O₂(I) -> I-bar carries the Fitting subgroup onto F(I-bar). The resulting
quotient isomorphism identifies I/O₂,F(I) with SL₂(5). The final marked
consumer constructs the surjection from the actual fixed residual to
that matrix group, proves its kernel solvable, and retains divisibility
by 120. It adds no fixed-cover, model or component-action premise.

This strengthens the fixed Sylow image to a full fixed perfect cover;
it does not exclude the remaining scalar action on the odd radical.
That ambient exclusion and 11.5.6(3) assembly remain with
qt-d-1222-natural-closure-cartan. The parent qt-d-1222-natural-closure
retains discharge of the preceding marked geometry. Extraspecial factors
and arbitrary homocyclic exponents remain included.
Source: Aschbacher--Smith A.3.6, pp.43--45, and 11.5.6(3), pp.780--781.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Every actual component is a product of its Cartan-fixed perfect residual
and its literal two-core Fitting preimage. -/
theorem cartan_component_fixed_residual_cover_of_marked (hp : E.point ≠ ⊥)
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
    Function.Surjective (((QuotientGroup.mk' (twoFittingCore I)).comp
      (inclusion (show I ⊓ centralizer (E.X : Set G) ≤ I from inf_le_left))).comp
        (solvableResidual (I ⊓ centralizer (E.X : Set G) : Subgroup G)).subtype) ∧
    (residualIn (I ⊓ centralizer (E.X : Set G)) : Set G) *
      ((twoFittingCore I).map I.subtype : Set G) = (I : Set G) := by
  let e : I.subgroupOf E.Y ≃* I := subgroupOfEquivOfLe hI.1
  let : Group.IsPerfect (I.subgroupOf E.Y) := hI.2.perfect
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  have hcop := (E.cartan_coprime_component_of_split_marking
    (c.cartanTorusEquiv hcart) hc hI).of_dvd_right (twoFittingCore I).card_subgroup_dvd_card
  have hn := E.cartan_normalizes_component hp hX hcart.odd hI
  have hm := (E.cartan_component_fitting_action_of_marked hp hT hX c hcart hXR
    hCX hz hNG hthree hexception hI).1
  exact ⟨residual_centralizer_quotient_surjective_of_solvable_coprime
      I E.X (twoFittingCore I) hn twoFittingCore_solvable hcop hm,
    residual_centralizer_mul_kernel_eq
      I E.X (twoFittingCore I) hn twoFittingCore_solvable hcop hm⟩

/-- Transport the actual remaining Fitting quotient to its SL₂(5) model. -/
theorem nilpotent_component_twoFitting_quotient {I : Subgroup G}
    (hI : Source.ComponentIn E.Y I)
    (hn : A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)))) :
    LocalModels.IsSL (I ⧸ twoFittingCore I) 2 5 := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let e := E.componentImageQuotientEquiv hI
  let q := QuotientGroup.mk' (pCore 2 I)
  let f := (QuotientGroup.mk' (fittingSubgroup B)).comp (e.toMonoidHom.comp q)
  have hk : f.ker = twoFittingCore I := by
    ext i
    change QuotientGroup.mk' (fittingSubgroup B) (e (q i)) = 1 ↔
      q i ∈ fittingSubgroup (I ⧸ pCore 2 I)
    apply (QuotientGroup.eq_one_iff (N := fittingSubgroup B) (e (q i))).trans
    rw [← map_fitting_equiv e]
    exact mem_map_iff_mem e.injective
  let eQ : (I ⧸ twoFittingCore I) ≃* (B ⧸ fittingSubgroup B) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f
        ((QuotientGroup.mk'_surjective _).comp (e.surjective.comp
          (QuotientGroup.mk'_surjective _))))
  obtain ⟨F,_,_,hF,⟨em⟩⟩ := hn.2.2.1
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨eQ.trans ((QuotientGroup.quotientMulEquivOfEq hn.1).symm.trans em)⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- A remaining moved component has an actual Cartan-fixed perfect cover of
SL₂(5), with its original quotient map and a solvable kernel. -/
theorem moved_component_fixed_perfect_sl2_five (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hthree : 1 ≤ primeRank 3 E.L₁)
    (hexception : E.L₁ < E.K → Even E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let C := I ⊓ centralizer (E.X : Set G)
    let f := ((QuotientGroup.mk' (twoFittingCore I)).comp
      (inclusion (show C ≤ I from inf_le_left))).comp (solvableResidual C).subtype
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 5 ∧
      ∃ e : (I ⧸ twoFittingCore I) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        Function.Surjective (e.toMonoidHom.comp f) ∧
          Group.IsSolvable (e.toMonoidHom.comp f).ker ∧
          120 ∣ Nat.card (solvableResidual C) := by
  have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  have hr := E.three_rank_Y_le_one hp hc hexception hz hthree
  have ho : Odd E.input.field.degree := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hmoved ((E.cartan_actions_of_even_marked hp hT hX c hcart hXR hCX hz hNG he).1 I hI)
  obtain ⟨hn,_,_⟩ := E.moved_component_nilpotent_fitting_case hp hT hX c hcart
    hXR hCX hz hNG hr ho hI hmoved
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := E.nilpotent_component_twoFitting_quotient hI hn
  let C := I ⊓ centralizer (E.X : Set G)
  let f := ((QuotientGroup.mk' (twoFittingCore I)).comp
    (inclusion (show C ≤ I from inf_le_left))).comp (solvableResidual C).subtype
  have hf : Function.Surjective f :=
    (E.cartan_component_fixed_residual_cover_of_marked hp hT hX c hcart hXR hCX hz
      hNG hthree hexception hI).1
  have hs : Function.Surjective (e.toMonoidHom.comp f) := e.surjective.comp hf
  refine ⟨F,inferInstance,inferInstance,hF,e,hs,?_,?_⟩
  · let k : (e.toMonoidHom.comp f).ker →* twoFittingCore I :=
      (((inclusion (show C ≤ I from inf_le_left)).comp (solvableResidual C).subtype).comp
        (e.toMonoidHom.comp f).ker.subtype).codRestrict _ (by
          intro j
          apply (QuotientGroup.eq_one_iff (N := twoFittingCore I) _).mp
          apply e.map_eq_one_iff.mp
          exact MonoidHom.mem_ker.mp j.property)
    let : Group.IsSolvable (twoFittingCore I) := twoFittingCore_solvable
    exact Group.isSolvable_of_isSolvable_injective (f := k) (by
      intro a b hab
      exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg
        (fun z : twoFittingCore I => ((z : I) : G)) hab))))
  · have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 120 := by
      rw [Atlas.card_sl_two,hF]
      norm_num
    exact hcard ▸ card_dvd_of_surjective (e.toMonoidHom.comp f) hs
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
