module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowSieve
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTwoTypes
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTwoTypeModels
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Two constituent types on the original chosen-seed action

A characteristic model kernel lets ambient conjugation act on the actual
faithful component image. The two-twist theorem then gives two actual
homogeneous conjugates. Passing through the original subgroup image proves
`SylowTwoModuleTypes` for the natural A₆, four-dimensional A₇, symplectic,
and binary SL₄/SL₅ rows. The subgroup comparisons fix the original L-action.

The model-list application leaves only the SL₃ row explicit. The source
consumer in `SeedAlternativesMovedSylowTwoTypesAssembly` retains that row,
exceptional-row exclusion and full-normalizer exhaustion with qt-baumann-fsu.

Source: Aschbacher--Smith D.3.5(4), combined manuscript of 1 March 2004,
printed pp.195--196, applied to 3.2.5 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Two twists of a marked model with characteristic action kernel exhaust the literal Sylow conjugates. -/
theorem sylowTwoModuleTypes_of_characteristic_model_twists (D : ChosenModule T L V)
    (hker : D.componentHom.ker.Characteristic)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (τ τ₁ : Representation (ZMod 2) P W)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) τ)
    (htypes : ∀ a : MulAut P, Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁)) :
    D.SylowTwoModuleTypes := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let R := (T : Subgroup G).subgroupOf H
  let ρ := reducedRepresentation H
  have himage : ReducedNormal.subspaceImage H D.space = V := D.image_eq
  let j : X ≃* L := subgroupOfEquivOfLe le_sup_left
  let r := D.componentHom.comp j.toMonoidHom
  let f := e.groupEquiv.toMonoidHom.comp r
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp
    (D.componentHom_surjective.comp j.surjective)
  let : f.ker.Characteristic :=
    characteristic_kernel_model_transport D.componentHom hker j e.groupEquiv
  let b : Representation.Equiv (invariantSubspace ρ X D.space D.irrPlus.invariant).toRepresentation
      (τ.comp f) := Representation.Equiv.mk e.linearEquiv (by
    intro x
    apply LinearMap.ext
    intro v
    have he := e.intertwines (D.componentHom (j x)) v
    change e.linearEquiv ((invariantSubspace ρ X D.space D.irrPlus.invariant).toRepresentation x v) = _ at he
    exact he)
  let q := QuotientGroup.quotientKerEquivOfSurjective f hf
  let bq := (zeroFixedImageEquiv ρ X D.space D.irrPlus.invariant
    (D.seed_inf_fixedSpace_eq_bot hc)).symm.trans b
  have hmove : ∃ t : R, D.space.map (ρ t.val) ≠ D.space := by
    by_contra! hfix
    apply hm.not_ge
    apply iSup_le
    intro s
    let s' : R := ⟨⟨s,(le_sup_right : (T : Subgroup G) ≤ H) s.property⟩,s.property⟩
    have he := congrArg (ReducedNormal.subspaceImage H) (hfix s')
    change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H s'.val)) =
      ReducedNormal.subspaceImage H D.space at he
    rw [ReducedNormal.subspaceImage_map,himage] at he
    exact he.le
  obtain ⟨t,ht,htypes⟩ := homogeneous_two_conjugates_of_quotient_twists ρ D.irrPlus
    f.ker q τ τ₁ bq hmove htypes
  have hnot : t.val.val ∉ normalizer (V : Set G) := by
    intro hn
    apply ht
    apply ReducedNormal.subspaceImage_injective H
    change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H t.val)) =
      ReducedNormal.subspaceImage H D.space
    rw [ReducedNormal.subspaceImage_map,himage]
    exact mem_normalizer_iff_map_conj_eq.mp hn
  have hrefl (U : Subgroup G) : SameConjugationModule L U U :=
    ⟨MulEquiv.refl U,fun _ _ _ he => he⟩
  refine ⟨t.val.val,t.property,hnot,fun s hs => ?_⟩
  let s' : R := ⟨⟨s,(le_sup_right : (T : Subgroup G) ≤ H) hs⟩,hs⟩
  rcases htypes s' with he | he
  · have he' := congrArg (ReducedNormal.subspaceImage H) he
    change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H s'.val)) =
      ReducedNormal.subspaceImage H D.space at he'
    rw [ReducedNormal.subspaceImage_map,himage] at he'
    change V.map (MulAut.conj s).toMonoidHom = V at he'
    apply Or.inl
    rw [he']
    exact hrefl V
  · have he' := congrArg (ReducedNormal.subspaceImage H) he
    change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H s'.val)) =
      ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H t.val)) at he'
    rw [ReducedNormal.subspaceImage_map,ReducedNormal.subspaceImage_map,himage] at he'
    change V.map (MulAut.conj s).toMonoidHom = V.map (MulAut.conj t.val.val).toMonoidHom at he'
    apply Or.inr
    rw [he']
    exact hrefl _

/-- Two twists of a center-free marked model exhaust the literal Sylow conjugates of the chosen seed. -/
theorem sylowTwoModuleTypes_of_model_twists (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (τ τ₁ : Representation (ZMod 2) P W) (hz : center P = ⊥)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) τ)
    (htypes : ∀ a : MulAut P, Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ₁)) :
    D.SylowTwoModuleTypes := by
  exact D.sylowTwoModuleTypes_of_characteristic_model_twists
    (D.componentHom_kernel_characteristic hq (center_eq_bot_of_model_equiv e.groupEquiv hz))
    hc hm τ τ₁ e htypes

/-- The natural A₆ row supplies the two unchanged-L types without a type-bound premise. -/
theorem sylowTwoModuleTypes_of_alternatingSix (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (alternatingNatural 6)) :
    D.SylowTwoModuleTypes := by
  obtain ⟨τ₁,htypes⟩ := alternating_six_two_twists
  exact D.sylowTwoModuleTypes_of_model_twists hq hc hm (alternatingNatural 6) τ₁
    (alternatingGroup.center_eq_bot (by norm_num)) e htypes

/-- Either marked four-dimensional A₇ row supplies the two unchanged-L types. -/
theorem sylowTwoModuleTypes_of_alternatingSeven (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ) :
    D.SylowTwoModuleTypes := by
  obtain ⟨τ₁,htypes⟩ := alternating_seven_two_twists σ
  exact D.sylowTwoModuleTypes_of_model_twists hq hc hm σ τ₁
    (alternatingGroup.center_eq_bot (by norm_num)) e htypes

/-- The natural symplectic row supplies the two unchanged-L types. -/
theorem sylowTwoModuleTypes_of_symplectic (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) (F : BinaryField)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))) :
    D.SylowTwoModuleTypes := by
  obtain ⟨τ₁,htypes⟩ := symplectic_four_two_twists (F := F.Carrier)
  exact D.sylowTwoModuleTypes_of_model_twists hq hc hm _ τ₁
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot e htypes

/-- The natural binary SL₄ and SL₅ rows supply the two unchanged-L types. -/
theorem sylowTwoModuleTypes_of_binaryLinear (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural BinaryField.two n)) : D.SylowTwoModuleTypes := by
  obtain ⟨τ₁,htypes⟩ := binary_linear_two_twists hn (linearNatural BinaryField.two n)
  exact D.sylowTwoModuleTypes_of_model_twists hq hc hm _ τ₁
    (BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega)) e htypes

/-- The complete marked model list reduces the type bound to its SL₃ row, retained by qt-baumann-fsu. -/
theorem sylowTwoModuleTypes_of_constituentModel_of_linearThree
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype))
    (hthree : ∀ F : BinaryField,
      ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3) →
      D.SylowTwoModuleTypes) : D.SylowTwoModuleTypes := by
  rcases hmodel with h | h | h | h | h
  · obtain ⟨F,⟨e⟩⟩ := h
    exact hthree F e
  · obtain ⟨F,_,⟨e⟩⟩ := h
    exact D.sylowTwoModuleTypes_of_symplectic hq hc hm F e
  · obtain ⟨e⟩ := h
    exact D.sylowTwoModuleTypes_of_alternatingSix hq hc hm e
  · obtain ⟨n,hn,⟨e⟩⟩ := h
    exact D.sylowTwoModuleTypes_of_binaryLinear hq hc hm n hn e
  · obtain ⟨σ,_,⟨e⟩⟩ := h
    exact D.sylowTwoModuleTypes_of_alternatingSeven hq hc hm σ e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
