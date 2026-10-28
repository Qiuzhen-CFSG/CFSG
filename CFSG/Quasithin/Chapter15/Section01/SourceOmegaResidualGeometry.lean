module
public import CFSG.Quasithin.Chapter15.Section01.SourceOmegaSplitting
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import Theory.SpecificGroups.OrthogonalFourBinary.OmegaResidualGeometry

/-!
# The residual geometry in the natural Omega branch

The source Omega coordinates identify the cubic commutator residual in the
chosen normalizer with the order-nine odd residual in the two symmetric-three
factors.  The coordinate lemma is stated with the literal subgroup-of action;
this keeps the proper chosen module unchanged while allowing the source
assembly to provide its quotient map and Sylow image.

Source: Aschbacher--Smith 15.1.11, final paragraph, printed p.1089.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD NoncentralChiefRefinement ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/--
The three literal hypotheses needed by `source_chosenNormalizer_commutatorResidual_splitting`
are discharged by the natural Omega coordinate calculation.  The quotient map
`q`, its coordinates on the literal `V.subgroupOf N`, and the Sylow image are
kept explicit so a final source consumer can instantiate the actual action
quotient without identifying a false complement in the ambient group.
-/
theorem source_chosenNormalizer_omega_residual_geometry_of_coordinates
    (_hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    [WNormal : (V.subgroupOf (chosenNormalizer T M V)).Normal]
    [WElementary : IsElementaryAbelian 2 (V.subgroupOf (chosenNormalizer T M V))]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (_hVne : V ≠ ⊥)
    (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (_ho : SourceCases.Omega (imageRepresentation M V hMV))
    (_himage : ChapterD.internalActionImage (chosenNormalizer T M V) V
      (inf_le_left.trans hMV) = ChapterD.internalActionImage M V hMV)
    (q : chosenNormalizer T M V →* OrthogonalFourBinary.omega)
    (hq : Function.Surjective q)
    (e : OrthogonalFourBinary.omega ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (x : Additive (V.subgroupOf (chosenNormalizer T M V)) ≃ₗ[ZMod 2]
      OrthogonalFourBinary.Space)
    (hx : ∀ n w, x (normalRepresentation (V.subgroupOf (chosenNormalizer T M V)) n w) =
      (q n).val.val (x w))
    (P : Subgroup (chosenNormalizer T M V))
    (S : Sylow 2 OrthogonalFourBinary.omega) (hP : P.map q = S) :
    let N := chosenNormalizer T M V
    let W := V.subgroupOf N
    let X := Subgroup.cubicCommutatorResidual P
    ⁅W,X⁆ = W ∧ W ⊓ centralizer (X : Set N) = ⊥ ∧
      IsElementaryAbelian 3 (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) ∧
      Nat.card (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) = 9 := by
  let N := chosenNormalizer T M V
  let W := V.subgroupOf N
  have hred := chosenNormalizer_reduced T hTM hVM hMV hspan
  have hg := OrthogonalFourBinary.commutatorResidual_geometry W q hq e x hx P S hP
  exact hg

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Coordinates transported from an Omega image to the literal chosen normalizer. -/
structure ChosenOmegaCoordinates (N : Subgroup G) (W : Subgroup N)
    [IsElementaryAbelian 2 W] [W.Normal] where
  q : N →* OrthogonalFourBinary.omega
  surjective : Function.Surjective q
  e : OrthogonalFourBinary.omega ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  x : Additive W ≃ₗ[ZMod 2] OrthogonalFourBinary.Space
  coord : ∀ n w, x (normalRepresentation W n w) = (q n).val.val (x w)

/-- The source Omega witness gives a faithful quotient map and coordinates on
`V.subgroupOf (chosenNormalizer T M V)`.  The action-image equality is used to
transport the actual chosen-normalizer action, rather than introducing an
unrelated abstract cover. -/
theorem source_chosenNormalizer_omega_coordinates
    (_hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (_hVne : V ≠ ⊥)
    (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (ho : SourceCases.Omega (imageRepresentation M V hMV)) :
    let N := chosenNormalizer T M V
    let W := V.subgroupOf N
    letI := (chosenNormalizer_reduced T hTM hVM hMV hspan).normal
    letI := (chosenNormalizer_reduced T hTM hVM hMV hspan).elementary
    Nonempty (ChosenOmegaCoordinates N W) := by
  dsimp only
  let N := chosenNormalizer T M V
  let W := V.subgroupOf N
  have hred := chosenNormalizer_reduced T hTM hVM hMV hspan
  let _ := hred.normal
  let _ := hred.elementary
  rcases ho with ⟨_,_,_,hpair,hcoords⟩
  let eD : ChapterD.internalActionImage M V hMV ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    Classical.choice hpair
  let xV : Additive V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space :=
    Classical.choose hcoords
  have hcoords' : ∃ e : ChapterD.internalActionImage M V hMV ≃*
      OrthogonalFourBinary.omega,
      ∀ g v, xV ((imageRepresentation M V hMV g) v) =
        (e g).val.val (xV v) := Classical.choose_spec hcoords
  let eΩ : ChapterD.internalActionImage M V hMV ≃*
      OrthogonalFourBinary.omega := Classical.choose hcoords'
  have hcoord : ∀ g v, xV ((imageRepresentation M V hMV g) v) =
      (eΩ g).val.val (xV v) := Classical.choose_spec hcoords'
  have hWN : V ≤ N := module_le_chosenNormalizer T hTM hVM hMV
  let ev : W ≃* V := subgroupOfEquivOfLe hWN
  let evlin : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (ev.toMonoidHom.toAdditive.toZModLinearMap 2)
      ev.toAdditive.bijective
  let xW : Additive W ≃ₗ[ZMod 2] OrthogonalFourBinary.Space := evlin.trans xV
  let hN : N ≤ normalizer (V : Set G) := inf_le_left.trans hMV
  let hImg := chosenNormalizer_actionImage_eq T hTM hMV
  change (actionHom N V hN).range = (actionHom M V hMV).range at hImg
  let eImg : (actionHom N V hN).range ≃* (actionHom M V hMV).range :=
    MulEquiv.subgroupCongr hImg
  let qD : N →* ChapterD.internalActionImage M V hMV :=
    eImg.toMonoidHom.comp (actionHom N V hN).rangeRestrict
  have hqD : Function.Surjective qD :=
    eImg.surjective.comp (actionHom N V hN).rangeRestrict_surjective
  let q : N →* OrthogonalFourBinary.omega := eΩ.toMonoidHom.comp qD
  have hq : Function.Surjective q := eΩ.surjective.comp hqD
  refine ⟨⟨q,hq,eΩ.symm.trans eD,xW,?_⟩⟩
  intro n w
  dsimp [xW, evlin, q, qD, ev, hN]
  change xV (evlin (normalRepresentation W n w)) =
    (eΩ (qD n)).val.val (xV (evlin w))
  rw [← hcoord (qD n) (evlin w)]
  apply congrArg xV
  apply Additive.toMul.injective
  apply Subtype.ext
  change n * (w.toMul : G) * n⁻¹ = ((qD n).val : MulAut V) (ev (w.toMul))
  change n * (w.toMul : G) * n⁻¹ = (actionHom N V hN n) (ev (w.toMul))
  rfl

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor

variable {G : Type*} [Group G] [Finite G]

/-- The chosen-normalizer Omega source facts, with the coordinate transport
already discharged from the actual `SourceCases.Omega` witness. -/
theorem source_chosenNormalizer_omega_residual_geometry
    (_hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (_hVne : V ≠ ⊥)
    (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (ho : SourceCases.Omega (imageRepresentation M V hMV))
    (P : Subgroup (chosenNormalizer T M V))
    (S : Sylow 2 OrthogonalFourBinary.omega) :
    let N := chosenNormalizer T M V
    let W := V.subgroupOf N
    letI := (chosenNormalizer_reduced T hTM hVM hMV hspan).normal
    letI := (chosenNormalizer_reduced T hTM hVM hMV hspan).elementary
    let c := Classical.choice
      (source_chosenNormalizer_omega_coordinates _hG T hTM hVM _hVne hMV hspan ho)
    P.map c.q = S →
    let X := Subgroup.cubicCommutatorResidual P
    ⁅W,X⁆ = W ∧ W ⊓ centralizer (X : Set N) = ⊥ ∧
      IsElementaryAbelian 3 (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) ∧
      Nat.card (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) = 9 := by
  dsimp only
  let N := chosenNormalizer T M V
  let W := V.subgroupOf N
  let _ := (chosenNormalizer_reduced T hTM hVM hMV hspan).normal
  let _ := (chosenNormalizer_reduced T hTM hVM hMV hspan).elementary
  let c := Classical.choice
    (source_chosenNormalizer_omega_coordinates _hG T hTM hVM _hVne hMV hspan ho)
  intro hP
  exact OrthogonalFourBinary.commutatorResidual_geometry W c.q c.surjective c.e c.x c.coord P S hP

end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The canonical choice uses the original Sylow subgroup inside the chosen
normalizer, so its Omega image is a Sylow subgroup without an extra image
premise. -/
theorem source_chosenNormalizer_omega_residual_geometry_of_chosenSylow
    (_hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (_hVne : V ≠ ⊥)
    (hMV : M ≤ normalizer (V : Set G))
    (hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M)
    (ho : SourceCases.Omega (imageRepresentation M V hMV)) :
    let N := chosenNormalizer T M V
    let W := V.subgroupOf N
    letI := (chosenNormalizer_reduced T hTM hVM hMV hspan).normal
    letI := (chosenNormalizer_reduced T hTM hVM hMV hspan).elementary
    let P : Sylow 2 N := T.subtype (sylow_le_chosenNormalizer T hTM hMV)
    let X := Subgroup.cubicCommutatorResidual (P : Subgroup N)
    ⁅W,X⁆ = W ∧ W ⊓ centralizer (X : Set N) = ⊥ ∧
      IsElementaryAbelian 3 (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) ∧
      Nat.card (X.map (QuotientGroup.mk' (centralizer (W : Set N)))) = 9 := by
  dsimp only
  let N := chosenNormalizer T M V
  let W := V.subgroupOf N
  let _ := (chosenNormalizer_reduced T hTM hVM hMV hspan).normal
  let _ := (chosenNormalizer_reduced T hTM hVM hMV hspan).elementary
  let c := Classical.choice
    (source_chosenNormalizer_omega_coordinates _hG T hTM hVM _hVne hMV hspan ho)
  let P : Sylow 2 N := T.subtype (sylow_le_chosenNormalizer T hTM hMV)
  let S : Sylow 2 OrthogonalFourBinary.omega := P.mapSurjective (f := c.q) c.surjective
  let X := Subgroup.cubicCommutatorResidual (P : Subgroup N)
  have hP : (P : Subgroup N).map c.q = (S : Subgroup OrthogonalFourBinary.omega) := by
    exact Sylow.coe_mapSurjective c.surjective P
  exact OrthogonalFourBinary.commutatorResidual_geometry W c.q c.surjective c.e c.x c.coord
    (P : Subgroup N) S hP

end CFSG.Quasithin.Chapter15.Section01
