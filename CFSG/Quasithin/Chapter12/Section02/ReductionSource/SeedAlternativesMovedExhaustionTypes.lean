module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenModules
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveLinearThree
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTwoTypeModels
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionTypes

/-!
# The two constituent types on the full chosen-seed normalizer orbit

The original reduced-subspace coordinates identify the literal L-conjugation
module with each marked D.3.10 model. Its characteristic action kernel lets
normalizer conjugation descend to an automorphism of that same model. The
proved automorphism-twist bounds then give the seed type or the type marked
by a moving Sylow element, for every normalizer conjugate.

The SL₃ case retains its scalar centre, and the four-dimensional A₇ case
remains distinct from natural A₆. No homogeneity in the larger orbit is
assumed. `SeedAlternativesMovedExhaustionTypesAssembly` applies these results
to the actual Chapter12 choice and reduces exhaustion to repeated copies.

Source: Aschbacher--Smith D.3.10, paragraph following D.3.11, printed p.201.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original reduced-subspace inclusion supplies coordinates on the actual
chosen subgroup, with its unchanged component map. -/
def seedConjugationCoordinates (D : ChosenModule T L V)
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) P W)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) τ) :
    ConjugationCoordinates L V τ (e.groupEquiv.toMonoidHom.comp D.componentHom) := by
  refine ⟨D.normalizes,D.spaceEquiv.symm.trans
    e.linearEquiv.toAddEquiv.toMultiplicative,?_⟩
  intro l v w hw
  let a := (D.spaceEquiv.symm v).toAdd
  let b := (D.spaceEquiv.symm w).toAdd
  have ha : a.val.toMul.val.val = v.val :=
    (D.spaceEquiv_apply a).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  have hb : b.val.toMul.val.val = w.val :=
    (D.spaceEquiv_apply b).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply w))
  have he : D.seedRepresentation (D.componentHom l).val a = b := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change l.val * a.val.toMul.val.val * l.val⁻¹ = b.val.toMul.val.val
    rw [ha,hb,hw]
  change e.linearEquiv b = τ (e.groupEquiv (D.componentHom l)) (e.linearEquiv a)
  rw [←he]
  exact e.intertwines (D.componentHom l) a

omit [Finite G] in
/-- The characteristic-kernel model controls all normalizer conjugates,
without assuming homogeneous selection in the larger orbit. -/
theorem normalizer_two_types_of_characteristic_model_twists
    (D : ChosenModule T L V) (hker : D.componentHom.ker.Characteristic)
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (τ τ' : Representation (ZMod 2) P W)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) τ)
    (htypes : ∀ a : MulAut P, Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ'))
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G)) :
    ∀ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom) := by
  let f := e.groupEquiv.toMonoidHom.comp D.componentHom
  let : f.ker.Characteristic :=
    characteristic_kernel_model_transport D.componentHom hker (MulEquiv.refl L) e.groupEquiv
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp D.componentHom_surjective
  exact fun g hg => two_conjugation_types_of_characteristic_model
    (D.seedConjugationCoordinates τ e) hf htypes
    ⟨t,D.sylow_normalizes_component ht⟩ (D.moved_conjugate_not_sameModule ht hnt) ⟨g,hg⟩

/-- A center-free constituent model supplies the characteristic kernel. -/
theorem normalizer_two_types_of_centerFree_model_twists
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (τ τ' : Representation (ZMod 2) P W) (hz : center P = ⊥)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) τ)
    (htypes : ∀ a : MulAut P, Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) ∨
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ'))
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G)) :
    ∀ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom) :=
  by
    let := hq
    have hk := kernel_characteristic_of_quasisimple_quotient (pCore 2 L)
      D.componentHom D.componentQuotientHom D.componentQuotientHom_surjective
      D.componentQuotientHom_mk (center_eq_bot_of_model_equiv e.groupEquiv hz)
    exact D.normalizer_two_types_of_characteristic_model_twists hk τ τ' e htypes t ht hnt

/-- Every marked D.3.10 model has exactly the two possible unchanged-L types
on the normalizer conjugates, marked by any moving Sylow element. -/
theorem normalizer_two_types_of_constituentModel
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype))
    (t : G) (ht : t ∈ (T : Subgroup G)) (hnt : t ∉ normalizer (V : Set G)) :
    ∀ g ∈ normalizer (L : Set G),
      SameConjugationModule L V (V.map (MulAut.conj g).toMonoidHom) ∨
      SameConjugationModule L (V.map (MulAut.conj t).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom) := by
  rcases hmodel with h | h | h | h | h
  · obtain ⟨F,⟨e⟩⟩ := h
    obtain ⟨τ',hτ⟩ := linearThree_two_twists F
    let := hq
    have hk := kernel_characteristic_of_linearThree_equiv F D.componentHom
      D.componentQuotientHom D.componentQuotientHom_surjective D.componentQuotientHom_mk e.groupEquiv
    exact D.normalizer_two_types_of_characteristic_model_twists hk _ τ' e hτ t ht hnt
  · obtain ⟨F,_,⟨e⟩⟩ := h
    obtain ⟨τ',hτ⟩ := symplectic_four_two_twists (F := F.Carrier)
    exact D.normalizer_two_types_of_centerFree_model_twists hq _ τ'
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot e hτ t ht hnt
  · obtain ⟨e⟩ := h
    obtain ⟨τ',hτ⟩ := alternating_six_two_twists
    exact D.normalizer_two_types_of_centerFree_model_twists hq _ τ'
      (alternatingGroup.center_eq_bot (by norm_num)) e hτ t ht hnt
  · obtain ⟨n,hn,⟨e⟩⟩ := h
    obtain ⟨τ',hτ⟩ := binary_linear_two_twists hn (linearNatural BinaryField.two n)
    exact D.normalizer_two_types_of_centerFree_model_twists hq _ τ'
      (BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega)) e hτ t ht hnt
  · obtain ⟨σ,_,⟨e⟩⟩ := h
    obtain ⟨τ',hτ⟩ := alternating_seven_two_twists σ
    exact D.normalizer_two_types_of_centerFree_model_twists hq _ τ'
      (alternatingGroup.center_eq_bot (by norm_num)) e hτ t ht hnt


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
