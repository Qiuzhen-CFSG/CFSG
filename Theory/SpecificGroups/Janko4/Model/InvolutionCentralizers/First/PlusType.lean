module

public import Theory.GroupTheory.DihedralCentralProductSix

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.PlusType.Generation
import all Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core

/-!
# The marked plus-type first J₄ two-core

The coordinate calculation in `PlusType.Quadratic` constructs six actual
hyperbolic pairs in the seed normal closure. The established inclusion-preserving
equivalences transport them into the intrinsic two-core of the literal
centralizer of `Janko4.a`. Their square and commutator identities retain the
same distinguished central involution. The internal import of `First.Core`
is used only to establish equations for its non-exposed marked-involution
definition, preserving that module and its public boundary.

The generating pairs instantiate the marked dihedral recognition theorem.
Its source is the explicit quotient of `Fin 6 → DihedralGroup 4` by the
five relations identifying the first central involution with the others.
We obtain actual isomorphisms with the normal closure, the matrix two-core,
and the literal `O₂(C_J₄(a))`. The product map has exactly this prescribed
kernel; its six dihedral factors are injective and commute pairwise. The
isomorphisms preserve the ambient embedding and send every factor's central
involution to the distinguished first generator `a`.

This proves the plus-type core clause of Aschbacher–Smith 16.1.5(9), printed
p.1172 (GLS3 Table 5.3i, printed p.270). The full centralizer extension is
assembled separately in the first-centralizer development.
-/

public section

namespace Janko4.InvolutionCentralizers.First.PlusType
open Subgroup
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData NormalClosureControl.IntrinsicCenter OuterImageComparison
open scoped BigOperators

attribute [local irreducible] normalClosureEquivTwoCore twoCoreEquiv centralizerEquiv

/-- The marked normal-closure involution maps to the literal core involution. -/
theorem centralWord_image : normalClosureEquivTwoCore centralWord = twoCoreInvolution := by
  apply Subtype.ext
  rw [normalClosureEquivTwoCore_coe]
  rfl

/-- The twelve specified lifts, embedded in the actual matrix-centralizer two-core. -/
noncomputable def twoCoreLift (i : Fin 6) (side : Bool) : involutionTwoCore :=
  normalClosureEquivTwoCore (hyperbolicLift i side)

/-- The inclusion is the original inclusion of the certified word. -/
theorem twoCoreLift_coe (i : Fin 6) (side : Bool) :
    (twoCoreLift i side : involutionCentralizer) =
      ((hyperbolicLift i side : localSubgroup) : involutionCentralizer) :=
  normalClosureEquivTwoCore_coe _

theorem twoCoreLift_square (i : Fin 6) (side : Bool) : twoCoreLift i side ^ 2 = 1 := by
  rw [twoCoreLift, ← map_pow, hyperbolicLift_square, map_one]

/-- The hyperbolic twists retain the distinguished central involution in O₂(C). -/
theorem twoCoreLift_twist (i j : Fin 6) (a b : Bool) :
    twoCoreLift i a * twoCoreLift j b =
      twoCoreLift j b * twoCoreLift i a *
        bit twoCoreInvolution (decide (i = j) && (a ^^ b)) := by
  have h := congrArg normalClosureEquivTwoCore (hyperbolicLift_twist i j a b)
  simpa only [twoCoreLift, map_mul, bit, apply_ite, centralWord_image, map_one] using h

/-- The marked involution in the literal subgroup O₂(C_J₄(a)). -/
noncomputable def literalCoreInvolution : pCore 2 centralizer :=
  twoCoreEquiv.symm twoCoreInvolution

/-- The same twelve words as elements of the intrinsic two-core inside J₄. -/
noncomputable def literalCoreLift (i : Fin 6) (side : Bool) : pCore 2 centralizer :=
  twoCoreEquiv.symm (twoCoreLift i side)

theorem literalCoreLift_square (i : Fin 6) (side : Bool) :
    literalCoreLift i side ^ 2 = 1 := by
  rw [literalCoreLift, ← map_pow, twoCoreLift_square, map_one]

theorem literalCoreLift_twist (i j : Fin 6) (a b : Bool) :
    literalCoreLift i a * literalCoreLift j b =
      literalCoreLift j b * literalCoreLift i a *
        bit literalCoreInvolution (decide (i = j) && (a ^^ b)) := by
  have h := congrArg twoCoreEquiv.symm (twoCoreLift_twist i j a b)
  simpa only [literalCoreLift, literalCoreInvolution, map_mul, bit, apply_ite, map_one] using h

/-- The square formula on every element of the intrinsic matrix-centralizer two-core. -/
theorem twoCore_square (g : involutionTwoCore) :
    g ^ 2 = bit twoCoreInvolution
      (quadratic (elementBits (normalClosureEquivTwoCore.symm g))) := by
  have h := congrArg normalClosureEquivTwoCore
    (square_eq_quadratic (normalClosureEquivTwoCore.symm g))
  simpa only [map_pow, MulEquiv.apply_symm_apply, bit, apply_ite,
    centralWord_image, map_one] using h

/-- The marked involution is literally the first generator of J₄. -/
theorem literalCoreInvolution_coe :
    ((literalCoreInvolution : centralizer) : Model) = a := by
  apply toAmbient_injective
  rw [← centralizerEquiv_coe, ← twoCoreEquiv_coe]
  change ((twoCoreEquiv (twoCoreEquiv.symm twoCoreInvolution) : involutionCentralizer) :
    BinaryMatrixˣ) = toAmbient a
  rw [twoCoreEquiv.apply_symm_apply]
  rfl

/-- The lifts preserve their original ambient matrices inside the literal J₄ carrier. -/
theorem literalCoreLift_coe (i : Fin 6) (side : Bool) :
    toAmbient ((literalCoreLift i side : centralizer) : Model) =
      (((hyperbolicLift i side : localSubgroup) : involutionCentralizer) : BinaryMatrixˣ) := by
  rw [← centralizerEquiv_coe, ← twoCoreEquiv_coe]
  change ((twoCoreEquiv (twoCoreEquiv.symm (twoCoreLift i side)) : involutionCentralizer) :
    BinaryMatrixˣ) = _
  rw [twoCoreEquiv.apply_symm_apply, twoCoreLift_coe]

private theorem closure_range_equiv {G H ι : Type*} [Group G] [Group H]
    (e : G ≃* H) (f : ι → G) (hf : closure (Set.range f) = ⊤) :
    closure (Set.range (fun i => e (f i))) = ⊤ := by
  have hi : e.toMonoidHom '' Set.range f = Set.range (fun i => e (f i)) :=
    (Set.range_comp e f).symm
  rw [← hi, ← MonoidHom.map_closure, hf, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr e.surjective

/-- The explicit hyperbolic pairs generate the intrinsic matrix-centralizer two-core. -/
theorem twoCoreLift_generate :
    closure (Set.range (fun p : Fin 6 × Bool => twoCoreLift p.1 p.2)) = ⊤ := by
  exact @closure_range_equiv localNormalClosure involutionTwoCore (Fin 6 × Bool)
    inferInstance inferInstance normalClosureEquivTwoCore
    (fun p : Fin 6 × Bool => hyperbolicLift p.1 p.2) hyperbolicLift_generate

/-- The same pairs generate O₂(C_J₄(a)) inside the literal J₄ carrier. -/
theorem literalCoreLift_generate :
    closure (Set.range (fun p : Fin 6 × Bool => literalCoreLift p.1 p.2)) = ⊤ := by
  exact @closure_range_equiv involutionTwoCore (pCore 2 centralizer) (Fin 6 × Bool)
    inferInstance inferInstance twoCoreEquiv.symm
    (fun p : Fin 6 × Bool => twoCoreLift p.1 p.2) twoCoreLift_generate


/-- All recognition relations hold for the actual twelve certified words. -/
theorem hyperbolicRelations : DihedralCentralProductSix.Relations centralWord hyperbolicLift where
  central := centralWord_mem_center
  order := centralWord_order
  square := hyperbolicLift_square
  twist := hyperbolicLift_pair_twist
  commute := fun _ _ hij => hyperbolicLift_commute hij

/-- The actual seed normal closure is the explicit central product of six D₈ factors. -/
noncomputable def normalClosurePlusEquiv :
    DihedralCentralProductSix.Model ≃* localNormalClosure :=
  DihedralCentralProductSix.recognition (G := localNormalClosure) hyperbolicRelations hyperbolicLift_generate normalClosure_card

/-- Recognition keeps the concrete product homomorphism on every quotient representative. -/
theorem normalClosurePlusEquiv_mk (x : DihedralCentralProductSix.D) :
    normalClosurePlusEquiv (QuotientGroup.mk x) =
      DihedralCentralProductSix.phi hyperbolicRelations x :=
  DihedralCentralProductSix.recognition_mk ..

/-- Plus type of the intrinsic two-core in the matrix centralizer. -/
noncomputable def twoCorePlusEquiv :
    DihedralCentralProductSix.Model ≃* involutionTwoCore :=
  normalClosurePlusEquiv.trans normalClosureEquivTwoCore

/-- The central-product equivalence preserves the established normal-closure inclusion. -/
theorem twoCorePlusEquiv_coe (q : DihedralCentralProductSix.Model) :
    (twoCorePlusEquiv q : involutionCentralizer) =
      ((normalClosurePlusEquiv q : localNormalClosure) : localSubgroup) :=
  normalClosureEquivTwoCore_coe _

/-- The explicit sixfold dihedral central product is O₂(C_J₄(a)) in the literal carrier. -/
noncomputable def literalCorePlusEquiv :
    DihedralCentralProductSix.Model ≃* pCore 2 centralizer :=
  twoCorePlusEquiv.trans twoCoreEquiv.symm

/-- Compatibility of the isomorphism with the actual embedding into the binary matrices. -/
theorem literalCorePlusEquiv_coe (q : DihedralCentralProductSix.Model) :
    toAmbient ((literalCorePlusEquiv q : centralizer) : Model) =
      (((normalClosurePlusEquiv q : localSubgroup) : involutionCentralizer) : BinaryMatrixˣ) := by
  rw [← centralizerEquiv_coe, ← twoCoreEquiv_coe]
  change ((twoCoreEquiv (twoCoreEquiv.symm (twoCorePlusEquiv q)) :
    involutionCentralizer) : BinaryMatrixˣ) = _
  rw [twoCoreEquiv.apply_symm_apply, twoCorePlusEquiv_coe]

/-- The rotation in each D₈ factor is the product of its two marked lifts. -/
theorem normalClosurePlusEquiv_r_one (i : Fin 6) :
    normalClosurePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 1))) =
      hyperbolicLift i false * hyperbolicLift i true :=
  DihedralCentralProductSix.recognition_r_one ..

/-- The first reflection retains its actual word marking. -/
theorem normalClosurePlusEquiv_sr_zero (i : Fin 6) :
    normalClosurePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.sr 0))) =
      hyperbolicLift i false :=
  DihedralCentralProductSix.recognition_sr_zero ..

/-- The common central involution retains its actual word marking. -/
theorem normalClosurePlusEquiv_r_two (i : Fin 6) :
    normalClosurePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 2))) =
      centralWord :=
  DihedralCentralProductSix.recognition_r_two ..

theorem twoCorePlusEquiv_r_one (i : Fin 6) :
    twoCorePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 1))) =
      twoCoreLift i false * twoCoreLift i true := by
  change normalClosureEquivTwoCore (normalClosurePlusEquiv _) = _
  rw [normalClosurePlusEquiv_r_one, map_mul]
  rfl

theorem twoCorePlusEquiv_sr_zero (i : Fin 6) :
    twoCorePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.sr 0))) =
      twoCoreLift i false := by
  change normalClosureEquivTwoCore (normalClosurePlusEquiv _) = _
  rw [normalClosurePlusEquiv_sr_zero]
  rfl

theorem twoCorePlusEquiv_r_two (i : Fin 6) :
    twoCorePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 2))) =
      twoCoreInvolution := by
  change normalClosureEquivTwoCore (normalClosurePlusEquiv _) = _
  rw [normalClosurePlusEquiv_r_two, centralWord_image]

theorem literalCorePlusEquiv_r_one (i : Fin 6) :
    literalCorePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 1))) =
      literalCoreLift i false * literalCoreLift i true := by
  change twoCoreEquiv.symm (twoCorePlusEquiv _) = _
  rw [twoCorePlusEquiv_r_one, map_mul]
  rfl

theorem literalCorePlusEquiv_sr_zero (i : Fin 6) :
    literalCorePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.sr 0))) =
      literalCoreLift i false := by
  change twoCoreEquiv.symm (twoCorePlusEquiv _) = _
  rw [twoCorePlusEquiv_sr_zero]
  rfl

theorem literalCorePlusEquiv_r_two (i : Fin 6) :
    literalCorePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 2))) =
      literalCoreInvolution := by
  change twoCoreEquiv.symm (twoCorePlusEquiv _) = _
  rw [twoCorePlusEquiv_r_two]
  rfl

/-- Every factor's central involution maps to the literal first generator a of J₄. -/
theorem literalCorePlusEquiv_r_two_coe (i : Fin 6) :
    ((literalCorePlusEquiv (QuotientGroup.mk (Pi.mulSingle i (DihedralGroup.r 2))) :
      centralizer) : Model) = a := by
  rw [literalCorePlusEquiv_r_two, literalCoreInvolution_coe]

/-- The marked homomorphism from D₈⁶ onto the actual first-centralizer two-core. -/
noncomputable def literalCoreProductMap :
    DihedralCentralProductSix.D →* pCore 2 centralizer :=
  literalCorePlusEquiv.toMonoidHom.comp (QuotientGroup.mk' DihedralCentralProductSix.Delta)

theorem literalCoreProductMap_apply (x : DihedralCentralProductSix.D) :
    literalCoreProductMap x = literalCorePlusEquiv (QuotientGroup.mk x) := by rfl

theorem literalCoreProductMap_surjective : Function.Surjective literalCoreProductMap :=
  literalCorePlusEquiv.surjective.comp QuotientGroup.mk_surjective

/-- All and only the five specified central identifications vanish in the actual core. -/
theorem literalCoreProductMap_ker :
    literalCoreProductMap.ker = DihedralCentralProductSix.Delta := by
  ext x
  change literalCorePlusEquiv (QuotientGroup.mk x) = 1 ↔ _
  rw [map_eq_one_iff _ literalCorePlusEquiv.injective, QuotientGroup.eq_one_iff]

/-- Exact central-overlap coordinates for the map into the actual core. -/
theorem literalCoreProductMap_eq_one_iff (x : DihedralCentralProductSix.D) :
    literalCoreProductMap x = 1 ↔
      ∃ v : Fin 5 → DihedralCentralProductSix.Bit,
        x 0 = DihedralCentralProductSix.bit (∏ i, v i) ∧
          ∀ i, x i.succ = DihedralCentralProductSix.bit (v i) := by
  change x ∈ literalCoreProductMap.ker ↔ _
  rw [literalCoreProductMap_ker, DihedralCentralProductSix.mem_Delta_iff]

/-- Six actual dihedral factors inside O₂(C_J₄(a)), with the established embeddings. -/
noncomputable def literalCoreFactor (i : Fin 6) : DihedralGroup 4 →* pCore 2 centralizer :=
  twoCoreEquiv.symm.toMonoidHom.comp
    (normalClosureEquivTwoCore.toMonoidHom.comp
      (DihedralCentralProductSix.factorMap hyperbolicRelations i))

/-- The factor maps are the restrictions of the specified product map. -/
theorem literalCoreProductMap_single (i : Fin 6) (x : DihedralGroup 4) :
    literalCoreProductMap (Pi.mulSingle i x) = literalCoreFactor i x := by
  change twoCoreEquiv.symm (normalClosureEquivTwoCore
    (normalClosurePlusEquiv (QuotientGroup.mk (Pi.mulSingle i x)))) = _
  rw [normalClosurePlusEquiv_mk, DihedralCentralProductSix.phi_single]
  rfl

/-- No nontrivial element of an individual D₈ factor is lost in the central product. -/
theorem literalCoreFactor_injective (i : Fin 6) : Function.Injective (literalCoreFactor i) :=
  twoCoreEquiv.symm.injective.comp
    (normalClosureEquivTwoCore.injective.comp
      (DihedralCentralProductSix.factorMap_injective hyperbolicRelations i))

/-- Different dihedral factors commute elementwise in the actual two-core. -/
theorem literalCoreFactor_commute (i j : Fin 6) (hij : i ≠ j) (x y : DihedralGroup 4) :
    Commute (literalCoreFactor i x) (literalCoreFactor j y) :=
  ((DihedralCentralProductSix.factorMap_commute hyperbolicRelations hij x y).map
    normalClosureEquivTwoCore.toMonoidHom).map twoCoreEquiv.symm.toMonoidHom

theorem literalCoreFactor_r_one (i : Fin 6) :
    literalCoreFactor i (DihedralGroup.r 1) =
      literalCoreLift i false * literalCoreLift i true := by
  rw [← literalCoreProductMap_single, literalCoreProductMap_apply, literalCorePlusEquiv_r_one]

theorem literalCoreFactor_sr_zero (i : Fin 6) :
    literalCoreFactor i (DihedralGroup.sr 0) = literalCoreLift i false := by
  rw [← literalCoreProductMap_single, literalCoreProductMap_apply, literalCorePlusEquiv_sr_zero]

theorem literalCoreFactor_r_two (i : Fin 6) :
    literalCoreFactor i (DihedralGroup.r 2) = literalCoreInvolution := by
  rw [← literalCoreProductMap_single, literalCoreProductMap_apply, literalCorePlusEquiv_r_two]

/-- The factor's second reflection is precisely the second certified lift. -/
theorem literalCoreFactor_sr_one (i : Fin 6) :
    literalCoreFactor i (DihedralGroup.sr 1) = literalCoreLift i true := by
  change twoCoreEquiv.symm (normalClosureEquivTwoCore
    (DihedralCentralProductSix.factorMap hyperbolicRelations i (DihedralGroup.sr 1))) = _
  rw [DihedralCentralProductSix.factorMap_sr_one]
  rfl

end Janko4.InvolutionCentralizers.First.PlusType
