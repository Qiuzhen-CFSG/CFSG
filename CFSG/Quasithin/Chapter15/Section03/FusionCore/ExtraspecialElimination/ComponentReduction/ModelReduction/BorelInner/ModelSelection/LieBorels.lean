module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Transport
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.SpecificGroups.LinearSylowNormalizers
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable

/-!
# Solvable Borels of the whole conjugate-component closure

Regard every T-conjugate star component as an intrinsic subgroup of L₀*.
Their join is the whole closure, each is multiplicatively equivalent to L*,
and distinct factors commute once L* is quasisimple. Multiplication from
the product of these actual factors is therefore surjective.

The Sylow subgroup selected here is exactly the image of T ∩ L₀. It lifts
to a Sylow subgroup of the product, whose entire normalizer maps onto the
required intrinsic normalizer. Central overlaps require no injectivity of
the product map. The commuting-family theorem transports the concrete
factor-normalizer solvability to the whole closure. Finally the solvable
two-core kernel lifts this conclusion to the original relative normalizer.

The concrete calculations cover PSL₂, SL₃, derived Sp₄ and G₂, and binary
PSL₄ and PSL₅ through their actual multiplicative equivalences. In particular,
both derived binary endpoints are retained. Quasisimplicity and the Lie-model
alternative are explicit classification inputs to this conditional result;
the parent model-selection argument must establish them.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.86, 104–105 and 1144, B.4.2, B.5.5(1)(iv), and proof of 15.3.49(k).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.LieBorels

open ModelSelection
universe u

/-- Every actual Lie component model has solvable Sylow two-normalizers,
including the derived binary symplectic and G₂ carriers. -/
theorem model_normalizer_isSolvable {D : Type u} [Group D] [Finite D] {e : ℕ}
    (hmodel : LieComponentModel D e) (S : Sylow 2 D) :
    Group.IsSolvable (normalizer (S : Set D)) := by
  cases hmodel with
  | linear_two he F hF model =>
    obtain ⟨f⟩ := model
    exact Sylow.isSolvable_normalizer_of_surjective f.symm.toMonoidHom f.symm.surjective
      (Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_psl_two_normalizer he hF) S
  | linear_three he F hF model =>
    obtain ⟨f⟩ := model
    exact Sylow.isSolvable_normalizer_of_surjective f.symm.toMonoidHom f.symm.surjective
      (Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sl_three_normalizer he hF) S
  | symplectic he F hF model =>
    obtain ⟨f⟩ := model
    exact Theory.SpecificGroups.SymplecticFour.isSolvable_derived_sylow_normalizer_of_equiv
      hF he f S
  | g2 he F hF model =>
    obtain ⟨f⟩ := model
    exact Sylow.isSolvable_normalizer_of_surjective f.symm.toMonoidHom f.symm.surjective
      (Atlas.G2.DerivedNormalizerSolvable.isSolvable_normalizer_of_card he hF) S
  | binary_linear he n hn model =>
    obtain ⟨f⟩ := model
    exact Sylow.isSolvable_normalizer_of_surjective f.symm.toMonoidHom f.symm.surjective
      (Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_binary_psl_normalizer hn) S

variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

/-- One of all conjugate components, regarded inside the whole star closure. -/
def factor (C : ↥(conjugateFactors H L T)) :
    Subgroup (starImage H (localSpan L T)) := C.val.subgroupOf _

/-- The actual multiplicative comparison with the original component. -/
noncomputable def factorEquiv (C : ↥(conjugateFactors H L T)) :
    starImage H L ≃* factor C :=
  (conjugateFactors_properties d C.val C.property).2.2.2.some.trans
    (subgroupOfEquivOfLe (conjugateFactors_properties d C.val C.property).2.1).symm

include d

/-- The intrinsic factors generate all of L₀*, without an orbit-size assumption. -/
theorem factor_sup : (⨆ C : ↥(conjugateFactors H L T), factor C) = ⊤ := by
  apply map_injective (starImage H (localSpan L T)).subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
  simp_rw [factor, map_subgroupOf_eq_of_le
    (conjugateFactors_properties d _ (Subtype.property _)).2.1]
  rw [← conjugateFactors_sup d, Finset.sup_eq_iSup, iSup_subtype]
  rfl

/-- Quasisimplicity makes distinct intrinsic factors commute. -/
theorem factor_commute (hq : Theory.GroupTheory.IsQuasisimple (starImage H L)) :
    Pairwise fun C D : ↥(conjugateFactors H L T) =>
      factor C ≤ centralizer (factor D : Set (starImage H (localSpan L T))) := by
  intro C D hne x hx y hy
  apply Subtype.ext
  exact conjugateFactors_commute d hq C.val D.val C.property D.property
    (fun h => hne (Subtype.ext h)) hx y.val hy

/-- Every factor retains the same concrete Lie alternative and field exponent. -/
theorem factor_lieModel {e : ℕ} (h : LieComponentModel (starImage H L) e)
    (C : ↥(conjugateFactors H L T)) : LieComponentModel (factor C) e :=
  lieModel_transport (factorEquiv d C) h

/-- A Sylow marking for the actual star image of T ∩ L₀. -/
noncomputable def closureSylow : Sylow 2 (starImage H (localSpan L T)) :=
  (closure_inter_sylow d).2.choose

/-- The marking has exactly the required intrinsic subgroup as carrier. -/
theorem closureSylow_coe :
    (closureSylow d : Subgroup (starImage H (localSpan L T))) =
      (starImage H ((T : Subgroup G) ⊓ localSpan L T)).subgroupOf
        (starImage H (localSpan L T)) := by
  apply map_injective (starImage H (localSpan L T)).subtype_injective
  have hle : starImage H ((T : Subgroup G) ⊓ localSpan L T) ≤
      starImage H (localSpan L T) := map_mono (comap_mono inf_le_right)
  rw [map_subgroupOf_eq_of_le hle]
  exact (closure_inter_sylow d).2.choose_spec

/-- The original relative normalizer is solvable exactly when this Sylow normalizer is. -/
theorem borel_isSolvable_iff_closureSylow :
    Group.IsSolvable (localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) : Subgroup G) ↔
      Group.IsSolvable (normalizer
        (closureSylow d : Set (starImage H (localSpan L T)))) := by
  change _ ↔ Group.IsSolvable (normalizer
    ((closureSylow d : Subgroup (starImage H (localSpan L T))) :
      Set (starImage H (localSpan L T))))
  rw [closureSylow_coe]
  exact borel_isSolvable_iff d

/-- Multiplication of all intrinsic conjugate factors into the star closure. -/
noncomputable def closureProduct
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L)) :
    ((C : ↥(conjugateFactors H L T)) → factor C) →*
      starImage H (localSpan L T) :=
  noncommPiCoprod (fun _ _ hne _x y hx hy =>
    (factor_commute d hq hne hx y hy).symm)

/-- Every element of the star closure is a product of factor elements. -/
theorem closureProduct_surjective
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L)) :
    Function.Surjective (closureProduct d hq) :=
  MonoidHom.range_eq_top.mp (noncommPiCoprod_range.trans (factor_sup d))

/-- A product Sylow lifts the required Sylow and its entire normalizer. -/
theorem exists_sylow_normalizer_lift
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L)) :
    ∃ P : Sylow 2 ((C : ↥(conjugateFactors H L T)) → factor C),
      P.map (closureProduct d hq) = (closureSylow d : Subgroup (starImage H (localSpan L T))) ∧
      (normalizer (P : Set ((C : ↥(conjugateFactors H L T)) → factor C))).map
        (closureProduct d hq) = normalizer (closureSylow d : Set (starImage H (localSpan L T))) := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective (closureProduct_surjective d hq) 2
    (closureSylow d)
  have hm := congrArg (fun S : Sylow 2 (starImage H (localSpan L T)) =>
    (S : Subgroup (starImage H (localSpan L T)))) hP
  change P.map (closureProduct d hq) =
    (closureSylow d : Subgroup (starImage H (localSpan L T))) at hm
  refine ⟨P, hm, ?_⟩
  rw [Sylow.normalizer_map_surjective P _ (closureProduct_surjective d hq), hm,
    Sylow.coe_coe]

/-- All conjugate components contribute their concrete solvable normalizers
to the Sylow normalizer in the whole star closure. -/
theorem closure_normalizer_isSolvable {e : ℕ}
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hmodel : LieComponentModel (starImage H L) e)
    (S : Sylow 2 (starImage H (localSpan L T))) :
    Group.IsSolvable (normalizer (S : Set (starImage H (localSpan L T)))) := by
  exact Sylow.isSolvable_normalizer_of_commuting_family factor
    (factor_commute d hq) (factor_sup d)
    (fun C P => model_normalizer_isSolvable (factor_lieModel d hmodel C) P) S

/-- The Borel needed in 15.3.49(k) is the solvable relative normalizer of
the actual Sylow intersection in L₀ = ⟨L^T⟩. The classification inputs
are discharged by the parent model-selection argument. -/
theorem borel_isSolvable {e : ℕ}
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hmodel : LieComponentModel (starImage H L) e) :
    Group.IsSolvable (localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G) : Subgroup G) :=
  (borel_isSolvable_iff_closureSylow d).mpr
    (closure_normalizer_isSolvable d hq hmodel (closureSylow d))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.LieBorels
