module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Positive
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Matrix
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The explicit C₂ presentation and its positive-subgroup faithfulness

The presented group uses only additivity and the chamber commuting/crossing
relations. Its universal property constructs an onto map to any generating
root system. In particular evaluation maps onto the existing matrix Sp₄.
Positive collection and concrete matrix coordinates prove that evaluation
is injective on the positive subgroup and has image exactly the full U.
Global evaluation injectivity is not asserted: the opposite-root Weyl and
torus relations and the Bruhat argument still have to be proved.

Source: Steinberg §6, Theorems 8–9 and Lemma 36, printed pp.68–74.
-/

@[expose] public section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootPresentation
variable {F E : Type*} [Field F] [Group E]

open scoped commutatorElement

/-- Only additive and chamber Chevalley relations are imposed. -/
inductive Relator : FreeGroup (Fin 8 × F) → Prop
  | add (r : Fin 8) (s t : F) : Relator
      (FreeGroup.of (r,s) * FreeGroup.of (r,t) * (FreeGroup.of (r,s+t))⁻¹)
  | commuting (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ weyl) (i : Fin 5) (s t : F) :
      Relator ⁅FreeGroup.of (σ (commutingPairs i).1,s),
        FreeGroup.of (σ (commutingPairs i).2,t)⁆
  | crossing (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ weyl) (v c : F) :
      Relator (FreeGroup.of (σ 2,v) * FreeGroup.of (σ 6,c) *
        (FreeGroup.of (σ 6,c) * FreeGroup.of (σ 0,c^2*v) *
          FreeGroup.of (σ 4,c*v) * FreeGroup.of (σ 2,v))⁻¹)

/-- The C₂ Steinberg group defined by the explicit characteristic-two schema. -/
abbrev SteinbergGroup (F : Type*) [Field F] :=
  PresentedGroup {w : FreeGroup (Fin 8 × F) | Relator w}

def generator (r : Fin 8) (t : F) : SteinbergGroup F := PresentedGroup.of (r,t)

theorem generator_relations : Relations (generator (F := F)) := by
  intro σ hσ
  refine {add := ?_, commuting := ?_, crossing := ?_}
  · intro r s t
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.add (σ r) s t))
  · intro i s t
    apply commutatorElement_eq_one_iff_commute.mp
    simpa only [map_commutatorElement, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.commuting σ hσ i s t))
  · intro v c
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv, generator, PresentedGroup.of] using
      (PresentedGroup.one_of_mem (rels := {w | Relator w}) (Relator.crossing σ hσ v c))

theorem Relations.eval_relator {x : Fin 8 → F → E} (h : Relations x)
    {w : FreeGroup (Fin 8 × F)} (hw : Relator w) :
    FreeGroup.lift (fun p => x p.1 p.2) w = 1 := by
  cases hw with
  | add r s t => simp [h.positive.add r s t]
  | commuting σ hσ i s t =>
    simpa only [map_commutatorElement, FreeGroup.lift_apply_of] using
      ((h σ hσ).commuting i s t).commutator_eq
  | crossing σ hσ v c => simp [(h σ hσ).crossing v c]

/-- The universal map of the literal relator presentation. -/
def lift {x : Fin 8 → F → E} (h : Relations x) : SteinbergGroup F →* E :=
  PresentedGroup.toGroup (fun _ hw => h.eval_relator hw)

@[simp] theorem lift_generator {x : Fin 8 → F → E} (h : Relations x) (r : Fin 8) (t : F) :
    lift h (generator r t) = x r t := PresentedGroup.toGroup.of _

theorem lift_unique {x : Fin 8 → F → E} (h : Relations x) (f : SteinbergGroup F →* E)
    (hf : ∀ r t, f (generator r t) = x r t) : f = lift h := by
  apply PresentedGroup.ext
  rintro ⟨r,t⟩
  exact (hf r t).trans (lift_generator h r t).symm

/-- Generation in the target makes the universal map surjective. -/
theorem lift_surjective {x : Fin 8 → F → E} (h : Relations x)
    (hgen : closure {g | ∃ r t, x r t = g} = ⊤) : Function.Surjective (lift h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (closure_le _).mpr
  rintro _ ⟨r,t,rfl⟩
  exact ⟨generator r t,lift_generator h r t⟩

variable [CharP F 2]

/-- Evaluation in the existing concrete matrix group. Faithfulness is separate. -/
def matrixMap : SteinbergGroup F →* Sp F := lift matrix_relations

@[simp] theorem matrixMap_generator (r : Fin 8) (t : F) :
    matrixMap (generator r t) = rootElement r t := lift_generator _ _ _

theorem matrixMap_surjective : Function.Surjective (matrixMap (F := F)) := by
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_rootElement_mem
  intro r t
  exact ⟨generator r t, matrixMap_generator r t⟩

/-- The canonical additive maps are injective even before global faithfulness
is proved: the matrix entry already separates their parameters. -/
theorem generator_injective (r : Fin 8) : Function.Injective (generator (F := F) r) := by
  intro s t h
  exact RootSubgroup.element_injective r (by simpa using congrArg matrixMap h)

open PositiveRelations

/-- The ordered four-root words already have unique parameters in the
presentation; this uses only separation by the concrete matrix coordinates. -/
theorem positive_product_injective : Function.Injective (fun p : F × F × F × F =>
    product generator p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  intro p q h
  have hm := congrArg matrixMap h
  simp only [product, map_mul, matrixMap_generator] at hm
  have he : CentralRootGeometry.element p.1 (p.2.1+p.1*p.2.2.1) p.2.2.1 p.2.2.2 =
      CentralRootGeometry.element q.1 (q.2.1+q.1*q.2.2.1) q.2.2.1 q.2.2.2 := by
    apply Subtype.ext
    simpa only [CentralRootGeometry.element, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      using hm
  have hcoords := (CentralRootGeometry.element_eq_iff _ _ _ _ _ _ _ _).mp he
  have hk : p.2.1 = q.2.1 := by
    have h' := hcoords.2.1
    rw [hcoords.1, hcoords.2.2.1] at h'
    exact add_right_cancel h'
  exact Prod.ext hcoords.1 (Prod.ext hk (Prod.ext hcoords.2.2.1 hcoords.2.2.2))

variable [Finite F]

/-- Positive roots in the presentation have no matrix kernel. -/
theorem matrixMap_injective_on_positive : Set.InjOn (matrixMap (F := F))
    (positiveSubgroup (generator (F := F)) : Set (SteinbergGroup F)) := by
  intro g hg k hk he
  obtain ⟨b,c,d,e,rfl⟩ := generator_relations.positive.positive_normal_form g hg
  obtain ⟨u,v,w,z,rfl⟩ := generator_relations.positive.positive_normal_form k hk
  have hs : CentralRootGeometry.element b (c+b*d) d e =
      CentralRootGeometry.element u (v+u*w) w z := by
    apply Subtype.ext
    simpa only [product, map_mul, matrixMap_generator, CentralRootGeometry.element,
      add_assoc, CharTwo.add_self_eq_zero, add_zero] using he
  obtain ⟨rfl,hc,rfl,rfl⟩ := (CentralRootGeometry.element_eq_iff _ _ _ _ _ _ _ _).mp hs
  have hv := add_right_cancel hc
  subst v
  rfl

/-- The matrix image of the positive subgroup is the full concrete U. -/
theorem matrixMap_positive : (positiveSubgroup (generator (F := F))).map matrixMap =
    unipotent (F := F) := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    obtain ⟨b,k,w,v,rfl⟩ := generator_relations.positive.positive_normal_form g hg
    simp only [product, map_mul, matrixMap_generator]
    exact mul_mem (mul_mem (mul_mem (positive_root_mem_unipotent 6 b (by simp))
      (positive_root_mem_unipotent 0 k (by simp)))
      (positive_root_mem_unipotent 4 w (by simp)))
      (positive_root_mem_unipotent 2 v (by simp))
  · intro g hg
    obtain ⟨⟨b,u,w,v⟩,he⟩ := CentralRootGeometry.element_surjective ⟨g,hg⟩
    refine ⟨product generator b (u+b*w) w v, ?_, ?_⟩
    · have hr (r : Fin 8) (t : F) (hr : r ∈ ({6,0,4,2} : Set (Fin 8))) :
          generator r t ∈ positiveSubgroup (generator (F := F)) := subset_closure ⟨r,hr,t,rfl⟩
      exact mul_mem (mul_mem (mul_mem (hr 6 b (by simp))
        (hr 0 _ (by simp))) (hr 4 w (by simp))) (hr 2 v (by simp))
    · simpa only [product, map_mul, matrixMap_generator, CentralRootGeometry.element]
        using congrArg Subtype.val he

end Theory.SpecificGroups.SymplecticFour.RootPresentation
