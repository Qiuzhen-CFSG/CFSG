module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualDihedralModel
public import Theory.GroupTheory.SpecificGroups.SymmetricFourProductResidualCore

/-!
# The two marked four-groups in the residual dihedral model

The point and plane Klein four-groups generate D8 and cover its involutions.
The canonical normal Klein four of S4 maps to them with the exact generator
marks used by the two endpoint matrix representations. Consequently equality
on those two generators identifies the literal endpoint subgroup images.
Source: Aschbacher--Smith F.5.5, printed pp.301--302.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.ResidualJoinModel
open Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
local notation "D8" => DihedralGroup 4
local notation "S4" => Equiv.Perm (Fin 4)

/-- The Klein four containing the point generator. -/
def pointFour : Subgroup D8 where
  carrier := {x | x=1 ∨ x=.r 2 ∨ x=.sr 0 ∨ x=.sr 2}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

/-- The Klein four containing the plane generator. -/
def planeFour : Subgroup D8 where
  carrier := {x | x=1 ∨ x=.r 2 ∨ x=.sr 1 ∨ x=.sr 3}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

instance : DecidablePred (· ∈ pointFour) := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
instance : DecidablePred (· ∈ planeFour) := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

private theorem eq_closure_pair {X : Type*} [Group X] (K : Subgroup X) (a b : X)
    (ha : a∈K) (hb : b∈K) (hc : ∀x∈K, x=1 ∨ x=a ∨ x=b ∨ x=a*b) :
    K=closure ({a,b} : Set X) := by
  apply le_antisymm
  · intro x hx
    have ha' : a∈closure ({a,b} : Set X) := subset_closure (by simp)
    have hb' : b∈closure ({a,b} : Set X) := subset_closure (by simp)
    rcases hc x hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ha'
    · exact hb'
    · exact mul_mem ha' hb'
  · apply (closure_le K).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ha
    · exact Set.mem_singleton_iff.mp hx ▸ hb

/-- The two standard double transpositions generate the canonical S4 core. -/
theorem core_eq_closure : core=closure ({doubleSwap 0,doubleSwap 1} : Set S4) := by
  apply eq_closure_pair
  · change quotientHom (doubleSwap 0)=1
    decide +kernel
  · change quotientHom (doubleSwap 1)=1
    decide +kernel
  · exact (by decide +kernel : ∀x:S4, x∈core →
      x=1 ∨ x=doubleSwap 0 ∨ x=doubleSwap 1 ∨ x=doubleSwap 0*doubleSwap 1)

/-- The point core generator markings determine its image. -/
theorem pointFour_eq_closure : pointFour=closure ({.sr 0,.sr 2} : Set D8) := by
  apply eq_closure_pair
  · decide +kernel
  · decide +kernel
  · exact (by decide +kernel : ∀x:D8, x∈pointFour →
      x=1 ∨ x=.sr 0 ∨ x=.sr 2 ∨ x=(.sr 0 : D8)*.sr 2)

/-- The plane core generator markings determine its image. -/
theorem planeFour_eq_closure : planeFour=closure ({.r 2,.sr 1} : Set D8) := by
  apply eq_closure_pair
  · decide +kernel
  · decide +kernel
  · exact (by decide +kernel : ∀x:D8, x∈planeFour →
      x=1 ∨ x=.r 2 ∨ x=.sr 1 ∨ x=(.r 2 : D8)*.sr 1)

/-- The marked canonical S4 core map into the point four-group. -/
def pointCoreHom : core →* D8 where
  toFun x := if x.val=1 then 1 else if x.val=doubleSwap 0 then .sr 0 else if x.val=doubleSwap 1 then .sr 2 else .r 2
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- The marked canonical S4 core map into the plane four-group. -/
def planeCoreHom : core →* D8 where
  toFun x := if x.val=1 then 1 else if x.val=doubleSwap 0 then .r 2 else if x.val=doubleSwap 1 then .sr 1 else .sr 3
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem pointCoreHom_injective : Function.Injective pointCoreHom := by decide +kernel
theorem planeCoreHom_injective : Function.Injective planeCoreHom := by decide +kernel

theorem pointCoreHom_range : pointCoreHom.range=pointFour := by
  ext x
  change (∃y,pointCoreHom y=x) ↔ x∈pointFour
  revert x
  decide +kernel

theorem planeCoreHom_range : planeCoreHom.range=planeFour := by
  ext x
  change (∃y,planeCoreHom y=x) ↔ x∈planeFour
  revert x
  decide +kernel

theorem pointCoreHom_marks : ∀ x:core,
    (x.val=doubleSwap 0 → pointCoreHom x=.sr 0) ∧
    (x.val=doubleSwap 1 → pointCoreHom x=.sr 2) := by decide +kernel

theorem planeCoreHom_marks : ∀ x:core,
    (x.val=doubleSwap 0 → planeCoreHom x=.r 2) ∧
    (x.val=doubleSwap 1 → planeCoreHom x=.sr 1) := by decide +kernel

/-- The canonical S4 core with the marked point embedding. -/
noncomputable def pointCoreEquiv : core ≃* pointFour :=
  (MonoidHom.ofInjective pointCoreHom_injective).trans (MulEquiv.subgroupCongr pointCoreHom_range)

/-- The canonical S4 core with the marked plane embedding. -/
noncomputable def planeCoreEquiv : core ≃* planeFour :=
  (MonoidHom.ofInjective planeCoreHom_injective).trans (MulEquiv.subgroupCongr planeCoreHom_range)

theorem pointCoreEquiv_apply (x : core) : (pointCoreEquiv x).val=pointCoreHom x := rfl
theorem planeCoreEquiv_apply (x : core) : (planeCoreEquiv x).val=planeCoreHom x := rfl

/-- Both four-groups contain the same nonidentity central involution. -/
theorem common_center_mem : (.r 2 : D8)∈pointFour ∧ (.r 2 : D8)∈planeFour ∧ (.r 2 : D8)≠1 := by
  decide +kernel

/-- Every involution of the residual dihedral model lies in one of its cores. -/
theorem involution_mem_four : ∀x:D8, x^2=1 → x∈pointFour ∨ x∈planeFour := by decide +kernel

/-- The two endpoint four-groups generate the entire residual dihedral model. -/
theorem four_sup_eq_top : pointFour ⊔ planeFour=⊤ := by
  apply top_unique
  intro x _
  have ha : (.sr 0 : D8)∈pointFour ⊔ planeFour  := (le_sup_left : pointFour ≤ pointFour ⊔ planeFour) (by decide +kernel : (.sr 0 : D8)∈pointFour)
  have hb : (.sr 1 : D8)∈pointFour ⊔ planeFour  := (le_sup_right : planeFour ≤ pointFour ⊔ planeFour) (by decide +kernel : (.sr 1 : D8)∈planeFour)
  have hc := (by decide +kernel : ∀x:D8, x∈pointFour ∨ x∈planeFour ∨
      x=(.sr 0 : D8)*.sr 1 ∨ x=(.sr 1 : D8)*.sr 0) x
  rcases hc with h | h | rfl | rfl
  · exact (le_sup_left : pointFour ≤ pointFour ⊔ planeFour) h
  · exact (le_sup_right : planeFour ≤ pointFour ⊔ planeFour) h
  · exact mul_mem ha hb
  · exact mul_mem hb ha

/-- Literal source point images agree once the two endpoint generator marks agree. -/
theorem core_map_eq_pointFour_map {G : Type*} [Group G] (f : S4 →* G) (g : D8 →* G)
    (h0 : f (doubleSwap 0)=g (.sr 0)) (h1 : f (doubleSwap 1)=g (.sr 2)) :
    core.map f=pointFour.map g := by
  rw [core_eq_closure,pointFour_eq_closure,MonoidHom.map_closure,MonoidHom.map_closure]
  simp only [Set.image_insert_eq,Set.image_singleton,h0,h1]

/-- Literal source plane images agree once the two endpoint generator marks agree. -/
theorem core_map_eq_planeFour_map {G : Type*} [Group G] (f : S4 →* G) (g : D8 →* G)
    (h0 : f (doubleSwap 0)=g (.r 2)) (h1 : f (doubleSwap 1)=g (.sr 1)) :
    core.map f=planeFour.map g := by
  rw [core_eq_closure,planeFour_eq_closure,MonoidHom.map_closure,MonoidHom.map_closure]
  simp only [Set.image_insert_eq,Set.image_singleton,h0,h1]

/-- The two literal source core images generate exactly the dihedral image. -/
theorem four_map_sup_eq_range {G : Type*} [Group G] (g : D8 →* G) :
    pointFour.map g ⊔ planeFour.map g=g.range := by
  rw [←Subgroup.map_sup,four_sup_eq_top,←MonoidHom.range_eq_map]

/-- The four endpoint generator equalities identify the whole source join. -/
theorem core_maps_sup_eq_range {G : Type*} [Group G]
    (p q : S4 →* G) (g : D8 →* G)
    (hp0 : p (doubleSwap 0)=g (.sr 0)) (hp1 : p (doubleSwap 1)=g (.sr 2))
    (hq0 : q (doubleSwap 0)=g (.r 2)) (hq1 : q (doubleSwap 1)=g (.sr 1)) :
    core.map p ⊔ core.map q=g.range := by
  rw [core_map_eq_pointFour_map p g hp0 hp1,core_map_eq_planeFour_map q g hq0 hq1]
  exact four_map_sup_eq_range g

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.ResidualJoinModel
