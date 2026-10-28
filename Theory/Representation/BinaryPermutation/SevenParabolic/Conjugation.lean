module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Ordinary
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# Conjugation transport of the ordinary seven-letter geometry

A chart intertwines the literal conjugation action on the whole module
with its seven-letter action and identifies the image of the actual
component with A₇. The orbit identity gives a vector in the actual second
span. Its centralizer has the literal A₆ image, and a specified element of
that image escapes both the first partition and the marked point stabilizer.

Source: Aschbacher--Smith, original14.6.10(5), printed pp.1029--1030.
-/

@[expose] public section
open Subgroup BinaryPermutation
open BinaryPermutation.SevenParabolic
namespace BinaryPermutation.SevenParabolic.Ordinary
variable {G : Type*} [Group G]
/-- A compatible whole-module conjugation chart, before any parabolic marking. -/
structure Chart (J C W : Subgroup G) where
  moduleEquiv : W ≃* Multiplicative Space
  actor : J →* Equiv.Perm (Fin 7)
  normalized : J ≤ normalizer (W : Set G)
  equivariant : ∀ j : J, ∀ w : W,
    (moduleEquiv ⟨j.val * w.val * j.val⁻¹,
      le_normalizer_iff.mp normalized j j.property w w.property⟩).toAdd =
      action (actor j) (moduleEquiv w).toAdd
  component_image : (C.subgroupOf J).map actor = alternatingGroup (Fin 7)

namespace Chart
variable {J C W : Subgroup G} (c : Chart J C W)
noncomputable def lift (v : Space) : W := c.moduleEquiv.symm (Multiplicative.ofAdd v)
@[simp] theorem coordinate_lift (v : Space) :
    (c.moduleEquiv (c.lift v)).toAdd = v := c.moduleEquiv.apply_symm_apply _
theorem lift_add (v w : Space) : c.lift (v+w) = c.lift v * c.lift w :=
  c.moduleEquiv.symm.map_mul _ _
theorem lift_ne_one {v : Space} (hv : v ≠ 0) : (c.lift v : G) ≠ 1 := by
  intro h
  have he : c.lift v = 1 := Subtype.ext h
  have hh := c.coordinate_lift v
  rw [he,map_one] at hh
  exact hv hh.symm

theorem lift_action (j : J) (v : Space) :
    (c.lift (action (c.actor j) v) : G) = j.val * (c.lift v : G) * j.val⁻¹ := by
  have he := c.equivariant j (c.lift v)
  rw [c.coordinate_lift] at he
  have hh : (⟨j.val * (c.lift v : G) * j.val⁻¹,
      le_normalizer_iff.mp c.normalized j j.property (c.lift v) (c.lift v).property⟩ : W) =
      c.lift (action (c.actor j) v) := by
    apply c.moduleEquiv.injective
    apply Multiplicative.toAdd.injective
    rw [he,c.coordinate_lift]
  exact (congrArg Subtype.val hh).symm

theorem centralizes_lift_iff (j : J) (v : Space) :
    j.val ∈ centralizer ({(c.lift v : G)} : Set G) ↔ action (c.actor j) v = v := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he : (c.lift (action (c.actor j) v) : G) = (c.lift v : G) := by
      rw [c.lift_action,h,mul_inv_cancel_right]
    have hh := congrArg (fun w : W => (c.moduleEquiv w).toAdd) (Subtype.ext he)
    simpa only [c.coordinate_lift] using hh
  · intro h
    have he := c.lift_action j v
    rw [h] at he
    have hh := congrArg (fun w : G => w * j.val) he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh.symm
end Chart
end BinaryPermutation.SevenParabolic.Ordinary
namespace BinaryPermutation.SevenParabolic.Ordinary.Chart
open Subgroup
variable {G : Type*} [Group G] {J C W : Subgroup G} (c : Chart J C W)
/-- The three-term orbit identity is transported into the actual generated subgroup. -/
theorem sixSupport_mem_span (V P : Subgroup G)
    (hz : (c.lift firstFour : G) ∈ V) (hw : (c.lift secondFour : G) ∈ V)
    (hc : complementCycle ∈ (P.subgroupOf J).map c.actor) :
    (c.lift firstSix : G) ∈ conjugateSpanBy V P := by
  obtain ⟨g,hg,hgc⟩ := hc
  have h1 : (c.lift (action complementCycle secondFour) : G) ∈ conjugateSpanBy V P := by
    rw [←hgc,c.lift_action]
    exact subset_closure ⟨g.val,hg,(c.lift secondFour : G),hw,rfl⟩
  have h2 : (c.lift (action (complementCycle ^ 2) secondFour) : G) ∈ conjugateSpanBy V P := by
    rw [←hgc,←map_pow,c.lift_action]
    exact subset_closure ⟨g.val ^ 2,P.pow_mem hg 2,(c.lift secondFour : G),hw,rfl⟩
  rw [firstSix_expression,c.lift_add,c.lift_add]
  exact (conjugateSpanBy V P).mul_mem
    ((conjugateSpanBy V P).mul_mem (le_conjugateSpanBy V P hz) h1) h2

/-- Fixation comes from the first parabolic's partition; no fixation by J is used. -/
theorem sixSupport_fixed (R : Subgroup G) (hRJ : R ≤ J)
    (hR : (R.subgroupOf J).map c.actor ≤ lambda) :
    R ≤ centralizer ({(c.lift firstSix : G)} : Set G) := by
  intro r hr
  exact (c.centralizes_lift_iff ⟨r,hRJ hr⟩ firstSix).mpr
    (lambda_fixes_firstSix _ (hR (mem_map_of_mem c.actor hr)))

/-- Centralizers are transported through the actual component image, not
through an abstract copy of A₇. -/
theorem centralizer_image (v : Space) :
    ((C ⊓ centralizer ({(c.lift v : G)} : Set G)).subgroupOf J).map c.actor =
      alternatingGroup (Fin 7) ⊓ pointStabilizer v := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    refine ⟨?_,(c.centralizes_lift_iff g v).mp hg.2⟩
    rw [←c.component_image]
    exact mem_map_of_mem c.actor hg.1
  · intro g hg
    have hh : g ∈ (C.subgroupOf J).map c.actor := c.component_image ▸ hg.1
    obtain ⟨j,hj,rfl⟩ := hh
    exact mem_map_of_mem c.actor ⟨hj,(c.centralizes_lift_iff j v).mpr hg.2⟩

/-- The actual component centralizer has the A₆ image used at the source step. -/
noncomputable def sixSupportCentralizerImageEquiv :
    (((C ⊓ centralizer ({(c.lift firstSix : G)} : Set G)).subgroupOf J).map c.actor) ≃*
      alternatingGroup (Fin 6) :=
  (MulEquiv.subgroupCongr (c.centralizer_image firstSix)).trans sixSupportCentralizerEquiv

/-- An element of that same A₆ image escapes both original marked intersections. -/
theorem sixSupport_escapes (M Mc : Subgroup G)
    (hM : ((J ⊓ M).subgroupOf J).map c.actor ≤ lambda)
    (hMc : ((J ⊓ Mc).subgroupOf J).map c.actor ≤ pointStabilizer firstFour) :
    ¬ C ⊓ centralizer ({(c.lift firstSix : G)} : Set G) ≤ M ∧
    ¬ C ⊓ centralizer ({(c.lift firstSix : G)} : Set G) ≤ Mc := by
  have hm : escapingCycle ∈
      ((C ⊓ centralizer ({(c.lift firstSix : G)} : Set G)).subgroupOf J).map c.actor := by
    rw [c.centralizer_image]
    exact ⟨escapingCycle_even,escapingCycle_fixes⟩
  obtain ⟨j,hj,hje⟩ := hm
  constructor
  · intro h
    apply escapingCycle_not_lambda
    rw [←hje]
    exact hM (mem_map_of_mem c.actor ⟨j.property,h hj⟩)
  · intro h
    apply escapingCycle_moves
    have hh := hMc (mem_map_of_mem c.actor (show j ∈ (J ⊓ Mc).subgroupOf J from ⟨j.property,h hj⟩))
    change action (c.actor j) firstFour = firstFour at hh
    rwa [hje] at hh
end BinaryPermutation.SevenParabolic.Ordinary.Chart
