module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecomposition
public import Theory.Representation.FirstCohomologyAutomorphism.Cocycle
public import Theory.Representation.BinaryAlternatingCoreFixedCocycles

/-!
# The literal displacement cocycles in the A₈ point span

Once the FF classification bounds [W,L] by V, each x in E normalizes L
and its displacement in V descends through the original map L/O₂(L) → A₈.
Reducedness supplies the required pointwise fixation of the quotient kernel.
The cocycle vanishes on the literal image of L ∩ C_T(v).

The last theorem assembles the corrected subgroup decomposition from
point-fixed principal vectors. Its correction premise is a remaining
permutation-module calculation, not an additional source hypothesis.
Source: Aschbacher--Smith 12.2.16, printed p.800; B.2.13, printed p.78.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.OneCohomology Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
namespace AlternatingEightFusion
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable (C : AlternatingEightFusion T L V)

/-- The original two-core projection followed by the supplied A₈ marking. -/
def componentProjection : L →* alternatingGroup (Fin 8) :=
  C.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem componentProjection_surjective : Function.Surjective C.componentProjection :=
  C.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))

/-- The actor on which each point displacement vanishes, retaining both inclusions. -/
abbrev pointComponentImage : Subgroup (alternatingGroup (Fin 8)) :=
  (C.pointSylow.subgroupOf L).map C.componentProjection

/-- Construct the cocycle on the actual quotient and keep its ambient evaluation formula. -/
theorem point_displacement_cocycle (D : ChosenModule T L V) (R : C.PointSpanModule)
    (hm : ⁅C.pointSpan, L⁆ ≤ V) {x : G} (hx : x ∈ omegaCenterIn C.pointSylow) :
    ∃ f : cocycles (BinaryPermutation.alternatingCoreRepresentation (Fin 8)),
      (∀ l : L, ((C.vectorEquiv.symm (Multiplicative.ofAdd
        (f.val (C.componentProjection l)))) : G) = x * l * x⁻¹ * (l : G)⁻¹) ∧
      (∀ a ∈ C.pointComponentImage, f.val a = 0) := by
  have hxW : x ∈ C.pointSpan := le_componentOrbit _ _ hx
  have hn : C.pointSpan ≤ normalizer (L : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hm.trans D.le_component)
  let α : MulAut L := L.normalizerMonoidHom ⟨x, hn hxW⟩
  let N := V.subgroupOf L
  let e : N ≃* Multiplicative (BinaryPermutation.core (Fin 8)) :=
    (subgroupOfEquivOfLe D.le_component).trans C.vectorEquiv
  have he (l : L) (w : BinaryPermutation.core (Fin 8)) :
      (e.symm (Multiplicative.ofAdd
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
          (C.componentProjection l) w)) : L) =
        l * (e.symm (Multiplicative.ofAdd w) : L) * l⁻¹ := by
    apply Subtype.ext
    change ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) w))) : G) =
      (l : G) * (C.vectorEquiv.symm (Multiplicative.ofAdd w) : G) * (l : G)⁻¹
    simpa only [C.vectorEquiv.apply_symm_apply, toAdd_ofAdd] using
      C.intertwines l (C.vectorEquiv.symm (Multiplicative.ofAdd w))
  have hd (l : L) : α l * l⁻¹ ∈ N :=
    hm (commutator_mem_commutator hxW l.property)
  have hk (l : L) (hl : l ∈ C.componentProjection.ker) : α l = l := by
    have hlq : QuotientGroup.mk' (pCore 2 L) l = 1 := by
      apply C.groupEquiv.injective
      exact (show C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 from hl).trans
        C.groupEquiv.map_one.symm
    have hlc := C.componentCore_centralizes_pointSpan D R
      (mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff l).mp hlq)) x hxW
    change x * (l : G) = (l : G) * x at hlc
    apply Subtype.ext
    change x * (l : G) * x⁻¹ = l
    rw [hlc, mul_inv_cancel_right]
  obtain ⟨f, hf⟩ := exists_automorphism_cocycle_of_subkernel N C.componentProjection
    C.componentProjection_surjective e
    (BinaryPermutation.alternatingCoreRepresentation (Fin 8)) he α hd hk
  have hfe (l : L) : ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (f.val (C.componentProjection l)))) : G) = x * l * x⁻¹ * (l : G)⁻¹ := by
    rw [hf]
    exact congrArg (fun n : N => ((n : L) : G)) (e.symm_apply_apply ⟨α l * l⁻¹, hd l⟩)
  refine ⟨f, hfe, ?_⟩
  rintro a ⟨l, hl, rfl⟩
  have hc := ((mem_omegaCenterIn_iff _ _).mp hx).2.1 l hl
  have hz : x * (l : G) * x⁻¹ * (l : G)⁻¹ = 1 := by
    rw [← hc, mul_inv_cancel_right, mul_inv_cancel]
  have hh := (hfe l).trans hz
  have hh' : C.vectorEquiv.symm (Multiplicative.ofAdd
      (f.val (C.componentProjection l))) = 1 := Subtype.ext hh
  have hh'' := congrArg (fun w : V => (C.vectorEquiv w).toAdd) hh'
  simpa only [C.vectorEquiv.apply_symm_apply, toAdd_ofAdd, map_one, toAdd_one] using hh''

/-- The general augmentation test applied to the literal point-displacement cocycle. -/
theorem point_displacement_principal_of_fixed_le_core
    (D : ChosenModule T L V) (R : C.PointSpanModule)
    (hm : ⁅C.pointSpan, L⁆ ≤ V)
    (hP : fixedSpace (BinaryPermutation.alternatingRepresentation (Fin 8))
      C.pointComponentImage ≤ BinaryPermutation.core (Fin 8))
    {x : G} (hx : x ∈ omegaCenterIn C.pointSylow) :
    ∃ w : BinaryPermutation.core (Fin 8),
      w ∈ fixedSpace (BinaryPermutation.alternatingCoreRepresentation (Fin 8))
        C.pointComponentImage ∧
      ∀ l : L, ((C.vectorEquiv.symm (Multiplicative.ofAdd
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
          (C.componentProjection l) w - w))) : G) = x * l * x⁻¹ * (l : G)⁻¹ := by
  obtain ⟨f, hf, hz⟩ := C.point_displacement_cocycle D R hm hx
  obtain ⟨w, hw, he⟩ := BinaryPermutation.core_cocycle_principal_of_fixed_le_core
    (by simp) C.pointComponentImage hP f hz
  refine ⟨w, hw, ?_⟩
  intro l
  have hh := congrArg (fun c : cocycles (BinaryPermutation.alternatingCoreRepresentation
    (Fin 8)) => c.val (C.componentProjection l)) he
  exact (congrArg (fun v => ((C.vectorEquiv.symm (Multiplicative.ofAdd v)) : G)) hh).trans
    (hf l)

/-- The two point-fixed-space calculations provide the actual correction in U. -/
theorem point_cocycle_correction_of_fixed_spaces
    (hP : fixedSpace (BinaryPermutation.alternatingRepresentation (Fin 8))
      C.pointComponentImage ≤ BinaryPermutation.core (Fin 8))
    (hfixed : V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore)
    {x : G} (hx : x ∈ omegaCenterIn C.pointSylow)
    (f : cocycles (BinaryPermutation.alternatingCoreRepresentation (Fin 8)))
    (hf : ∀ l : L, ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (f.val (C.componentProjection l)))) : G) = x * l * x⁻¹ * (l : G)⁻¹) :
    ∃ w : V, (w : G) ∈ C.pointCore ∧
      principal (BinaryPermutation.alternatingCoreRepresentation (Fin 8))
        (C.vectorEquiv w).toAdd = f := by
  have hz : ∀ a ∈ C.pointComponentImage, f.val a = 0 := by
    rintro a ⟨l, hl, rfl⟩
    have hc := ((mem_omegaCenterIn_iff _ _).mp hx).2.1 l hl
    have he := hf l
    rw [← hc, mul_inv_cancel_right, mul_inv_cancel] at he
    have he' : C.vectorEquiv.symm (Multiplicative.ofAdd
        (f.val (C.componentProjection l))) = 1 := Subtype.ext he
    simpa only [C.vectorEquiv.apply_symm_apply, toAdd_ofAdd, map_one, toAdd_one] using
      congrArg (fun w : V => (C.vectorEquiv w).toAdd) he'
  obtain ⟨w, hw, he⟩ := BinaryPermutation.core_cocycle_principal_of_fixed_le_core
    (by simp) C.pointComponentImage hP f hz
  let v : V := C.vectorEquiv.symm (Multiplicative.ofAdd w)
  have hv : (v : G) ∈ C.pointCore := by
    apply hfixed
    refine ⟨v.property, ?_⟩
    rintro l ⟨hlL, hlP⟩
    have hh := hw ⟨C.componentProjection ⟨l, hlL⟩,
      mem_map_of_mem _ (show (⟨l, hlL⟩ : L) ∈ C.pointSylow.subgroupOf L from hlP)⟩
    have hi := C.intertwines (⟨l, hlL⟩ : L) v
    simp only [v, C.vectorEquiv.apply_symm_apply, toAdd_ofAdd] at hi
    change BinaryPermutation.alternatingCoreRepresentation (Fin 8)
      (C.componentProjection ⟨l, hlL⟩) w = w at hh
    change BinaryPermutation.alternatingCoreRepresentation (Fin 8)
      (C.groupEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hlL⟩)) w = w at hh
    rw [hh] at hi
    exact mul_inv_eq_iff_eq_mul.mp hi.symm
  refine ⟨v, hv, ?_⟩
  simpa only [v, C.vectorEquiv.apply_symm_apply, toAdd_ofAdd] using he

/-- Assembly from the moved-space bound and point-fixed principal corrections.
Both premises are intermediate mathematical obligations, not source hypotheses. -/
theorem pointFixed_decomposition_of_cocycle_corrections
    (D : ChosenModule T L V) (R : C.PointSpanModule)
    (hm : ⁅C.pointSpan, L⁆ ≤ V)
    (correction : ∀ (x : G), x ∈ omegaCenterIn C.pointSylow →
      ∀ f : cocycles (BinaryPermutation.alternatingCoreRepresentation (Fin 8)),
      (∀ l : L, ((C.vectorEquiv.symm (Multiplicative.ofAdd
        (f.val (C.componentProjection l)))) : G) = x * l * x⁻¹ * (l : G)⁻¹) →
      ∃ w : V, (w : G) ∈ C.pointCore ∧
        principal (BinaryPermutation.alternatingCoreRepresentation (Fin 8))
          (C.vectorEquiv w).toAdd = f) :
    omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed := by
  apply le_antisymm _ (sup_le (C.pointCore_le_omega D) inf_le_left)
  intro x hx
  obtain ⟨f, hf, _⟩ := C.point_displacement_cocycle D R hm hx
  obtain ⟨w, hw, he⟩ := correction x hx f hf
  have hz : (w : G) * x ∈ C.pointFixed := by
    refine ⟨(omegaCenterIn C.pointSylow).mul_mem (C.pointCore_le_omega D hw) hx, ?_⟩
    intro l hl
    have hh := hf ⟨l, hl⟩
    rw [← he] at hh
    change ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (C.componentProjection ⟨l, hl⟩) (C.vectorEquiv w).toAdd -
          (C.vectorEquiv w).toAdd))) : G) = x * l * x⁻¹ * l⁻¹ at hh
    rw [sub_eq_add_neg] at hh
    change ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (C.componentProjection ⟨l, hl⟩) (C.vectorEquiv w).toAdd) *
          (C.vectorEquiv w)⁻¹)) : G) = x * l * x⁻¹ * l⁻¹ at hh
    rw [map_mul, map_inv, C.vectorEquiv.symm_apply_apply] at hh
    change ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (C.componentProjection ⟨l, hl⟩) (C.vectorEquiv w).toAdd))) : G) *
          (w : G)⁻¹ = x * l * x⁻¹ * l⁻¹ at hh
    have hi := C.intertwines (⟨l, hl⟩ : L) w
    change ((C.vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (C.componentProjection ⟨l, hl⟩) (C.vectorEquiv w).toAdd))) : G) =
      l * w * l⁻¹ at hi
    rw [hi] at hh
    calc
      l * ((w : G) * x) = (l * w * l⁻¹ * (w : G)⁻¹) * w * l * x := by group
      _ = (x * l * x⁻¹ * l⁻¹) * w * l * x := by rw [hh]
      _ = (w : G) * x * l := by
        have hwc : Commute (w : G) (x * l * x⁻¹ * l⁻¹) := by
          let := R.elementary
          have hxw : x * l * x⁻¹ * l⁻¹ ∈ C.pointSpan :=
            C.chosen_le_pointSpan D (hm (commutator_mem_commutator
              (le_componentOrbit _ _ hx) hl))
          exact congrArg (fun a : C.pointSpan => (a : G))
            (mul_comm (⟨w, C.chosen_le_pointSpan D w.property⟩ : C.pointSpan) ⟨_, hxw⟩)
        rw [← hwc.eq]
        group
  have hmemb := mul_mem_sup (C.pointCore.inv_mem hw) hz
  simpa only [inv_mul_cancel_left] using hmemb

/-- The corrected local supplement, conditional only on its three identified
intermediate calculations. The source assembly must discharge all three. -/
theorem pointFixed_decomposition_of_moved_and_fixed_spaces
    (D : ChosenModule T L V) (R : C.PointSpanModule)
    (hm : ⁅C.pointSpan, L⁆ ≤ V)
    (hP : fixedSpace (BinaryPermutation.alternatingRepresentation (Fin 8))
      C.pointComponentImage ≤ BinaryPermutation.core (Fin 8))
    (hfixed : V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore) :
    omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed :=
  C.pointFixed_decomposition_of_cocycle_corrections D R hm
    (fun _ hx f hf => C.point_cocycle_correction_of_fixed_spaces hP hfixed hx f hf)

/-- Both conclusions consumed by the corrected terminal geometry. -/
theorem pointFixed_conclusions_of_moved_and_point_geometry
    (D : ChosenModule T L V) (R : C.PointSpanModule)
    (hm : ⁅C.pointSpan, L⁆ ≤ V)
    (hP : fixedSpace (BinaryPermutation.alternatingRepresentation (Fin 8))
      C.pointComponentImage ≤ BinaryPermutation.core (Fin 8))
    (hfixed : V ⊓ centralizer (L ⊓ C.pointSylow : Set G) ≤ C.pointCore)
    (hs : (T : Subgroup G) ≤ C.pointSylow ⊔ ((T : Subgroup G) ⊓ L)) :
    omegaCenterIn C.pointSylow = C.pointCore ⊔ C.pointFixed ∧
      C.pointFixed ≤ centralizer ((T : Subgroup G) : Set G) :=
  ⟨C.pointFixed_decomposition_of_moved_and_fixed_spaces D R hm hP hfixed,
    C.pointFixed_centralizes_sylow_of_supplement hs⟩

end AlternatingEightFusion
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
