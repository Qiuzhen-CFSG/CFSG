module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import Theory.Representation.SL3OddNaturalNormalizer.PointFixers
public import Theory.Representation.SL3OddNaturalNormalizer.Index
public import Theory.ElementaryAbelian.RankOneImageCriterion
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.GroupTheory.SylowNormalJoinIntersection

/-!
# Inner A₂ actors for the original natural SL₃ module

The field action of an elementary two-group has image of order at most two.
Thus the defining A₂ equality makes every actor fix the same space as its
field-linear kernel. That kernel has a nonzero fixed field line. Pointwise
fixation of the line removes the field part, and square one forces determinant
one. Faithfulness then identifies every actor with an element of the actual
SL₃ layer.

The original SL₃ central part vanishes by the proved preliminary theorem,
so its literal coordinate projection transports the A₂ condition exactly.
Finally a Sylow intersection in the product of the layer and action kernel
lifts inner image containment to L O₂(LT), retaining the actual two-core.
Source: Aschbacher--Smith, I.2.3 and 11.2.2(4), printed pp.413,768.
The Source endpoint applies this to the actual indexed weak closure.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
  [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite H] [CharP F 2] in
private theorem field_kernel_corank (A : Subgroup H) [IsElementaryAbelian 2 A]
    (φ : H →* (F ≃+* F)) : Nat.log 2 ((A ⊓ φ.ker).relIndex A) < 2 := by
  let f := φ.comp A.subtype
  have he : f.ker = (A ⊓ φ.ker).subgroupOf A := by
    ext x
    change φ (x : H) = 1 ↔ (x : H) ∈ A ∧ φ (x : H) = 1
    exact ⟨fun hx => ⟨x.property,hx⟩, And.right⟩
  have hr : f.range = A.map φ := by ext x; simp [f,MonoidHom.mem_range,mem_map]
  have hcard := Representation.SL2NaturalOffenders.fieldAction_range_card_le_two A (inferInstance : IsElementaryAbelian 2 A) f
  have hc : (A ⊓ φ.ker).relIndex A ≤ 2 := by
    change ((A ⊓ φ.ker).subgroupOf A).index ≤ 2
    rw [← he, index_ker,hr]
    rwa [hr] at hcard
  have hh := Nat.log_mono_right hc (b := 2)
  norm_num at hh
  omega

/-- A₂ actors of a faithful full natural SL₃ normalizer are inner. -/
theorem sl3_two_family_inner
    (K : Subgroup H) [K.Normal]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F)) (hρ : Function.Injective ρ)
    (hK : ∀ (g : K) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {A : Subgroup H} (hA : A ∈ fixedSpaceFamily ρ 2) : A ≤ K := by
  let := hA.2.1.2
  let hsemi := SL3OddNaturalNormalizer.normalizer_semilinear K e ρ hK
  let φ := SL3OddNaturalNormalizer.fieldAction ρ hsemi
  let B := A ⊓ φ.ker
  have hfix := hA.2.2 B inf_le_left (field_kernel_corank A φ)
  let τ : Representation F B (Fin 3 → F) := {
    toFun g := {
      toFun := ρ (g : H)
      map_add' := (ρ (g : H)).map_add
      map_smul' := (SL3OddNaturalNormalizer.fieldAction_eq_one_iff ρ hsemi g).mp g.property.2 }
    map_one' := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun ρ.map_one v
    map_mul' g h := by apply LinearMap.ext; intro v; exact LinearMap.congr_fun (ρ.map_mul g h) v }
  have hB : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left
  obtain ⟨v,hv,hvfix⟩ := pGroup_fix_nonzero_vector
    (F := F) (by rw [ringChar.eq F 2]; decide)
    (by simpa only [ringChar.eq F 2] using hB) τ
  have hall (a : A) (r : F) : ρ a (r • v) = r • v := by
    have hb : r • v ∈ fixedSpace ρ B := by
      intro b
      change τ b (r • v) = r • v
      rw [map_smul]
      exact congrArg (r • ·) (hvfix b)
    exact (hfix.symm ▸ hb) a
  let P := Submodule.span F {v}
  have hP : P ≠ ⊥ := by
    intro hz
    have hm : v ∈ P := Submodule.subset_span (Set.mem_singleton v)
    rw [hz,Submodule.mem_bot] at hm
    exact hv hm
  intro a ha
  have hsa : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  obtain ⟨s,hs⟩ := SL3OddNaturalNormalizer.exists_specialLinear_of_square_one_of_fixes_submodule
    K e ρ hK P hP a hsa (by
      intro w hw
      obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hw
      exact hall ⟨a,ha⟩ r)
  have heq : a = e.symm s := hρ (by
    apply LinearMap.ext
    intro w
    rw [hK,e.apply_symm_apply]
    exact hs w)
  rw [heq]
  exact (e.symm s).property

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The same assertion on the literal automizer of the original chosen V. -/
theorem sl3_original_two_family_inner
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := D.elementary
    ∀ A : Subgroup (Automizer V),
      A ∈ fixedSpaceFamily (automizerRepresentation V) 2 → A ≤ inducedAutomizer V L := by
  let := D.elementary
  intro A hA
  let c := Coordinates.sl3 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  have hinj : Function.Injective c.projection := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro w hw
    have hc := (c.projection_eq_one_iff w).mp hw
    have hz : (w : G) ∈ (⊥ : Subgroup G) := by
      rw [← Preliminary.sl3_centralizer_eq_bot D S m]
      exact ⟨w.property,hc⟩
    exact Subtype.ext hz
  have hpi : Function.Injective (projectionLinear D S c) := hinj
  have hfix (B : Subgroup (Automizer V)) :
      fixedSpace (automizerRepresentation V) B =
        (fixedSpace ρ B).comap (projectionLinear D S c) := by
    ext v
    constructor
    · intro hv b
      exact (he b v).symm.trans (congrArg (projectionLinear D S c) (hv b))
    · intro hv b
      apply hpi
      exact (he b v).trans (hv b)
  have hf : A ∈ fixedSpaceFamily ρ 2 := by
    refine ⟨hA.1,hA.2.1,fun B hBA hk => ?_⟩
    apply Submodule.comap_injective_of_surjective (projectionLinear_surjective D S c)
    rw [← hfix,← hfix]
    exact hA.2.2 B hBA hk
  let := layer_normal D S
  exact sl3_two_family_inner (inducedAutomizer V L) (layerEquiv D S c) ρ hρ hres hf

include D S in
/-- Lifting inner two-actors retains the actual kernel O₂(LT). -/
theorem le_component_join_core_of_image
    {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (himage : inducedAutomizer V A ≤ inducedAutomizer V L) :
    A ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let N := normalizer (V : Set G)
  let K := L.subgroupOf N
  let f := V.normalizerMonoidHom.rangeRestrict
  let C := f.ker
  let P := T.subtype S.sylow_normalizes
  let : K.Normal := normal_subgroupOf_of_le_normalizer (seed_normalizer_le D S)
  have hc : (P : Subgroup N) ⊓ C ≤
      (L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).comap N.subtype := by
    intro y hy
    have ht : (y : G) ∈ (T : Subgroup G) := hy.1
    have hcv : (y : G) ∈ centralizer (V : Set G) := by
      have hh : y ∈ V.normalizerMonoidHom.rangeRestrict.ker := hy.2
      rwa [MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker] at hh
    exact mem_sup_right ((seed_sylow_centralizer D S).le ⟨ht,hcv⟩)
  have hk : (P : Subgroup N) ⊓ K ≤
      (L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).comap N.subtype :=
    fun y hy => mem_sup_left hy.2
  intro x hx
  let y : N := ⟨x,S.sylow_normalizes (hAT hx)⟩
  have hy : f y ∈ K.map f := himage ⟨y,hx,rfl⟩
  have hyKC : y ∈ K ⊔ C := by
    have hh : y ∈ (K.map f).comap f := hy
    rwa [comap_map_eq] at hh
  have hyP : y ∈ (P : Subgroup N) := hAT hx
  have hyjoin : y ∈ ((P : Subgroup N) ⊓ K) ⊔ ((P : Subgroup N) ⊓ C) := by
    rw [← P.inf_sup_eq_sup_inf_normal K C]
    exact ⟨hyP,hyKC⟩
  exact (sup_le hk hc) hyjoin

/-- Source 11.2.2's A₂ assertion for SL₃ in every degree, in the literal T. -/
theorem sl3_two_family
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := D.elementary
    ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
      A ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := D.elementary
  intro A hAT hA
  exact le_component_join_core_of_image D S hAT
    (sl3_original_two_family_inner D S m _ hA)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors
