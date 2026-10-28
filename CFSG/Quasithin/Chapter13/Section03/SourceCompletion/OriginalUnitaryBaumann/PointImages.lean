module
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import Theory.Representation.G2BinaryPointOffenders
public import Theory.Representation.G2BinaryThompson
/-!
# Thompson and Baumann images in the unitary point radical

The natural action descends through its exact centralizer kernel, including
when its image is proper. Absence of strong offenders puts V in Baum(R).
The point-radical offender theorem identifies every moving maximum elementary
image with the marked root eight. B.2.20 then identifies both J(R) and
Baum(R), using the literal pointwise fixer of the fixed three-space.

Source: Aschbacher–Smith C.1.37 and 13.3.10(2), pp.141–143,887–888.
The original automizer application is in AutomizerImages and
OriginalUnitaryNoncentrality.OffenderImages.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Atlas.G2.Natural.BinaryPointFlag
open ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
variable (q : G →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
variable (hker : q.ker = centralizer (V : Set G))
variable (hE : ∀ g v, E (Additive.ofMul (MulAut.conjNormal g v)) =
  Atlas.G2.Restricted.NaturalCoordinates.action F (q g) (E (Additive.ofMul v)))
include hE hker

omit [Finite G] hker in
/-- Faithfulness identifies the kernel in the same six-coordinate marking. -/
theorem unitary_coordinate_kernel : q.ker = centralizer (V : Set G) := by
  let C := Atlas.G2.Restricted.NaturalCoordinates.equiv F
  let E0 := E.trans C.symm
  apply Atlas.G2.Natural.BinaryNormalizer.marked_kernel_eq_centralizer V q E0
  intro g v
  apply C.injective
  have hc := hE g v
  have hr := (Atlas.G2.Restricted.NaturalCoordinates.repEquiv F).isIntertwining (q g)
    (E0 (Additive.ofMul v))
  change C (Atlas.G2.Natural.action F (q g) (E0 (Additive.ofMul v))) =
    Atlas.G2.Restricted.NaturalCoordinates.action F (q g) (C (E0 (Additive.ofMul v))) at hr
  have hv : C (E0 (Additive.ofMul v)) = E (Additive.ofMul v) := C.apply_symm_apply _
  exact (C.apply_symm_apply _).trans (hc.trans (hr.trans (congrArg
    (Atlas.G2.Restricted.NaturalCoordinates.action F (q g)) hv)).symm)

omit [Finite G] in
private theorem quotient_coordinates :
    ∀ g : q.range, ∀ v : Additive V,
      E (NormalElementaryQuotient.representation V q.rangeRestrict
        q.rangeRestrict_surjective (q.ker_rangeRestrict.trans hker) g v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F g.val (E v) := by
  intro g v
  obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
  have hr := NormalElementaryQuotient.representation_apply V q.rangeRestrict
    q.rangeRestrict_surjective (q.ker_rangeRestrict.trans hker) g v
  have hh : (NormalElementaryQuotient.representation V q.rangeRestrict
      q.rangeRestrict_surjective (q.ker_rangeRestrict.trans hker) (q.rangeRestrict g) v).toMul =
      MulAut.conjNormal g v.toMul := Subtype.ext hr
  exact (congrArg (fun w : V => E (Additive.ofMul w)) hh).trans (hE g v.toMul)

/-- The actual binary G₂ action has no strong offenders, even when the
specified acting image is proper. Every overgroup of V contains V in its Baumann subgroup. -/
theorem unitary_no_strong_and_le_baumann (R : Subgroup G) (hVR : V ≤ R) :
    NoStrongOffenders V R ∧ V ≤ ChapterB.baumann R := by
  let qr := q.rangeRestrict
  have hk := q.ker_rangeRestrict.trans hker
  let τ := NormalElementaryQuotient.representation V qr q.rangeRestrict_surjective hk
  let E0 := E.trans (Atlas.G2.Restricted.NaturalCoordinates.equiv F).symm
  have he0 (g : q.range) (v : Additive V) :
      E0 (τ g v) = Atlas.G2.Natural.action F g.val (E0 v) := by
    let C := Atlas.G2.Restricted.NaturalCoordinates.equiv F
    apply C.injective
    have hc := quotient_coordinates V q E hker hE g v
    have hr := (Atlas.G2.Restricted.NaturalCoordinates.repEquiv F).isIntertwining g.val (E0 v)
    change C (Atlas.G2.Natural.action F g.val (E0 v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F g.val (C (E0 v)) at hr
    have hv : C (E0 v) = E v := C.apply_symm_apply _
    exact (C.apply_symm_apply _).trans (hc.trans (hr.trans (congrArg
      (Atlas.G2.Restricted.NaturalCoordinates.action F g.val) hv)).symm)
  have hn : ¬ IsStrongFFModule τ := by
    rintro ⟨A,hA,hs⟩
    have ho : IsOffender τ A := ⟨hA,hs.le⟩
    have hm := ho.map_equivariant τ (Atlas.G2.Natural.action F)
      q.range.subtype q.range.subtype_injective E0 he0
    apply Atlas.G2.NaturalOffenders.natural_no_strong (F := F) (n := 1)
      (by norm_num) (by decide)
    refine ⟨A.map q.range.subtype,hm.1,?_⟩
    change BinaryOffender.fixedCodim (Atlas.G2.Natural.action F) _ < _
    rw [←fixedCodim_map_equivariant τ (Atlas.G2.Natural.action F)
      q.range.subtype E0 he0,rank_map_injective _ q.range.subtype_injective]
    exact hs
  have hno := noStrong_of_centralizer_quotient V qr q.rangeRestrict_surjective hk hn R
  refine ⟨hno,le_inf hVR ?_⟩
  have hc := centralizer_rank_and_alpha V R hVR hno
  let C := ChapterB.thompsonAlpha (R ⊓ centralizer (V : Set G))
  let : IsElementaryAbelian 2 C := omegaOneCenterAmbient_elementaryAbelian _
  intro v hv a ha
  exact congrArg (fun x : C => (x : G))
    ((inferInstance : IsMulCommutative C).is_comm.comm ⟨a,hc.2.2.2 ha⟩ ⟨v,hc.2.2.1 hv⟩)

/-- Original maximum elementary subgroups have the unique marked point-radical image.
Consequently J(R) and Baum(R) have that same image whenever J(R) moves V. -/
theorem unitary_point_thompson_baumann_images (R : Subgroup G) (hVR : V ≤ R)
    (hR : R.map q ≤ Atlas.G2.LieParabolicSetup.radical₂)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    (elementaryAbelianMaxJ R).map q = Atlas.G2.BinaryCore.elementary ∧
      (ChapterB.baumann R).map q = Atlas.G2.BinaryCore.elementary := by
  let qr := q.rangeRestrict
  have hk := q.ker_rangeRestrict.trans hker
  let τ := NormalElementaryQuotient.representation V qr q.rangeRestrict_surjective hk
  have he := quotient_coordinates V q E hker hE
  have hmax (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R)
      (hne : A.map q ≠ ⊥) : A.map q = Atlas.G2.BinaryCore.elementary := by
    have hn : ¬ A ≤ centralizer (V : Set G) := by
      intro hc
      exact hne ((map_eq_bot_iff A).mpr (hc.trans_eq hker.symm))
    have ho := NormalElementaryQuotient.maxElementary_isOffender V qr
      q.rangeRestrict_surjective hk R A hVR hA (by rwa [hk])
    have hm := ho.map_equivariant τ (Atlas.G2.Restricted.NaturalCoordinates.action F)
      q.range.subtype q.range.subtype_injective E he
    rw [Subgroup.map_map] at hm
    exact Atlas.G2.Natural.BinaryPointOffenders.offender_eq_elementary _ hm
      ((map_mono hA.1).trans hR)
  apply ChapterB.thompson_baumann_image_of_unique_maximum_image V R q
    Atlas.G2.BinaryCore.elementary hVR hJ hmax
  rintro _ ⟨x,hx,rfl⟩
  apply (Atlas.G2.Natural.BinaryPointOffenders.fixes_seed_iff (q x)).mp
  intro w hw
  obtain ⟨v,rfl⟩ := E.surjective w
  have hv : (v.toMul : G) ∈ V ⊓ centralizer
      ((Atlas.G2.BinaryCore.elementary).comap q : Set G) := by
    refine ⟨v.toMul.property,?_⟩
    intro a ha
    have hf := (Atlas.G2.Natural.BinaryPointOffenders.fixes_seed_iff (q a)).mpr ha (E v) hw
    have hf' := (hE a v.toMul).trans hf
    have heq : a * (v.toMul : G) * a⁻¹ = v.toMul :=
      congrArg (fun z : Additive V => (z.toMul : G)) (E.injective hf')
    exact (mul_inv_eq_iff_eq_mul.mp heq)
  have hc : MulAut.conjNormal x v.toMul = v.toMul := by
    apply Subtype.ext
    change x * (v.toMul : G) * x⁻¹ = v.toMul
    rw [←hx.2 _ hv,mul_inv_cancel_right]
  exact (hE x v.toMul).symm.trans (congrArg (fun z : V => E (Additive.ofMul z)) hc)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
