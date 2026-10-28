module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals

/-!
# The actual projection of a lifted Borel

The Borel is lifted inside K through H → H/O₂(H). Its restricted star
map has two-group kernel, by its injective map into O₂(H). Restricting
the range constructs a surjection onto the prescribed Borel B₀*.
Thus source lifts can be used without identifying them with their images.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels
variable {G : Type*} [Group G]

theorem starHom_ker_isTwoGroup (H K : Subgroup G) (hKH : K ≤ H) :
    IsPGroup 2 (starHom H K hKH).ker := by
  let i : (starHom H K hKH).ker →* pCore 2 H :=
    { toFun x := ⟨inclusion hKH x.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : pCore 2 H => a.val.val) h
  exact pCore_isPGroup.of_injective i hi

noncomputable def borelStarProjection (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K) :
    borelLift H K hKH B₀star →* B₀star := by
  let f := starHom H (borelLift H K hKH B₀star) ((borelLift_le H K hKH B₀star).trans hKH)
  have hr : f.range = B₀star :=
    (range_starHom _ _ _).trans (starImage_borelLift H K hKH B₀star hB)
  exact (MulEquiv.subgroupCongr hr).toMonoidHom.comp f.rangeRestrict

theorem borelStarProjection_surjective (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K) :
    Function.Surjective (borelStarProjection H K hKH B₀star hB) := by
  let f := starHom H (borelLift H K hKH B₀star) ((borelLift_le H K hKH B₀star).trans hKH)
  have hr : f.range = B₀star :=
    (range_starHom _ _ _).trans (starImage_borelLift H K hKH B₀star hB)
  exact (MulEquiv.subgroupCongr hr).surjective.comp f.rangeRestrict_surjective

theorem borelStarProjection_ker_isTwoGroup (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K) :
    IsPGroup 2 (borelStarProjection H K hKH B₀star hB).ker := by
  have he : (borelStarProjection H K hKH B₀star hB).ker =
      (starHom H (borelLift H K hKH B₀star) ((borelLift_le H K hKH B₀star).trans hKH)).ker := by
    ext x
    change borelStarProjection H K hKH B₀star hB x = 1 ↔ _ = 1
    exact Subtype.ext_iff
  rw [he]
  exact starHom_ker_isTwoGroup _ _ _

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels
