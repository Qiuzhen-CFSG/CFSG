module
public import Theory.GroupTheory.QuaternionSwapModel.MarkedSylow.SecondParabolic

/-!
# Transport of marked quaternion-swap overlap geometry

An injective map on the second parabolic carries its entire overlap, extra
involution, and four generator equations to their literal images. Restricting
the map to this parabolic avoids assuming an ambient extension of an amalgam
isomorphism. This preserves the hypotheses that identify the Thompson sixteen
and the conjugate-generated marked plane.

Source application: Aschbacher--Smith 14.2.21, printed p.988.
-/

public noncomputable section
open Subgroup
namespace QuaternionSwapModel.MarkedSylow.SecondGeometry
variable {G G' : Type*} [Group G] [Group G']
variable {f : QH →* G} {T YT : Subgroup G} (d : SecondGeometry f T YT)

include d in
private theorem range_le : f.range ≤ T := by
  rintro _ ⟨x,rfl⟩
  exact (d.cover (f x)).mpr ⟨x,false,by simp⟩
private theorem t_mem : d.t ∈ T := (d.cover d.t).mpr ⟨1,true,by simp⟩
include d in
private theorem sylow_le : T ≤ YT := d.span.ge.trans' le_sup_left
private theorem y_mem : d.y ∈ YT := d.span.ge (mem_sup_right (mem_zpowers _))

@[expose] def into (d : SecondGeometry f T YT) : QH →* YT := f.codRestrict YT (by
  intro x
  apply d.span.ge
  exact mem_sup_left ((d.cover (f x)).mpr ⟨x,false,by simp⟩))

/-- Restrict the marked geometry to its second parabolic, then transport it
along an injective homomorphism. The whole overlap and generator remain actual images. -/
theorem transport (j : YT →* G') (hj : Function.Injective j) :
    Nonempty (SecondGeometry (j.comp d.into) ((T.subgroupOf YT).map j) j.range) := by
  let t : YT := ⟨d.t,(sylow_le d) (t_mem d)⟩
  let y : YT := ⟨d.y,(y_mem d)⟩
  have hTt : t ∈ T.subgroupOf YT := (t_mem d)
  have hconj (w : Raw) : t * d.into (projection w) * t⁻¹ = d.into (projection (twist w)) :=
    Subtype.ext (d.conjugation w)
  refine ⟨{ injective := hj.comp (fun x y h => d.injective (congrArg Subtype.val h))
            t := j t
            square := by rw [←map_mul,show t*t=1 from Subtype.ext d.square,map_one]
            outside := ?_
            conjugation := ?_
            cover := ?_
            y := j y
            span := ?_
            action_zero := ?_
            action_one := ?_
            action_two := ?_
            action_three := ?_ }⟩
  · rintro ⟨x,hx⟩
    exact d.outside ⟨x,congrArg Subtype.val (hj hx)⟩
  · intro w
    change j t * j (d.into (projection w)) * (j t)⁻¹ = _
    rw [←map_inv,←map_mul,←map_mul,hconj]
    rfl
  · intro g
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨x,b,he⟩ := (d.cover a.val).mp ha
      refine ⟨x,b,?_⟩
      have he' : a = d.into x * (if b then t else 1) := by
        cases b
        · apply Subtype.ext
          change (a : G) = f x * 1
          simpa using he
        · apply Subtype.ext
          change (a : G) = f x * d.t
          simpa using he
      rw [he',map_mul]
      cases b <;> simp
    · rintro ⟨x,b,rfl⟩
      refine ⟨d.into x * (if b then t else 1),?_,?_⟩
      · apply mul_mem
        · exact (range_le d) ⟨x,rfl⟩
        · cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
          · exact one_mem _
          · exact hTt
      · rw [map_mul]
        cases b <;> simp
  · apply le_antisymm
    · rintro _ ⟨a,rfl⟩
      have hall : (⊤ : Subgroup YT) = T.subgroupOf YT ⊔ zpowers y := by
        symm
        apply top_unique
        intro a ha
        have hspan : (T.subgroupOf YT ⊔ zpowers y).map YT.subtype = YT := by
          rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (sylow_le d),MonoidHom.map_zpowers]
          exact d.span.symm
        obtain ⟨z,hz,hza⟩ := hspan.ge a.property
        exact YT.subtype_injective hza ▸ hz
      have hmem : a ∈ T.subgroupOf YT ⊔ zpowers y := hall ▸ mem_top a
      have hm := mem_map_of_mem j hmem
      rwa [Subgroup.map_sup,MonoidHom.map_zpowers] at hm
    · apply sup_le
      · exact map_le_range j _
      · exact zpowers_le.mpr ⟨y,rfl⟩
  · simpa only [MonoidHom.comp_apply,map_mul,map_inv] using congrArg j
      (show y * d.into (MarkedCubic.bit 0) * y⁻¹ = d.into (MarkedCubic.bit 0) from
        Subtype.ext d.action_zero)
  · simpa only [MonoidHom.comp_apply,map_mul,map_inv] using congrArg j
      (show y * d.into (MarkedCubic.bit 1) * y⁻¹ = d.into (MarkedCubic.bit 1 * MarkedCubic.bit 2) from
        Subtype.ext d.action_one)
  · simpa only [MonoidHom.comp_apply,map_mul,map_inv] using congrArg j
      (show y * d.into (MarkedCubic.bit 2) * y⁻¹ = d.into (MarkedCubic.bit 1) from
        Subtype.ext d.action_two)
  · simpa only [MonoidHom.comp_apply,map_mul,map_inv] using congrArg j
      (show y * d.into (MarkedCubic.bit 3) * y⁻¹ = d.into (MarkedCubic.bit 1 * MarkedCubic.bit 3) from
        Subtype.ext d.action_three)

end QuaternionSwapModel.MarkedSylow.SecondGeometry
end
