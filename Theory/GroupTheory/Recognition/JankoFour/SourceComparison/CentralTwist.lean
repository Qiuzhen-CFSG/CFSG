module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.SixCover
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.PointComparison
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The plane central twist of AS91 (8.2)

The inverse image of Inn(M₂₂) in H is QC_H(A). Its index is two.
Perfectness puts C_H(A) inside O²(H), and the coprime cubic action puts Q
there as well. Thus this inverse image is precisely the source two-residual.
Multiplying the other coset by the actual marked z defines a nonidentity
involutory automorphism. It fixes Q and C_H(A) pointwise and preserves the
literal point-plane overlap.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), pp.605–606.
This constructs alpha and its stated restriction; classification of all
automorphisms of the overlap remains a separate argument.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu
attribute [local instance] Classical.propDecidable

section Twist
variable {H : Type*} [Group H] (K : Subgroup H) (hi : K.index = 2)
variable (u : H) (hu : u ∈ center H) (huK : u ∈ K) (hu2 : u * u = 1)

private noncomputable def centralShear : H →* H where
  toFun x := if x ∈ K then x else x * u
  map_one' := by simp
  map_mul' x y := by
    classical
    have hm := Subgroup.mul_mem_iff_of_index_two hi (a := x) (b := y)
    have hc := mem_center_iff.mp hu y
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
    · simp only [if_pos hx,if_pos hy,if_pos (K.mul_mem hx hy)]
    · have hxy : x*y ∉ K := fun hxy => hy ((hm.mp hxy).mp hx)
      simp only [if_pos hx,if_neg hy,if_neg hxy,mul_assoc]
    · have hxy : x*y ∉ K := fun hxy => hx ((hm.mp hxy).mpr hy)
      simp only [if_neg hx,if_pos hy,if_neg hxy]
      rw [mul_assoc,hc,← mul_assoc]
    · have hxy : x*y ∈ K := hm.mpr (iff_of_false hx hy)
      simp only [if_neg hx,if_neg hy,if_pos hxy]
      rw [mul_assoc,← mul_assoc u y u,← hc,mul_assoc y u u,hu2,mul_one]

include huK in
private theorem centralShear_mem (x : H) : centralShear K hi u hu hu2 x ∈ K ↔ x ∈ K := by
  classical
  change (if x ∈ K then x else x*u) ∈ K ↔ x ∈ K
  by_cases hx : x ∈ K
  · simp [hx]
  · rw [if_neg hx]
    exact K.mul_mem_cancel_right huK

include huK in
private theorem centralShear_involutive : Function.Involutive (centralShear K hi u hu hu2) := by
  classical
  intro x
  change (if centralShear K hi u hu hu2 x ∈ K then centralShear K hi u hu hu2 x
    else centralShear K hi u hu hu2 x * u) = x
  by_cases hx : x ∈ K
  · rw [if_pos ((centralShear_mem K hi u hu huK hu2 x).mpr hx)]
    exact if_pos hx
  · rw [if_neg (fun hm => hx ((centralShear_mem K hi u hu huK hu2 x).mp hm))]
    change (if x ∈ K then x else x*u)*u=x
    rw [if_neg hx,mul_assoc,hu2,mul_one]

/-- The central involutory change on the nontrivial coset of an index-two subgroup. -/
noncomputable def indexTwoCentralTwist : MulAut H :=
  { centralShear K hi u hu hu2 with
    invFun := centralShear K hi u hu hu2
    left_inv := centralShear_involutive K hi u hu huK hu2
    right_inv := centralShear_involutive K hi u hu huK hu2 }

theorem indexTwoCentralTwist_apply (x : H) :
    indexTwoCentralTwist K hi u hu huK hu2 x = if x ∈ K then x else x*u := by rfl

theorem indexTwoCentralTwist_sq : indexTwoCentralTwist K hi u hu huK hu2 ^ 2 = 1 := by
  apply MulEquiv.ext
  exact centralShear_involutive K hi u hu huK hu2

theorem indexTwoCentralTwist_map (I : Subgroup H) (huI : u ∈ I) :
    I.map (indexTwoCentralTwist K hi u hu huK hu2).toMonoidHom = I := by
  classical
  have hf (x : H) (hx : x ∈ I) : indexTwoCentralTwist K hi u hu huK hu2 x ∈ I := by
    rw [indexTwoCentralTwist_apply]
    split_ifs
    · exact hx
    · exact I.mul_mem hx huI
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hf x hx
  · intro x hx
    exact ⟨indexTwoCentralTwist K hi u hu huK hu2 x,hf x hx,
      centralShear_involutive K hi u hu huK hu2 x⟩
end Twist

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

/-- The inverse image of the inner Mathieu automorphisms in the original H. -/
noncomputable def planeEven : Subgroup (centralizer z) :=
  (innerPreimage e).comap (QuotientGroup.mk' (core z))

instance planeEven_normal : (planeEven e).Normal := by
  unfold planeEven
  infer_instance

include h in
theorem planeEven_eq_sup : planeEven e = core z ⊔ cubicCentralizerInH e X := by
  unfold planeEven
  rw [← cubicCentralizer_map_coreQuotient h e X,comap_map_eq,QuotientGroup.ker_mk',sup_comm]

theorem planeEven_index : (planeEven e).index = 2 := by
  change (((MulAut.innerSubgroup M22).comap e.projection).comap (QuotientGroup.mk' (core z))).index = 2
  rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    index_comap_of_surjective _ e.surjective,index_eq_card]
  have hu := M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two
  have hl := m22Out_card_lower_bound
  change 2 ≤ Nat.card (MulAut.Outer M22) at hl
  exact Nat.le_antisymm (Nat.le_of_dvd (by decide) hu) hl

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))

include h hp in
/-- The actual two-residual is QC; no residual convention is replaced by a tag. -/
theorem planeEven_eq_twoResidual : planeEven e = pResidual 2 (centralizer z) := by
  let := hp
  have hC : cubicCentralizerInH e X ≤ pResidual 2 (centralizer z) := by
    have hm := map_pResidual_le 2 (cubicCentralizerInH e X).subtype
    rw [pResidual_eq_top_of_isPerfect 2,← MonoidHom.range_eq_map,range_subtype] at hm
    exact hm
  have hQ : core z ≤ pResidual 2 (centralizer z) := by
    let : IsExtraspecial 2 (core z) := h.extraspecial
    let : Group.IsNilpotent (core z) := (IsExtraspecial.isPGroup 2 (core z)).isNilpotent
    have hdec := eq_commutator_sup_centralizer_of_solvable_coprime
      (core z) (cubicSylowImage e X) (by rw [(core z).normalizer_eq_top]; exact le_top)
      inferInstance (by rw [cubicSylowImage_card h e X,h.core_card]; norm_num)
    rw [hdec]
    apply sup_le
    · exact (commutator_mono le_rfl ((cubicSylowImage_le_centralizer h e X).trans hC)).trans
        (commutator_le_right _ _)
    · exact inf_le_right.trans hC
  apply le_antisymm
  · rw [planeEven_eq_sup h e X]
    exact sup_le hQ hC
  · apply (pResidual_le_iff_isPGroup_quotient 2 (planeEven e)).mpr
    apply IsPGroup.of_card (n := 1)
    rw [← index_eq_card,planeEven_index,pow_one]

/-- The marker inside the original H. -/
def planeMarker : centralizer z := ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite G] in
theorem planeMarker_central : planeMarker (z := z) ∈ center (centralizer z) := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

include h in
theorem planeMarker_mem_even : planeMarker (z := z) ∈ planeEven e := by
  change QuotientGroup.mk' (core z) (planeMarker (z := z)) ∈ innerPreimage e
  rw [show QuotientGroup.mk' (core z) (planeMarker (z := z)) = 1 from
    (QuotientGroup.eq_one_iff _).mpr (centralizer_center_le_core h planeMarker_central)]
  exact one_mem _

include h in
theorem planeMarker_sq : planeMarker (z := z) * planeMarker (z := z) = 1 := by
  apply Subtype.ext
  change z*z=1
  have ho := pow_orderOf_eq_one z
  rwa [h.involution,pow_two] at ho

/-- The actual central twist from AS91 (8.2). -/
noncomputable def planeTwist : MulAut (centralizer z) :=
  indexTwoCentralTwist (planeEven e) (planeEven_index e) (planeMarker (z := z))
    planeMarker_central (planeMarker_mem_even h e) (planeMarker_sq h)

theorem planeTwist_apply (x : centralizer z) :
    planeTwist h e x = if x ∈ planeEven e then x else x*planeMarker := by rfl

include hp in
theorem planeTwist_residual_formula (x : centralizer z) :
    planeTwist h e x = if x ∈ pResidual 2 (centralizer z) then x else x*planeMarker := by
  rw [planeTwist_apply,planeEven_eq_twoResidual h e X hp]

theorem planeTwist_sq : planeTwist h e ^ 2 = 1 :=
  indexTwoCentralTwist_sq _ _ _ _ _ _

theorem planeTwist_ne_one : planeTwist h e ≠ 1 := by
  intro he
  have htop : planeEven e = ⊤ := by
    apply top_unique
    intro x _
    by_contra hx
    have hh := congrArg (fun a : MulAut (centralizer z) => a x) he
    change planeTwist h e x = x at hh
    rw [planeTwist_apply,if_neg hx] at hh
    have hz1 : z = 1 := congrArg Subtype.val (mul_left_cancel (hh.trans (mul_one x).symm))
    have ho := h.involution
    rw [hz1,orderOf_one] at ho
    contradiction
  have hi := planeEven_index e
  rw [htop,index_top] at hi
  contradiction

theorem planeTwist_fixes_core (q : core z) : planeTwist h e q.val = q.val := by
  rw [planeTwist_apply]
  apply if_pos
  change QuotientGroup.mk' (core z) q.val ∈ innerPreimage e
  rw [show QuotientGroup.mk' (core z) q.val = 1 from (QuotientGroup.eq_one_iff _).mpr q.property]
  exact one_mem _

theorem planeTwist_fixes_cubicCentralizer (c : cubicCentralizerInH e X) :
    planeTwist h e c.val = c.val := by
  rw [planeTwist_apply]
  exact if_pos ((planeEven_eq_sup h e X).ge ((le_sup_right : cubicCentralizerInH e X ≤ core z ⊔ cubicCentralizerInH e X) c.property))

/-- In particular, the actual point-plane overlap is preserved. -/
theorem planeTwist_point_overlap (a : SourceIncidence.LocalData h) :
    (a.P.M.subgroupOf (centralizer z)).map (planeTwist h a.e).toMonoidHom =
      a.P.M.subgroupOf (centralizer z) :=
  indexTwoCentralTwist_map _ _ _ _ _ _ _ (marker_mem_point a)

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
