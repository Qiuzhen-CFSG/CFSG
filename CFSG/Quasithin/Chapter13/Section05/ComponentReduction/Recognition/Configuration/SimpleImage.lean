module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Marked
public import Theory.GroupAction.PerfectCentralQuotient

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis)

/-- The surjection from the original K inside X to precisely K*. -/
def componentStarMap : K.subgroupOf (X D K) →* starImage D.H K :=
  (MulEquiv.subgroupCongr (starHom_map s h K le_sup_left)).toMonoidHom.comp
    ((starHom s h).subgroupMap (K.subgroupOf (X D K)))

theorem componentStarMap_surjective : Function.Surjective (componentStarMap s h) :=
  (MulEquiv.subgroupCongr (starHom_map s h K le_sup_left)).surjective.comp
    ((starHom s h).subgroupMap_surjective _)

theorem componentStarMap_apply (k : K.subgroupOf (X D K)) :
    (componentStarMap s h k : Hstar D.H) = starHom s h k.val := rfl

variable [(componentCentralizer s h).Normal]

/-- The two maps on K have the same kernel: centralizing K* is exactly
membership in Z(K*) for an element of K*. -/
theorem component_image_kernel :
    ((QuotientGroup.mk' (componentCentralizer s h)).subgroupMap
      (K.subgroupOf (X D K))).ker =
    ((QuotientGroup.mk' (center (starImage D.H K))).comp (componentStarMap s h)).ker := by
  rw [ker_subgroupMap, QuotientGroup.ker_mk']
  ext k
  change starHom s h k.val ∈ centralizer (starImage D.H K : Set (Hstar D.H)) ↔
    QuotientGroup.mk' (center (starImage D.H K)) (componentStarMap s h k) = 1
  constructor
  · intro hk
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hk y y.property)
  · intro hk
    have hk' := (QuotientGroup.eq_one_iff _).mp hk
    rw [mem_center_iff] at hk'
    intro y hy
    exact congrArg Subtype.val (hk' ⟨y, hy⟩)

/-- The source K̂ is the actual simple central quotient of K*. -/
def KhatEquiv : Khat s h ≃* starImage D.H K ⧸ center (starImage D.H K) :=
  (QuotientGroup.quotientKerEquivOfSurjective
    ((QuotientGroup.mk' (componentCentralizer s h)).subgroupMap (K.subgroupOf (X D K)))
    ((QuotientGroup.mk' (componentCentralizer s h)).subgroupMap_surjective _)).symm.trans
  ((QuotientGroup.quotientMulEquivOfEq (component_image_kernel s h)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (center (starImage D.H K))).comp (componentStarMap s h))
      ((QuotientGroup.mk'_surjective _).comp (componentStarMap_surjective s h))))

theorem Khat_simple : IsSimpleGroup (Khat s h) := by
  let := s.quasisimple
  let : IsSimpleGroup (starImage D.H K ⧸ center (starImage D.H K)) := IsQuasisimple.simple
  exact (KhatEquiv s h).isSimpleGroup

theorem Khat_perfect : Group.IsPerfect (Khat s h) := by
  let := s.ccomponent.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe s.le_H).toMonoidHom)
    (subgroupOfEquivOfLe s.le_H).surjective
  let : Group.IsPerfect (K.subgroupOf (X D K)) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ X D K from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).symm.surjective
  exact Group.IsPerfect.ofSurjective
    ((QuotientGroup.mk' (componentCentralizer s h)).subgroupMap_surjective (K.subgroupOf (X D K)))

theorem Khat_normal
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    (Khat s h).Normal := by
  let := s.normal_in_X h hn
  exact (inferInstance : (K.subgroupOf (X D K)).Normal).map _
    (QuotientGroup.mk'_surjective _)

/-- Perfectness of K* makes the action of X̂ on K̂ faithful. -/
theorem Khat_centralizer
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    centralizer (Khat s h : Set (Xhat s h)) = ⊥ := by
  let := s.quasisimple
  apply bot_unique
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (componentCentralizer s h) z
  let a := componentConjugation s h hn x
  have ha : a = 1 := by
    apply MulAut.eq_one_of_central_displacement
    intro k
    obtain ⟨u, rfl⟩ := componentStarMap_surjective s h k
    have hu : QuotientGroup.mk' (componentCentralizer s h) u.val ∈ Khat s h :=
      markedImage_mk s h K u.val u.property
    have he := mem_centralizer_iff.mp hz _ hu
    have hk : u.val⁻¹ * x * u.val * x⁻¹ ∈ componentCentralizer s h := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (componentCentralizer s h)
        (u.val⁻¹ * x * u.val * x⁻¹) = 1
      simp only [map_mul, map_inv]
      calc
        _ = (QuotientGroup.mk' (componentCentralizer s h) u.val)⁻¹ *
          (QuotientGroup.mk' (componentCentralizer s h) x *
            QuotientGroup.mk' (componentCentralizer s h) u.val) *
              (QuotientGroup.mk' (componentCentralizer s h) x)⁻¹ := by group
        _ = _ := by rw [← he]; group
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    have hcomm := mem_centralizer_iff.mp hk b.val b.property
    change b.val * starHom s h (u.val⁻¹ * x * u.val * x⁻¹) =
      starHom s h (u.val⁻¹ * x * u.val * x⁻¹) * b.val at hcomm
    change b.val * ((starHom s h u.val)⁻¹ *
      (starHom s h x * starHom s h u.val * (starHom s h x)⁻¹)) =
      ((starHom s h u.val)⁻¹ *
      (starHom s h x * starHom s h u.val * (starHom s h x)⁻¹)) * b.val
    simpa only [map_mul, map_inv, mul_assoc] using hcomm
  have hx : x ∈ componentCentralizer s h := by
    rw [← componentConjugation_ker s h hn]
    exact ha
  exact (QuotientGroup.eq_one_iff x).mpr hx

private theorem fitting_eq_of_normal_quasisimple {A : Type*} [Group A] [Finite A]
    (L : Subgroup A) [L.Normal] [IsQuasisimple L]
    (hc : centralizer (L : Set A) = ⊥) : generalizedFitting A = L := by
  have hL : IsComponent A L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  apply le_antisymm
  · apply sup_le
    · rcases hL.normal_dichotomy (fittingSubgroup A) with h | h
      · have hs : Group.IsSolvable L :=
          Group.isSolvable_of_isSolvable_injective (inclusion_injective h)
        exact (Group.IsPerfect.not_isSolvable L hs).elim
      · have hf := commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans h)
        rw [hc] at hf
        exact hf.trans bot_le
    · apply sSup_le
      intro M hM
      rcases hM.normal_dichotomy L with h | h
      · exact h
      · exact ((commutator_eq_bot_iff_le_centralizer.mp h).trans hc.le).trans bot_le
  · exact component_le_generalizedFitting A L hL

/-- The selected simple image is the whole generalized Fitting subgroup of X̂. -/
theorem Khat_generalizedFitting
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    generalizedFitting (Xhat s h) = Khat s h := by
  let := Khat_normal s h hn
  let := Khat_simple s h
  let := Khat_perfect s h
  have hz : center (Khat s h) = ⊥ := by
    rcases (inferInstance : (center (Khat s h)).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · exact (Group.IsPerfect.not_isMulCommutative (Khat s h)
        (center_eq_top_iff.mp he)).elim
  let : IsQuasisimple (Khat s h) := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  exact fitting_eq_of_normal_quasisimple _ (Khat_centralizer s h hn)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
