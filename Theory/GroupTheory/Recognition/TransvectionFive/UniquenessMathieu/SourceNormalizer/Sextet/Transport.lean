module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Plane
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Action

/-!
# The six literal four-subgroups of the 45-point rectangle

The checked census determines the marked fusion set. Its 18 excluded
nonzero vectors form six intrinsic four-subgroups, which are transported
through the original rectangle coordinates. The ambient normalizer permutes
these actual subgroups, and the action descends through the original
rectangle denominator. This constructs the six-point action used in 40.4.
Its surjectivity, order-three kernel, and the involution centralizer and
solvable-residual identifications remain to be proved.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4, p.218.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The marked 45-point fusion set is the complement of the six triples. -/
theorem plane_fusion_iff_fused [Finite G]
    (hcount : (F.fusion F.plane).ncard = 45) (x : Code) :
    IsConj z (element F x) ↔ Sextet.fused x = true :=
  plane_fusion_census F hcount Sextet.fused Sextet.eq_fused_of_forty_five x

/-- The six four-subgroups, as subgroups of the original ambient group. -/
def planeFour (i : Fin 6) : Subgroup G where
  carrier := {a | ∃ x ∈ Sextet.line i, element F x = a}
  one_mem' := ⟨0, Sextet.line_zero i, element_zero F⟩
  mul_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x ^^^ y, Sextet.line_xor i x y hx hy, element_xor F x y⟩
  inv_mem' := by
    rintro a ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    have hh : element F x * element F x = 1 := by
      rw [← element_xor]
      rw [BitVec.xor_self]
      exact element_zero F
    exact (inv_eq_of_mul_eq_one_right hh).symm

theorem mem_planeFour (i : Fin 6) (a : G) :
    a ∈ planeFour F i ↔ ∃ x ∈ Sextet.line i, element F x = a := Iff.rfl

theorem planeFour_le (i : Fin 6) : planeFour F i ≤ F.plane := by
  rintro a ⟨x, _, rfl⟩
  exact element_mem F x

theorem planeFour_card (i : Fin 6) : Nat.card (planeFour F i) = 4 := by
  let e : {x : Code // x ∈ Sextet.line i} ≃ planeFour F i :=
    Equiv.ofBijective (fun x => ⟨element F x, x, x.property, rfl⟩)
      ⟨fun x y h => Subtype.ext (element_injective F (congrArg (fun q : planeFour F i => (q : G)) h)), by
        rintro ⟨a, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Sextet.line_card i

theorem planeFour_elementary (i : Fin 6) : IsElementaryAbelian 2 (planeFour F i) := by
  let := marked_rectangle_elementary F 2
  exact IsElementaryAbelian.of_injective (inclusion (planeFour_le F i))
    (inclusion_injective _)

/-- Distinct indices denote distinct literal ambient four-subgroups. -/
theorem planeFour_injective : Function.Injective (planeFour F) := by
  intro i j hij
  apply Sextet.line_injective
  ext x
  have hm (k : Fin 6) : element F x ∈ planeFour F k ↔ x ∈ Sextet.line k := by
    rw [mem_planeFour]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact element_injective F hyx ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  rw [← hm i, ← hm j, hij]

/-- The nonidentity elements of every marked four-group avoid the distinguished
involution's conjugacy class. -/
theorem planeFour_not_fused [Finite G] (hcount : (F.fusion F.plane).ncard = 45)
    (i : Fin 6) (a : G) (ha : a ∈ planeFour F i) (ha1 : a ≠ 1) : ¬ IsConj z a := by
  obtain ⟨x, hx, rfl⟩ := ha
  have hx0 : x ≠ 0 := fun he => ha1 (he ▸ element_zero F)
  have he := (Sextet.exceptional_iff x).mp (Sextet.line_exceptional i x hx hx0)
  rw [plane_fusion_iff_fused F hcount, he.2]
  decide

/-- Every nonidentity plane element outside the fused class lies in exactly
one of the six actual four-subgroups. -/
theorem exists_unique_planeFour [Finite G] (hcount : (F.fusion F.plane).ncard = 45)
    (a : G) (ha : a ∈ F.plane) (ha1 : a ≠ 1) (hza : ¬ IsConj z a) :
    ∃! i : Fin 6, a ∈ planeFour F i := by
  obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha⟩
  have hxe : element F x = a := congrArg Subtype.val hx
  have hx0 : x ≠ 0 := fun he => ha1 (hxe.symm.trans (he ▸ element_zero F))
  have hex : Sextet.exceptional x = true := by
    apply (Sextet.exceptional_iff x).mpr
    refine ⟨hx0, ?_⟩
    have hnot : Sextet.fused x ≠ true := fun h => hza (hxe ▸ (plane_fusion_iff_fused F hcount x).mpr h)
    cases h : Sextet.fused x <;> simp_all
  obtain ⟨i, hi, hu⟩ := Sextet.exceptional_unique_line x hex
  refine ⟨i, ⟨x, hi, hxe⟩, ?_⟩
  rintro j ⟨y, hy, hya⟩
  exact hu j ((element_injective F (hya.trans hxe.symm)) ▸ hy)

private theorem normalizer_exceptional [Finite G]
    (hcount : (F.fusion F.plane).ncard = 45) (n : planeNormalizer F) :
    normalizerAction F n ∈ Sextet.symmetryGroup := by
  apply (Sextet.mem_symmetryGroup _).mpr
  refine ⟨normalizerAction_xor F n, ?_⟩
  intro x
  have hf : Sextet.fused (normalizerAction F n x) = Sextet.fused x := by
    apply Bool.eq_iff_iff.mpr
    rw [← plane_fusion_iff_fused F hcount, ← plane_fusion_iff_fused F hcount,
      normalizerAction_element]
    have hc : IsConj (element F x) ((n : G) * element F x * (n : G)⁻¹) :=
      isConj_iff.mpr ⟨n, rfl⟩
    exact ⟨fun h => h.trans hc.symm, fun h => h.trans hc⟩
  have hz : normalizerAction F n 0 = 0 := by
    apply element_injective F
    rw [normalizerAction_element, element_zero]
    simp
  apply Bool.eq_iff_iff.mpr
  rw [Sextet.exceptional_iff, Sextet.exceptional_iff, hf]
  have hziff : normalizerAction F n x = 0 ↔ x = 0 := by
    conv_lhs => rw [← hz]
    exact (normalizerAction F n).injective.eq_iff
  exact and_congr hziff.not Iff.rfl

private theorem quotient_exceptional [Finite G]
    (hcount : (F.fusion F.plane).ncard = 45) (q : planeQuotient F) :
    quotientCodeAction F q ∈ Sextet.symmetryGroup := by
  induction q using QuotientGroup.induction_on with
  | H n => rw [quotientCodeAction_mk]; exact normalizer_exceptional F hcount n

/-- The literal quotient acts on the six-bit exceptional geometry. -/
def planeSextetRepresentation [Finite G] (hcount : (F.fusion F.plane).ncard = 45) :
    planeQuotient F →* Sextet.symmetryGroup :=
  (quotientCodeAction F).codRestrict _ (quotient_exceptional F hcount)

theorem planeSextetRepresentation_val [Finite G]
    (hcount : (F.fusion F.plane).ncard = 45) (q : planeQuotient F) :
    (planeSextetRepresentation F hcount q).val = quotientCodeAction F q := by
  unfold planeSextetRepresentation
  rfl

/-- The coordinate representation retains the proved faithful quotient action. -/
theorem planeSextetRepresentation_injective [Finite G]
    (hcount : (F.fusion F.plane).ncard = 45) :
    Function.Injective (planeSextetRepresentation F hcount) := by
  intro a b h
  exact quotientCodeAction_injective F (congrArg Subtype.val h)

/-- The six-point action descended through the original plane subgroup. -/
def planeSextetAction [Finite G] (hcount : (F.fusion F.plane).ncard = 45) :
    planeQuotient F →* Equiv.Perm (Fin 6) :=
  Sextet.action.comp (planeSextetRepresentation F hcount)

theorem planeSextetAction_apply [Finite G]
    (hcount : (F.fusion F.plane).ncard = 45) (q : planeQuotient F) :
    planeSextetAction F hcount q = Sextet.action (planeSextetRepresentation F hcount q) := by
  unfold planeSextetAction
  rfl

/-- The six-point quotient action describes conjugation of the literal
four-subgroups inside G. -/
theorem planeSextetAction_conjugation [Finite G]
    (hcount : (F.fusion F.plane).ncard = 45) (n : planeNormalizer F) (i : Fin 6) :
    (planeFour F i).map (MulAut.conj (n : G)).toMonoidHom =
      planeFour F (planeSextetAction F hcount (QuotientGroup.mk n) i) := by
  let f := planeSextetRepresentation F hcount (QuotientGroup.mk n)
  have hfx (x : Code) : f.val x = normalizerAction F n x := by
    change quotientCodeAction F (QuotientGroup.mk n) x = _
    rw [quotientCodeAction_mk]
  have hmem (x : Code) : normalizerAction F n x ∈
      Sextet.line (planeSextetAction F hcount (QuotientGroup.mk n) i) ↔ x ∈ Sextet.line i := by
    exact hfx x ▸ Sextet.action_mem_line f i x
  ext a
  constructor
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨normalizerAction F n x, (hmem x).mpr hx, normalizerAction_element F n x⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (normalizerAction F n).surjective y
    exact ⟨element F x, ⟨x, (hmem x).mp hy, rfl⟩, (normalizerAction_element F n x).symm⟩

/-- Apply the geometry to the original Mathieu three-space using exactly
the checked opposite marking. These are six distinct elementary four-groups
inside the original A₂. -/
theorem oriented_threeSpace_fours [Finite G] (hcounts : MathieuFusionOrientation F) :
    Function.Injective (planeFour (oppositeMarking F)) ∧
    (∀ i, planeFour (oppositeMarking F) i ≤ F.threeSpace ∧
      Nat.card (planeFour (oppositeMarking F) i) = 4 ∧
      IsElementaryAbelian 2 (planeFour (oppositeMarking F) i)) ∧
    (∀ a ∈ F.threeSpace, a ≠ 1 → ¬ IsConj z a →
      ∃! i : Fin 6, a ∈ planeFour (oppositeMarking F) i) := by
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2
  refine ⟨planeFour_injective _, fun i => ⟨?_, planeFour_card _ i, planeFour_elementary _ i⟩, ?_⟩
  · simpa only [oppositeMarking_plane] using planeFour_le (oppositeMarking F) i
  · intro a ha ha1 hza
    apply exists_unique_planeFour (oppositeMarking F) hc a _ ha1 hza
    simpa only [oppositeMarking_plane] using ha

private def quotientCongr (A B : Subgroup G) (h : A = B) :
    (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
      (normalizer (B : Set G) ⧸ B.subgroupOf (normalizer (B : Set G))) := by
  subst B
  exact MulEquiv.refl _

private theorem quotientCongr_mk (A B : Subgroup G) (h : A = B)
    (n : normalizer (A : Set G)) :
    quotientCongr A B h (QuotientGroup.mk n) =
      QuotientGroup.mk (⟨n, h ▸ n.property⟩ : normalizer (B : Set G)) := by
  subst B
  rfl

/-- The six-point action on the original oriented three-space quotient,
transported through the checked marking interchange. -/
def threeSpaceSextetAction [Finite G] (hcounts : MathieuFusionOrientation F) :
    threeSpaceQuotient F →* Equiv.Perm (Fin 6) :=
  (planeSextetAction (oppositeMarking F) (by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2)).comp
      (quotientCongr F.threeSpace (oppositeMarking F).plane
        (oppositeMarking_plane F).symm).toMonoidHom

/-- The quotient identification induced by the literal marking interchange. -/
def threeSpacePlaneQuotientEquiv :
    threeSpaceQuotient F ≃* planeQuotient (oppositeMarking F) :=
  quotientCongr F.threeSpace (oppositeMarking F).plane (oppositeMarking_plane F).symm

theorem threeSpacePlaneQuotientEquiv_mk (n : threeSpaceNormalizer F) :
    threeSpacePlaneQuotientEquiv F (QuotientGroup.mk n) =
      QuotientGroup.mk (⟨n, by
        change (n : G) ∈ normalizer ((oppositeMarking F).plane : Set G)
        rw [oppositeMarking_plane]
        exact n.property⟩ : planeNormalizer (oppositeMarking F)) := by
  unfold threeSpacePlaneQuotientEquiv
  exact quotientCongr_mk _ _ _ n

/-- Interchanging the marking preserves the six-point action, including its
original quotient map. -/
theorem threeSpaceSextetAction_eq [Finite G] (hcounts : MathieuFusionOrientation F) :
    threeSpaceSextetAction F hcounts =
      (planeSextetAction (oppositeMarking F) (by
        simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2)).comp
        (threeSpacePlaneQuotientEquiv F).toMonoidHom := by
  unfold threeSpaceSextetAction threeSpacePlaneQuotientEquiv
  rfl

/-- The original A₂ quotient map describes ambient conjugation on the six
actual four-subgroups. No abstract model identification is substituted. -/
theorem threeSpaceSextetAction_conjugation [Finite G]
    (hcounts : MathieuFusionOrientation F) (n : threeSpaceNormalizer F) (i : Fin 6) :
    (planeFour (oppositeMarking F) i).map (MulAut.conj (n : G)).toMonoidHom =
      planeFour (oppositeMarking F) (threeSpaceSextetAction F hcounts (QuotientGroup.mk n) i) := by
  change _ = planeFour (oppositeMarking F)
    (planeSextetAction (oppositeMarking F) _
      (quotientCongr _ _ _ (QuotientGroup.mk n)) i)
  rw [quotientCongr_mk]
  exact planeSextetAction_conjugation (oppositeMarking F) _
    (⟨(n : G), by
      change (n : G) ∈ normalizer ((oppositeMarking F).plane : Set G)
      rw [oppositeMarking_plane]
      exact n.property⟩ : planeNormalizer (oppositeMarking F)) i

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
