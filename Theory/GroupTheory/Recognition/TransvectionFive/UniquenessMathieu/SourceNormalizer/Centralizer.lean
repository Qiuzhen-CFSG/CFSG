module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Quotient
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Stabilizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Boundary

/-!
# The actual exceptional involution centralizer quotient

Restrict the faithful normalizer-quotient representation to the centralizer of
an original rectangle element. The kernel is exactly the rectangle, and the
image is the corresponding vector stabilizer. This isomorphism retains the
ambient conjugation formula on every marked coordinate. For an exceptional
nonzero vector, the faithful action on the other five four-groups is onto S₅.
Transport through the marking interchange gives the original I/A₂ clause.

The hypothesis excluding the distinguished conjugacy class is explicit here.
Its discharge for the source second involution class, and identification of
the solvable-residual fixed four-subgroup and its XI normalizer, remain with
the source assembly. This module does not assert the full 40.4(2) record.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

abbrev planeCentralizer (t : G) := planeNormalizer F ⊓ centralizer ({t} : Set G)

instance plane_normal_in_planeCentralizer (t : G) :
    (F.plane.subgroupOf (planeCentralizer F t)).Normal :=
  normal_subgroupOf_of_le_normalizer inf_le_left

omit [Finite G] in
/-- For t in the rectangle, the denominator in its centralizer quotient
is the entire rectangle. -/
theorem plane_le_planeCentralizer (t : G) (ht : t ∈ F.plane) :
    F.plane ≤ planeCentralizer F t := by
  refine le_inf le_normalizer ?_
  intro a ha
  have hc : a ∈ centralizer (F.plane : Set G) := (plane_centralizer_eq F).symm ▸ ha
  exact mem_centralizer_singleton_iff.mpr (hc t ht).symm

private def centralizerRepresentation (hc : (F.fusion F.plane).ncard = 45) (t : G) :
    planeCentralizer F t →* Sextet.symmetryGroup :=
  (planeSextetRepresentation F hc).comp
    ((QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))).comp (inclusion inf_le_left))

private theorem centralizerRepresentation_action (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (n : planeCentralizer F t) (x : Code) :
    element F ((centralizerRepresentation F hc t n).val x) =
      (n : G) * element F x * (n : G)⁻¹ := by
  change element F ((planeSextetRepresentation F hc
    (QuotientGroup.mk (⟨n, n.property.1⟩ : planeNormalizer F))).val x) = _
  rw [planeSextetRepresentation_val, quotientCodeAction_mk, normalizerAction_element]

private def centralizerPointHom (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) :
    planeCentralizer F t →* Sextet.pointFixer x :=
  (centralizerRepresentation F hc t).codRestrict _ (by
    intro n
    change (centralizerRepresentation F hc t n).val x = x
    apply element_injective F
    rw [centralizerRepresentation_action, hxt,
      mem_centralizer_singleton_iff.mp n.property.2, mul_inv_cancel_right])

private theorem centralizerPointHom_surjective (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) :
    Function.Surjective (centralizerPointHom F hc t x hxt) := by
  intro f
  obtain ⟨q, hq⟩ := planeSextetRepresentation_surjective F hc f.val
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (F.plane.subgroupOf (planeNormalizer F)) q
  have hn : (n : G) ∈ centralizer ({t} : Set G) := by
    have he := congrArg (fun f : Sextet.symmetryGroup => element F (f.val x)) hq
    rw [planeSextetRepresentation_val] at he
    change element F (quotientCodeAction F (QuotientGroup.mk n) x) = element F (f.val.val x) at he
    rw [quotientCodeAction_mk, normalizerAction_element,
      show f.val.val x = x from f.property, hxt] at he
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  refine ⟨⟨n, n.property, hn⟩, ?_⟩
  exact Subtype.ext hq

private theorem centralizerPointHom_ker (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) :
    F.plane.subgroupOf (planeCentralizer F t) = (centralizerPointHom F hc t x hxt).ker := by
  ext n
  change (n : G) ∈ F.plane ↔ centralizerPointHom F hc t x hxt n = 1
  have he : centralizerPointHom F hc t x hxt n = 1 ↔
      planeSextetRepresentation F hc
        (QuotientGroup.mk (⟨n, n.property.1⟩ : planeNormalizer F)) = 1 := Subtype.ext_iff
  rw [he, ← map_one (planeSextetRepresentation F hc),
    (planeSextetRepresentation_injective F hc).eq_iff, QuotientGroup.eq_one_iff]
  rfl

/-- The actual centralizer quotient, identified with the exceptional vector
stabilizer using its action on the original rectangle coordinates. -/
def planeCentralizerPointEquiv (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) :
    (planeCentralizer F t ⧸ F.plane.subgroupOf (planeCentralizer F t)) ≃*
      Sextet.pointFixer x :=
  QuotientGroup.liftEquiv (F.plane.subgroupOf (planeCentralizer F t))
    (φ := centralizerPointHom F hc t x hxt) (centralizerPointHom_surjective F hc t x hxt)
      (centralizerPointHom_ker F hc t x hxt)

/-- The centralizer quotient isomorphism retains ambient conjugation on
all original rectangle coordinates. -/
theorem planeCentralizerPointEquiv_action (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (x : Code) (hxt : element F x = t) (n : planeCentralizer F t) (y : Code) :
    element F ((planeCentralizerPointEquiv F hc t x hxt (QuotientGroup.mk n)).val.val y) =
      (n : G) * element F y * (n : G)⁻¹ := by
  unfold planeCentralizerPointEquiv
  rw [QuotientGroup.liftEquiv_mk]
  exact centralizerRepresentation_action F hc t n y

/-- The source involution centralizer quotient is S₅ whenever its marked
coordinate belongs to the exceptional 18-element orbit. -/
theorem plane_centralizer_quotient (hc : (F.fusion F.plane).ncard = 45)
    (t : G) (ht : t ∈ F.plane) (ht1 : t ≠ 1) (hzt : ¬ IsConj z t) :
    Nonempty ((↥(planeNormalizer F ⊓ centralizer ({t} : Set G)) ⧸
      F.plane.subgroupOf (planeNormalizer F ⊓ centralizer ({t} : Set G))) ≃*
      Equiv.Perm (Fin 5)) := by
  obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨t, ht⟩
  have hxt : element F x = t := congrArg Subtype.val hx
  have hex : Sextet.exceptional x = true := by
    apply (Sextet.exceptional_iff x).mpr
    refine ⟨fun he => ht1 (hxt.symm.trans (he ▸ element_zero F)), ?_⟩
    have hh : Sextet.fused x ≠ true := fun hh => hzt (hxt ▸ (plane_fusion_iff_fused F hc x).mpr hh)
    cases h : Sextet.fused x <;> simp_all
  obtain ⟨i, hi, _⟩ := Sextet.exceptional_unique_line x hex
  let e : planeQuotient F ≃* Sextet.symmetryGroup :=
    MulEquiv.ofBijective (planeSextetRepresentation F hc)
      ⟨planeSextetRepresentation_injective F hc, planeSextetRepresentation_surjective F hc⟩
  have hcard : Nat.card Sextet.symmetryGroup = 2160 :=
    (Nat.card_congr e.toEquiv).symm.trans (planeSextet_quotient_card F hc)
  exact ⟨(planeCentralizerPointEquiv F hc t x hxt).trans
    (Sextet.pointFixerEquiv hcard x hex i hi)⟩

private instance centralizerQuotient_normal (A : Subgroup G) (t : G) :
    (A.subgroupOf (normalizer (A : Set G) ⊓ centralizer ({t} : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer inf_le_left

private def centralizerQuotientCongr (A B : Subgroup G) (h : A = B) (t : G) :
    (↥(normalizer (A : Set G) ⊓ centralizer ({t} : Set G)) ⧸
      A.subgroupOf (normalizer (A : Set G) ⊓ centralizer ({t} : Set G))) ≃*
    (↥(normalizer (B : Set G) ⊓ centralizer ({t} : Set G)) ⧸
      B.subgroupOf (normalizer (B : Set G) ⊓ centralizer ({t} : Set G))) := by
  subst B
  exact MulEquiv.refl _

/-- The literal source I/A₂ has symmetric-five type. The hypothesis says
that t lies outside the distinguished involution class; the remaining source
fusion argument must supply it for `SecondInvolutionClass`. -/
theorem involutionCentralizer_quotient_of_not_fused
    (hcounts : MathieuFusionOrientation F) (t : G) (ht : t ∈ F.threeSpace)
    (ht1 : t ≠ 1) (hzt : ¬ IsConj z t) :
    Nonempty (involutionCentralizerQuotient F t ≃* Equiv.Perm (Fin 5)) := by
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2
  have h := plane_centralizer_quotient (oppositeMarking F) hc t
    (by simpa only [oppositeMarking_plane] using ht) ht1 hzt
  obtain ⟨e⟩ := h
  exact ⟨(centralizerQuotientCongr F.threeSpace (oppositeMarking F).plane
    (oppositeMarking_plane F).symm t).trans e⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
