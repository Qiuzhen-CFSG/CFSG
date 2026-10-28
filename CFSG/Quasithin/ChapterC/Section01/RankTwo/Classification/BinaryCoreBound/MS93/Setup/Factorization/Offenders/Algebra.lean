module

public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index

/-!
# Quotient actions and the critical-pair offender comparison

For a subgroup N centralizing Y and normal in A, conjugation gives an
actual action of A/N on the literal subgroup Y. Its native fixed subgroup
maps to Y intersect C(A), and restriction through an overgroup quotient
preserves this action. All normality assertions are relative.

For an elementary endpoint layer E, the second isomorphism theorem
identifies (E N)/N with E/(E intersect N). When the edge centralizer is N,
a favorable displacement comparison makes E N an offender preimage.
These lemmas do not require the ambient group to be finite.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of 2.2(vi), printed p.857.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders
variable {G : Type*} [Group G]

noncomputable def conjugation (A Y : Subgroup G) (h : A ≤ normalizer (Y : Set G)) :
    A →* MulAut Y := by
  letI := conjMulDistribMulActionOfLeNormalizer A Y h
  exact MulDistribMulAction.toMulAut A Y

noncomputable def quotientConjugation (A N Y : Subgroup G)
    (hn : (N.subgroupOf A).Normal) (h : A ≤ normalizer (Y : Set G))
    (hc : N ≤ centralizer (Y : Set G)) :
    letI := hn
    A ⧸ N.subgroupOf A →* MulAut Y := by
  letI := hn
  refine QuotientGroup.lift _ (conjugation A Y h) ?_
  intro n hn
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change (n : G) * (y : G) * (n : G)⁻¹ = y
  have he : (y : G) * (n : G) = (n : G) * (y : G) := hc hn y y.property
  rw [← he, mul_assoc, mul_inv_cancel, mul_one]

theorem quotientConjugation_apply (A N Y : Subgroup G)
    (hn : (N.subgroupOf A).Normal) (h : A ≤ normalizer (Y : Set G))
    (hc : N ≤ centralizer (Y : Set G)) (x : A) (y : Y) :
    letI := hn
    (quotientConjugation A N Y hn h hc (QuotientGroup.mk' _ x) y : G) =
      (x : G) * (y : G) * (x : G)⁻¹ := rfl

/-- The native fixed subgroup of the action supplied by an automorphism homomorphism. -/
def fixedSubgroup {B : Type*} [Group B] (Y : Subgroup G) (ρ : B →* MulAut Y) :
    Subgroup Y :=
  letI := MulDistribMulAction.compHom Y ρ
  FixedPoints.subgroup B Y

theorem quotientConjugation_fixed (A N Y : Subgroup G)
    (hn : (N.subgroupOf A).Normal) (h : A ≤ normalizer (Y : Set G))
    (hc : N ≤ centralizer (Y : Set G)) :
    (fixedSubgroup Y (quotientConjugation A N Y hn h hc)).map Y.subtype =
      Y ⊓ centralizer (A : Set G) := by
  ext y
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, fun a ha => ?_⟩
    have he := congrArg Subtype.val (hy (QuotientGroup.mk' _ ⟨a, ha⟩))
    change a * (y : G) * a⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  · rintro ⟨hy, hc'⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    intro b
    induction b using QuotientGroup.induction_on with
    | H x =>
      apply Subtype.ext
      change (x : G) * y * (x : G)⁻¹ = y
      rw [hc' x x.property, mul_assoc, mul_inv_cancel, mul_one]

private theorem centralizer_join (E N : Subgroup G) :
    centralizer ((E ⊔ N : Subgroup G) : Set G) = centralizer (E : Set G) ⊓ centralizer (N : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show E ≤ E ⊔ N from le_sup_left))
      (centralizer_le (show N ≤ E ⊔ N from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

noncomputable def displacement (Y E : Subgroup G) : ℕ := (centralizer (E : Set G)).relIndex Y

private theorem displacement_join (Y E N : Subgroup G) (h : N ≤ centralizer (Y : Set G)) :
    displacement Y (E ⊔ N) = displacement Y E := by
  unfold displacement
  rw [centralizer_join, ← inf_relIndex_right, inf_assoc,
    inf_of_le_right (le_centralizer_iff.mp h), inf_relIndex_right]

theorem displacement_map {G' : Type*} [Group G'] (e : G ≃* G') (Y E : Subgroup G) :
    displacement (Y.map e.toMonoidHom) (E.map e.toMonoidHom) = displacement Y E := by
  have hc : (centralizer (E.map e.toMonoidHom : Set G')).comap e.toMonoidHom =
      centralizer (E : Set G) := by
    ext x
    constructor
    · intro hx y hy
      apply e.injective
      rw [map_mul, map_mul]
      exact hx (e y) (mem_map.mpr ⟨y, hy, rfl⟩)
    · intro hx y hy
      obtain ⟨z, hz, rfl⟩ := hy
      change e z * e x = e x * e z
      rw [← map_mul, ← map_mul, hx z hz]
  unfold displacement
  rw [← relIndex_comap, hc]

private theorem join_quotient_elementary (E N : Subgroup G)
    (hEN : E ≤ normalizer (N : Set G)) [IsElementaryAbelian 2 E] :
    let := normal_subgroupOf_sup_of_le_normalizer hEN
    IsElementaryAbelian 2 ((E ⊔ N : Subgroup G) ⧸ N.subgroupOf (E ⊔ N)) := by
  let := normal_subgroupOf_of_le_normalizer hEN
  let := normal_subgroupOf_sup_of_le_normalizer hEN
  exact IsElementaryAbelian.of_surjective
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hEN).toMonoidHom
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hEN).surjective

private theorem relIndex_join (E N : Subgroup G) (hEN : E ≤ normalizer (N : Set G)) :
    N.relIndex (E ⊔ N) = N.relIndex E := by
  let := normal_subgroupOf_of_le_normalizer hEN
  let := normal_subgroupOf_sup_of_le_normalizer hEN
  exact Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hEN).toEquiv.symm

/-- An offender on the literal layer, with its relative kernel. -/
structure Witness (N T Y : Subgroup G) where
  A : Subgroup G
  kernel_lt : N < A
  le_edge : A ≤ T
  normal : (N.subgroupOf A).Normal
  elementary : letI := normal; IsElementaryAbelian 2 (A ⧸ N.subgroupOf A)
  normalized : A ≤ normalizer (Y : Set G)
  centralizes : N ≤ centralizer (Y : Set G)
  bound : (Y ⊓ centralizer (A : Set G)).relIndex Y ≤ N.relIndex A

noncomputable def Witness.action {N T Y : Subgroup G} (w : Witness N T Y) :
    letI := w.normal
    w.A ⧸ N.subgroupOf w.A →* MulAut Y :=
  quotientConjugation w.A N Y w.normal w.normalized w.centralizes

theorem Witness.action_apply {N T Y : Subgroup G} (w : Witness N T Y)
    (x : w.A) (y : Y) :
    letI := w.normal
    (w.action (QuotientGroup.mk' _ x) y : G) = (x : G) * y * (x : G)⁻¹ :=
  quotientConjugation_apply _ _ _ _ _ _ _ _

theorem Witness.action_fixed {N T Y : Subgroup G} (w : Witness N T Y) :
    letI := w.normal
    (fixedSubgroup Y w.action).map Y.subtype = Y ⊓ centralizer (w.A : Set G) :=
  quotientConjugation_fixed _ _ _ _ _ _

/-- The quotient is nontrivial, rather than merely an elementary group of order one. -/
theorem Witness.quotient_nontrivial {N T Y : Subgroup G} (w : Witness N T Y) :
    Nontrivial (w.A ⧸ N.subgroupOf w.A) := by
  apply QuotientGroup.nontrivial_iff.mpr
  intro he
  apply w.kernel_lt.not_ge
  intro x hx
  have hh : (⟨x, hx⟩ : w.A) ∈ N.subgroupOf w.A := by rw [he]; trivial
  exact hh

/-- The order of the actor quotient is exactly the relative index in the bound. -/
theorem Witness.quotient_card {N T Y : Subgroup G} (w : Witness N T Y) :
    Nat.card (w.A ⧸ N.subgroupOf w.A) = N.relIndex w.A := rfl

/-- The displayed centralizer bound is the native fixed-subgroup index bound. -/
theorem Witness.fixed_index_le_card {N T Y : Subgroup G} (w : Witness N T Y) :
    letI := w.normal
    (fixedSubgroup Y w.action).index ≤ Nat.card (w.A ⧸ N.subgroupOf w.A) := by
  let := w.normal
  have hi := relIndex_map_map_of_injective (fixedSubgroup Y w.action)
    (⊤ : Subgroup Y) Y.subtype_injective
  rw [relIndex_top_right, ← MonoidHom.range_eq_map, range_subtype] at hi
  rw [← hi, w.action_fixed, w.quotient_card]
  exact w.bound

/-- The natural inclusion of the actor quotient into an overgroup quotient. -/
def quotientInclusion (A S N : Subgroup G) (hAS : A ≤ S)
    (hnA : (N.subgroupOf A).Normal) (hnS : (N.subgroupOf S).Normal) :
    letI := hnA; letI := hnS
    A ⧸ N.subgroupOf A →* S ⧸ N.subgroupOf S := by
  letI := hnA
  letI := hnS
  exact QuotientGroup.map _ _ (inclusion hAS) (fun _ hx => hx)

theorem quotientInclusion_injective (A S N : Subgroup G) (hAS : A ≤ S)
    (hnA : (N.subgroupOf A).Normal) (hnS : (N.subgroupOf S).Normal) :
    Function.Injective (quotientInclusion A S N hAS hnA hnS) := by
  let := hnA
  let := hnS
  intro x y
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      intro he
      apply QuotientGroup.eq.mpr
      exact (QuotientGroup.eq (s := N.subgroupOf S)).mp he

/-- Restriction along that inclusion agrees with the constructed offender action. -/
theorem quotientConjugation_restrict (A S N Y : Subgroup G) (hAS : A ≤ S)
    (hnA : (N.subgroupOf A).Normal) (hnS : (N.subgroupOf S).Normal)
    (hSY : S ≤ normalizer (Y : Set G)) (hNY : N ≤ centralizer (Y : Set G)) :
    letI := hnA; letI := hnS
    (quotientConjugation S N Y hnS hSY hNY).comp
      (quotientInclusion A S N hAS hnA hnS) =
        quotientConjugation A N Y hnA (hAS.trans hSY) hNY := by
  let := hnA
  let := hnS
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rfl

theorem favorable (N T Y E : Subgroup G)
    (hNT : N ≤ T) (hET : E ≤ T)
    (hTN : T ≤ normalizer (N : Set G)) (hTY : T ≤ normalizer (Y : Set G))
    (hNY : N ≤ centralizer (Y : Set G))
    (hC : T ⊓ centralizer (Y : Set G) = N) (hne : ¬ E ≤ N)
    [IsElementaryAbelian 2 E]
    (hcomp : displacement Y E ≤ displacement E Y) : Nonempty (Witness N T Y) := by
  have hEN := hET.trans hTN
  have he : E ⊓ centralizer (Y : Set G) = E ⊓ N := by
    rw [← hC, ← inf_assoc, inf_of_le_left hET]
  have hi : displacement E Y = N.relIndex E := by
    unfold displacement
    rw [← inf_relIndex_left E, he, inf_relIndex_left]
  refine ⟨{
    A := E ⊔ N
    kernel_lt := lt_iff_le_not_ge.mpr ⟨le_sup_right, fun h => hne (le_sup_left.trans h)⟩
    le_edge := sup_le hET hNT
    normal := normal_subgroupOf_sup_of_le_normalizer hEN
    elementary := join_quotient_elementary E N hEN
    normalized := (sup_le hET hNT).trans hTY
    centralizes := hNY
    bound := ?_ }⟩
  rw [inf_relIndex_left, relIndex_join E N hEN]
  change displacement Y (E ⊔ N) ≤ _
  rw [displacement_join Y E N hNY]
  exact hcomp.trans_eq hi

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Offenders
