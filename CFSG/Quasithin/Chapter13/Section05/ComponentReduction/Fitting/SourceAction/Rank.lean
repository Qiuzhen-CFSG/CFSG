module

public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupTheory.ConjugationLocalGeometry
public import Mathlib.FieldTheory.Finiteness
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Representation
public import CFSG.Quasithin.Chapter13.Section05.LocalGeometry.NonabelianClosure

/-!
# Rank two of the literal quotient action

F.9.5(2) is retained as a universal commutator-image equality on U_H/V₁.
The actual conjugation formula identifies that image with the linear moved
space. An order-two actor has equal moved dimension and fixed codimension.
Since |V|=16, |V:V₊|=2 and |V₁|=2, the seed image has order four.
Thus the fixed codimension is two, without assuming any local rank claim.

The order-sixteen hypothesis expresses m(V)=4 for the elementary abelian
source V. The universal F.9.5 input remains with qt-f09-rank-one/qt-f-09;
its final source application belongs to qt-13-05.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.5(2), printed p.319; 13.5.20, printed p.923.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
variable {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]

theorem fixedCodim_eq_moved_finrank_of_card_two [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) J W) (A : Subgroup J) (hc : Nat.card A = 2) :
    fixedCodim ρ A = Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) := by
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  have hA : A = zpowers (a : J) := by
    apply le_antisymm _ (zpowers_le.mpr a.property)
    intro x hx
    by_cases he : x = 1
    · simp [he]
    · have hxa : x = (a : J) := congrArg Subtype.val (ha ⟨x, hx⟩ (fun e => he (congrArg Subtype.val e)))
      rw [hxa]
      exact mem_zpowers _
  have hm : subspaceCommutator ρ ⊤ A = LinearMap.range (ρ a - LinearMap.id) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, w, _, rfl⟩
      by_cases he : x = 1
      · simp only [he, map_one, Module.End.one_apply, sub_self]
        exact Submodule.zero_mem _
      · have hxa : x = (a : J) := congrArg Subtype.val (ha ⟨x, hx⟩ (fun e => he (congrArg Subtype.val e)))
        exact ⟨w, by simp [hxa]⟩
    · rintro _ ⟨w, rfl⟩
      exact Submodule.subset_span ⟨a, a.property, w, Submodule.mem_top, rfl⟩
  rw [hm]
  calc
    fixedCodim ρ A = fixedCodim ρ (zpowers (a : J)) := congrArg (fixedCodim ρ) hA
    _ = _ := fixedCodim_zpowers_eq_displacement_rank ρ a

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
open Section08.Source
variable {G : Type*} [Group G] [Finite G]

/-- The universally quantified U_H clause of F.9.5(2), in the literal
quotient U_H/V₁. This asserts equality of subgroups, not their dimension. -/
def F95Two : Prop :=
  ∀ (D : ChapterF.Section09.Setup G) (h : D.Hypothesis),
    D.Vplus.relIndex D.V = 2 → starImage D.H D.V ≠ ⊥ →
    let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
    ((⁅D.UH, D.V⁆).subgroupOf D.UH).map (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)) =
      (D.Vplus.subgroupOf D.UH).map (QuotientGroup.mk' (D.V₁.subgroupOf D.UH))

variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
include h

theorem seed_quotient_card (hindex : D.Vplus.relIndex D.V = 2)
    (hcard : Nat.card D.V = 16) [(D.V₁.subgroupOf D.UH).Normal] :
    Nat.card ((D.Vplus.subgroupOf D.UH).map
      (QuotientGroup.mk' (D.V₁.subgroupOf D.UH))) = 4 := by
  rw [← relIndex_ker, QuotientGroup.ker_mk',
    relIndex_subgroupOf (show D.Vplus ≤ D.UH from le_conjugateSpanBy D.Vplus D.H)]
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) D.Vplus D.V bot_le h.plus_le
  rw [relIndex_bot_left, relIndex_bot_left, hindex, hcard] at hc
  have hz := relIndex_mul_relIndex (⊥ : Subgroup G) D.V₁ D.Vplus bot_le h.point_lt.le
  rw [relIndex_bot_left, relIndex_bot_left, h.point_card] at hz
  omega

section
variable [(D.V₁.subgroupOf D.UH).Normal]
  [IsElementaryAbelian 2 (Quotient (D := D))]

theorem moved_space_eq_seed (hsource : F95Two (G := G))
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH) :
    subspaceCommutator (representation h) ⊤ (starImage D.H D.V) =
      quotientImage D.UH (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)) D.Vplus := by
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
  let f := (QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion h.V_le_H)
  have hr : f.range = starImage D.H D.V := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact mem_map_of_mem _ v.property
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have ht : quotientImage D.UH q D.UH = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) w.toMul
    exact mem_map_of_mem q u.property
  have he := quotientImage_commutator (representation h) D.UH D.UH D.V
    (h.V_le_H.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)) le_rfl f q
    (QuotientGroup.mk'_surjective _) (fun x u => representation_apply h (inclusion h.V_le_H x) u)
  rw [ht, hr] at he
  rw [← he]
  have hn : starImage D.H D.V ≠ ⊥ := by
    intro hb
    have hc := LocalGeometry.star_V_card_two h hindex hU
    rw [hb] at hc
    simp at hc
  exact congrArg (fun A => AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup A))
    (hsource D h hindex hn)

theorem fixedCodim_two (hsource : F95Two (G := G))
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16) :
    fixedCodim (representation h) (starImage D.H D.V) = 2 := by
  rw [fixedCodim_eq_moved_finrank_of_card_two (representation h) _
    (LocalGeometry.star_V_card_two h hindex hU), moved_space_eq_seed h hsource hindex hU]
  let P := quotientImage D.UH (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)) D.Vplus
  have hc : Nat.card P = 4 := (binarySubgroup_card P).symm.trans
    (seed_quotient_card h hindex hcard)
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
  rw [Nat.card_zmod, hc] at hd
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hd.symm

end

/-- For the original elementary abelian V, the order-sixteen formulation
is exactly the source binary rank-four hypothesis. -/
theorem card_V_iff_rank_four :
    let := h.elementary
    Nat.card D.V = 16 ↔ Module.finrank (ZMod 2) (Additive D.V) = 4 := by
  let := h.elementary
  have hc : Nat.card D.V = 2 ^ Module.finrank (ZMod 2) (Additive D.V) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.V)
  rw [hc]
  constructor
  · intro he
    exact Nat.pow_right_injective (by decide : 2 ≤ 2)
      (show 2 ^ Module.finrank (ZMod 2) (Additive D.V) = 2 ^ 4 from he)
  · intro he
    rw [he]
    decide

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
