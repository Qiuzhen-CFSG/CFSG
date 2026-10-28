module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Dimensions
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Involution displacement in the outer-extension case

The supplied natural isomorphism and the disjoint decomposition of Z give
|Z| = 8|C|. The literal relative index [X:Z] = 2 therefore gives |X| = 16|C|.
Here C is identified with the full fixed space of the actual marked X action,
using layerAction_fixed_iff. Thus that action has full fixed-space codimension
four. The dual three-involution bound forces every involution to displace
at least two dimensions.

This argument uses the actual extension and conjugation action without
choosing a splitting of X or changing the source quotient marking.
Source: Meierfrankenfeld–Stellmacher (1993), (3.2)(v), printed pp.863,877.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private noncomputable def fixedEquiv (source : LocalSource L R) :
    letI := X_elementary R (alpha R)
    fixedSpace (Offenders.linearize (xAction source)) ⊤ ≃ fixedPart R := by
  let := X_elementary R (alpha R)
  let ρ := Offenders.linearize (xAction source)
  have hfix (v : X R (alpha R)) := layerAction_fixed_iff source (X R (alpha R))
    (X_normalized R (alpha R)) (Q_le_centralizer_X R (alpha R)) v
  exact {
    toFun := fun v => ⟨v.val.toMul, v.val.toMul.property, (hfix v.val.toMul).mp
      (fun g => congrArg Additive.toMul (v.property ⟨g, mem_top g⟩))⟩
    invFun := fun c => ⟨Additive.ofMul ⟨c.val, c.property.1⟩, fun g =>
      congrArg Additive.ofMul ((hfix ⟨c.val, c.property.1⟩).mpr c.property.2 g.val)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

omit [Finite M] in
private theorem outerExtension_card (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source) :
    Nat.card (X R (alpha R)) = 16 * Nat.card (fixedPart R) := by
  obtain ⟨⟨q⟩, hZ, hd, hi⟩ := h
  let := X_elementary R (alpha R)
  have hZX := geometry.omega_bound (alpha R) rfl hb
  have hUX := (U_le_Z (alpha R)).trans hZX
  have hn : U R (alpha R) ≤ normalizer (fixedPart R : Set (FreeAmalgam R)) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro u hu c hc
    exact congrArg Subtype.val (mul_comm (⟨c, hc.1⟩ : X R (alpha R)) ⟨u, hUX hu⟩)
  have huc : Nat.card (U R (alpha R)) = 8 := by
    rw [Nat.card_congr q.equiv.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hzc : Nat.card (Z R (alpha R)) = Nat.card (fixedPart R) * 8 := by
    rw [hZ, card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd, huc]
  have hc := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R (alpha R)) (X R (alpha R)) bot_le hZX
  rw [relIndex_bot_left, relIndex_bot_left, hi, hzc] at hc
  omega

/-- The index-two outer extension has fixed-space codimension four on the
literal marked X action. The fixed part is its actual full invariant subgroup. -/
theorem outerExtension_fixedCodim_top (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source) :
    letI := X_elementary R (alpha R)
    fixedCodim (Offenders.linearize (xAction source)) ⊤ = 4 := by
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  let ρ := Offenders.linearize (xAction source)
  have hc := outerExtension_card source geometry hb h
  have hX := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X R (alpha R)))
  have hF := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ ⊤)
  rw [Nat.card_zmod] at hX hF
  change Nat.card (X R (alpha R)) = _ at hX
  rw [← Nat.card_congr (fixedEquiv source)] at hc
  rw [hX, hF, show 16 = 2 ^ 4 by decide, ← pow_add] at hc
  have he := (Nat.pow_right_injective (by decide : 1 < 2)) hc
  have hd := fixedCodim_add_finrank ρ ⊤
  change fixedCodim ρ ⊤ = 4
  omega

theorem outerExtension_involutionBound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h : OuterExtension source) : InvolutionBound source := by
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  intro a ha hne
  have hlow := outerExtension_fixedCodim_top source geometry hb h
  have hhigh := fixedCodim_top_le_three_mul (Offenders.linearize (xAction source)) a ha hne
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Models
