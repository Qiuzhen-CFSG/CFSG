module
public import Theory.Representation.PSL3Two.PointOffenders
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPoint
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.PSL3Two.DoubledSylowPoint

/-!
# Strict doubled-natural bounds on a point radical

Every subgroup A of a natural SL₃(2) point radical satisfies
|C_W(A)| |A| = 8. Fixed spaces multiply on W ⊕ W, so every nontrivial A
has |C_(W⊕W)(A)| |A| < 64. A Sylow-fixed nonzero doubled vector also
has a literal natural-point stabilizer, with no change to the action.

These are the finite model inputs for the Baumann normalization step in
Aschbacher–Smith 13.4.10(4), printed p.909. The proof uses the existing
point-radical subgroup calculation and transports it by inner conjugation.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace BinaryLinearThree
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private theorem pointCore_marking (v : Vector) (hv : v ≠ 0) :
    ∃ g : Group, (naturalPoint v).pCoreIn 2 = pointV.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := natural_transitive_nonzero ![1,0,0] v (by decide) hv
  have hstd : naturalPoint ![1,0,0] = pointParabolicSL := by
    rw [← Fano.stabilizer_flagPoint_SL]
    ext a
    change a • (![1,0,0] : Vector) = ![1,0,0] ↔ a • flagPoint = flagPoint
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  refine ⟨g,?_⟩
  rw [←hg,naturalPoint_action,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    hstd,MarkedProduct.pointParabolic_core]

/-- Every subgroup of a natural point radical has natural weight three. -/
theorem point_radical_fixed_card (v : Vector) (hv : v ≠ 0)
    (A : Subgroup Group) (hA : A ≤ (naturalPoint v).pCoreIn 2) :
    Nat.card (fixedSpace W A) * Nat.card A = 8 := by
  obtain ⟨g,hg⟩ := pointCore_marking v hv
  let E := A.comap (MulAut.conj g).toMonoidHom
  have hE : E ≤ pointV := by
    rw [hg] at hA
    exact (comap_mono hA).trans_eq (comap_map_eq_self_of_injective (MulAut.conj g).injective _)
  have hm : E.map (MulAut.conj g).toMonoidHom = A :=
    map_comap_eq_self_of_surjective (MulAut.conj g).surjective _
  have he : Nat.card (fixedSpace W E) = Nat.card (PointOffenders.fixed E) := by
    exact Nat.card_congr {
      toFun := fun x => ⟨x.val,fun a ha => x.property ⟨a,ha⟩⟩
      invFun := fun x => ⟨x.val,fun a => x.property a a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [←hm,←Nat.card_congr (fixedSpaceConjEquiv W E g).toEquiv,
    card_map_of_injective (MulAut.conj g).injective,he]
  exact PointOffenders.fixed_card_identity E hE

private def prodFixedEquiv (A : Subgroup Group) :
    fixedSpace (W.prod W) A ≃ (fixedSpace W A × fixedSpace W A) where
  toFun x := (⟨x.val.1,fun a => congrArg Prod.fst (x.property a)⟩,
    ⟨x.val.2,fun a => congrArg Prod.snd (x.property a)⟩)
  invFun x := ⟨(x.1.val,x.2.val),fun a => Prod.ext (x.1.property a) (x.2.property a)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A nontrivial subgroup of the point radical is not an offender on two
natural summands; the strict inequality retains both copies. -/
theorem doubled_point_radical_fixed_card_lt (v : Vector) (hv : v ≠ 0)
    (A : Subgroup Group) (hA : A ≤ (naturalPoint v).pCoreIn 2) (hne : A ≠ ⊥) :
    Nat.card (fixedSpace (W.prod W) A) * Nat.card A < 64 := by
  have he := point_radical_fixed_card v hv A hA
  have ha : 1 < Nat.card A := Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    ⟨Nat.card_pos.ne',fun hh => hne (card_eq_one.mp hh)⟩
  have hf : Nat.card (fixedSpace W A) < 8 := by nlinarith
  rw [Nat.card_congr (prodFixedEquiv A),Nat.card_prod]
  nlinarith

/-- A Sylow-fixed nonzero pair determines a literal natural point stabilizer. -/
theorem doubled_sylow_fixed_naturalPoint (P : Sylow 2 Group)
    (v : Vector × Vector) (hv : v ≠ 0)
    (hfix : ∀ a : P, (W.prod W) a.val v = v) :
    ∃ w : Vector, w ≠ 0 ∧
      (OrbitStabilizers.natural v.1 ⊓ OrbitStabilizers.natural v.2 : Subgroup Group) = naturalPoint w := by
  let F := fixedSpace W (P : Subgroup Group)
  have h1 : v.1 ∈ F := fun p => congrArg Prod.fst (hfix p)
  have h2 : v.2 ∈ F := fun p => congrArg Prod.snd (hfix p)
  have hz : OrbitStabilizers.natural (0 : Vector) = ⊤ := by
    ext g
    simp only [OrbitStabilizers.mem_natural,map_zero,mem_top]
  by_cases hv1 : v.1 = 0
  · refine ⟨v.2,fun hh => hv (Prod.ext hv1 hh),?_⟩
    rw [hv1,hz,top_inf_eq]
    ext g
    rw [OrbitStabilizers.mem_natural,mem_naturalPoint]
  by_cases hv2 : v.2 = 0
  · refine ⟨v.1,hv1,?_⟩
    rw [hv2,hz,inf_top_eq]
    ext g
    rw [OrbitStabilizers.mem_natural,mem_naturalPoint]
  let : Nontrivial F := ⟨⟨⟨v.1,h1⟩,0,fun hh => hv1 (congrArg Subtype.val hh)⟩⟩
  have hc : Nat.card F = 2 := le_antisymm (card_sylow_natural_fixed_le_two P)
    (Nat.succ_le_of_lt (Finite.one_lt_card (α := F)))
  have he := ((Nat.card_eq_two_iff' (0 : F)).mp hc).unique
    (show (⟨v.1,h1⟩ : F) ≠ 0 from fun hh => hv1 (congrArg Subtype.val hh))
    (show (⟨v.2,h2⟩ : F) ≠ 0 from fun hh => hv2 (congrArg Subtype.val hh))
  have he' : v.1 = v.2 := congrArg Subtype.val he
  refine ⟨v.2,hv2,?_⟩
  rw [he',inf_idem]
  ext g
  rw [OrbitStabilizers.mem_natural,mem_naturalPoint]
end BinaryLinearThree
