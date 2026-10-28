module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleStructure.NaturalRadicals
public import Theory.SpecificGroups.SL2.NaturalFixedIndex

/-!
# The middle root is a full field line

In a split triangle the middle root has order q and centralizes the simple
root at either endpoint. Under any equivariant natural SL₂ coordinates it
therefore lies in the fixed subgroup of a nontrivial matrix group. That
fixed subgroup has order at most q, so equality holds. Scalar multiples
of any nonzero fixed vector give exactly this middle root.

This includes q=2 and retains the supplied rank-one marking and literal
conjugation action. The triangle affine-incidence consumer uses the result
to identify its marked pencil over one field.
Source: Fong--Seitz I (3E), printed p.14, and the projective-plane argument
underlying DGS (10.5), printed p.156.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure
open RootCoordinates HexagonStructure QuadrangleStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 3)
  (hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (hE : ∀ i, IsElementaryAbelian 2 (simpleRoot Q split i))
  (i j : Fin 2) (hij : i ≠ j) (μ : rankOne Q split i ≃* SL(2,F))
  (c : simpleRemainder Q split i ≃* Multiplicative (Fin 2 → F))
  (hc : ∀ r v, (c (radicalAction Q split i (hV i) r v)).toAdd =
    Matrix.mulVec (μ r).val (c v).toAdd)

include hm hV hE hij μ hc in
theorem radical_intersection_field_line :
    ∃ v₀ : Fin 2 → F, v₀ ≠ 0 ∧ ∀ x : simpleRemainder Q split i,
      (x : X ⧸ Q.D) ∈ simpleRemainder Q split j ↔ ∃ a : F, (c x).toAdd = a • v₀ := by
  let := remainder_elementary Q split hm hV hE j
  let M := simpleRemainder Q split i ⊓ simpleRemainder Q split j
  let I := M.subgroupOf (simpleRemainder Q split i)
  let W := I.map c.toMonoidHom
  let B := ((simpleRoot Q split i).subgroupOf (rankOne Q split i)).map μ.toMonoidHom
  let V := Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed B
  have hBF : B ≠ ⊥ := by
    intro he
    have hh := (map_injective μ.injective) (he.trans (Subgroup.map_bot μ.toMonoidHom).symm)
    have ha := congrArg (fun K : Subgroup (rankOne Q split i) => K.map (rankOne Q split i).subtype) hh
    rw [map_subgroupOf_eq_of_le (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left),Subgroup.map_bot] at ha
    exact simpleRoot_ne_bot Q split i ha
  have hWV : W ≤ V := by
    rintro _ ⟨x,hx,rfl⟩ b ⟨r,hr,rfl⟩
    have hri := (opposite_roots_le_remainder Q split i j hij).1 hr
    have he : (r : X ⧸ Q.D)*(x : X ⧸ Q.D) = (x : X ⧸ Q.D)*(r : X ⧸ Q.D) :=
      congrArg Subtype.val (mul_comm (⟨r,hri⟩ : simpleRemainder Q split j) ⟨x,hx.2⟩)
    have hact : radicalAction Q split i (hV i) r x = x := by
      apply Subtype.ext
      rw [radicalAction_apply,he,mul_inv_cancel_right]
    exact (hc r x).symm.trans (congrArg (fun z => (c z).toAdd) hact)
  have hI : Nat.card I = Nat.card F := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show M ≤ simpleRemainder Q split i from inf_le_left)).toEquiv]
    change Nat.card (simpleRemainder Q split i ⊓ simpleRemainder Q split j : Subgroup (X ⧸ Q.D)) = _
    rw [radical_intersection Q split hm i j hij]
    simp only [rootAt,card_rightConjugate]
    exact GTwoSource.simpleRoot_card Q split i (hV i)
      ((localGroupEquivOfCenterless Q split i (hV i) μ
        Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
          Atlas.RankOneFieldAutomorphisms.slEquivPSL)
  have hW : Nat.card W = Nat.card F := (card_map_of_injective c.injective).trans hI
  have hWVeq : W = V := eq_of_le_of_card_ge hWV
    ((Theory.SpecificGroups.SL2.NaturalFixedIndex.card_fixed_le hBF).trans_eq hW.symm)
  have hWne : W ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hW
    exact Finite.one_lt_card.ne hW
  obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hz0 : z.val.toAdd ≠ 0 := fun he => hz (Subtype.ext he)
  let f : F → W := fun a => ⟨Multiplicative.ofAdd (a • z.val.toAdd),by
    apply hWVeq.ge
    intro b hb
    change Matrix.mulVec b.val (a • z.val.toAdd) = a • z.val.toAdd
    rw [Matrix.mulVec_smul]
    exact congrArg (a • ·) (hWV z.property b hb)⟩
  have hf : Function.Injective f := fun a b he =>
    smul_left_injective F hz0 (congrArg (fun x : W => x.val.toAdd) he)
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hW.symm⟩).2
  refine ⟨z.val.toAdd,hz0,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := hs ⟨c x,mem_map_of_mem c.toMonoidHom ⟨x.property,hx⟩⟩
    exact ⟨a,(congrArg (fun x : W => x.val.toAdd) ha).symm⟩
  · rintro ⟨a,ha⟩
    have hw : c x ∈ W := ha ▸ (f a).property
    obtain ⟨y,hy,he⟩ := hw
    exact (c.injective he) ▸ hy.2
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure
