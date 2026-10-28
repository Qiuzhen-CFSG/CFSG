module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TriangleStructure.Radicals
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearPlacement
public import Theory.Representation.RankOne.QuadraticRecognition.SmallFixedSeed

/-!
# Natural coordinates on the whole radical of a split triangle

The middle root is fixed by the canonical root Sylow, contains every
Sylow displacement, and together with its reflection generates the whole
radical. Its order is the defining field order. The small fixed-seed
recognition theorem therefore constructs a single natural SL₂ module.
The supplied rank-one marking and actual conjugation action are retained.

Both orientations and the field of order two are included. Neither
irreducibility nor perfectness is assumed. This supplies the natural-core
input for the projective-plane identification in Fong--Seitz I (3E),
printed p.14, through the elementary root geometry and DGS (5.12), (10.5),
printed pp.113--114,156. It does not assert the final A₂ comparison.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative Pointwise commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure
open RootCoordinates HexagonStructure QuadrangleStructure
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 3)
  (hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (hE : ∀ i, IsElementaryAbelian 2 (simpleRoot Q split i))
  (i : Fin 2) (μ : rankOne Q split i ≃* SL(2,F))
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The actual whole triangle radical is a natural module, including the binary field. -/
theorem radical_natural_coordinates :
    let := remainder_elementary Q split hm hV hE i
    ∃ c : Additive (simpleRemainder Q split i) ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ r v, c (elementaryRepresentation (p := 2) (radicalAction Q split i (hV i)) r v) =
        Matrix.mulVec ((μ r).val) (c v) := by
  let := remainder_elementary Q split hm hV hE i
  let j : Fin 2 := 1-i
  have hij : i ≠ j := by dsimp [j]; omega
  let := remainder_elementary Q split hm hV hE j
  let V := simpleRemainder Q split i
  let M := V ⊓ simpleRemainder Q split j
  have hM : M = rootAt Q split j (Q.simple i) :=
    (radical_intersection Q split hm i j hij).trans (cross_root_eq Q split hm i j hij)
  let C : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (M.subgroupOf V).toAddSubgroup
  let ρ := elementaryRepresentation (p := 2) (radicalAction Q split i (hV i))
  let ν := μ
  let μlocal := (localGroupEquivOfCenterless Q split i (hV i) μ
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL
  let σ := ρ.comp ν.symm.toMonoidHom
  obtain ⟨T,hT⟩ := simpleRoot_sylow_of_linear Q split i (hV i) ν
  let S := T.mapSurjective (f := ν.toMonoidHom) ν.surjective
  have hroot (a : SL(2,F)) (ha : a ∈ (S : Subgroup SL(2,F))) :
      (ν.symm a : X ⧸ Q.D) ∈ simpleRoot Q split i := by
    obtain ⟨r,hr,rfl⟩ := ha
    rw [hT] at hr
    change (r : X ⧸ Q.D) ∈ simpleRoot Q split i at hr
    simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] using hr
  have hfix : C ≤ BinaryOffender.fixedSpace σ S := by
    intro v hv a
    have ha := (opposite_roots_le_remainder Q split i j hij).1 (hroot a a.property)
    have hvj : (v.toMul : X ⧸ Q.D) ∈ simpleRemainder Q split j := hv.2
    have he : (ν.symm a : X ⧸ Q.D) * (v.toMul : X ⧸ Q.D) =
        (v.toMul : X ⧸ Q.D) * (ν.symm a : X ⧸ Q.D) :=
      congrArg Subtype.val (mul_comm
        (⟨_,ha⟩ : simpleRemainder Q split j) ⟨_,hvj⟩)
    change Additive.ofMul (radicalAction Q split i (hV i) (ν.symm a) v.toMul) = v
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((radicalAction Q split i (hV i) (ν.symm a) v.toMul : V) : X ⧸ Q.D) = _
    rw [radicalAction_apply,he,mul_inv_cancel_right]
  have hmove : BinaryOffender.subspaceCommutator σ ⊤ S ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,v,_,rfl⟩
    change (radicalAction Q split i (hV i) (ν.symm a) v.toMul / v.toMul : V) ∈ M.subgroupOf V
    simp only [div_eq_mul_inv]
    change ((radicalAction Q split i (hV i) (ν.symm a) v.toMul : V) : X ⧸ Q.D) *
      (v.toMul : X ⧸ Q.D)⁻¹ ∈ M
    rw [radicalAction_apply]
    have hd : ⁅(ν.symm a : X ⧸ Q.D),(v.toMul : X ⧸ Q.D)⁆ ∈ ⁅split.U,split.U⁆ :=
      commutator_mem_commutator (simpleRoot_le Q split i (hroot a ha)) v.toMul.property.1
    have hdV (k : Fin 2) : ⁅split.U,split.U⁆ ≤ simpleRemainder Q split k := by
      let := hE k
      exact unipotent_commutator_le_remainder Q split k (hV k)
        (commutator_self_eq_bot_iff.mpr inferInstance)
    exact ⟨hdV i hd,hdV j hd⟩
  have hseed : (⨆ a : SL(2,F), C.map (σ a)) = ⊤ := by
    let W := ⨆ a : SL(2,F), C.map (σ a)
    have hCW : C ≤ W := by
      have hh := le_iSup (fun a : SL(2,F) => C.map (σ a)) 1
      simpa only [map_one,show (1 : Module.End (ZMod 2) (Additive V)) = LinearMap.id from rfl,
        Submodule.map_id] using hh
    let s := UnitarySource.actorReflection Q split i
    let r : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩
    have hAW (a : X ⧸ Q.D) (ha : a ∈ simpleRoot Q split j) :
        Additive.ofMul (⟨a,(opposite_roots_le_remainder Q split j i hij.symm).1 ha⟩ : V) ∈ W := by
      let v : V := ⟨a,(opposite_roots_le_remainder Q split j i hij.symm).1 ha⟩
      let z := radicalAction Q split i (hV i) r⁻¹ v
      have hz : (z : X ⧸ Q.D) ∈ M := by
        rw [hM,rootAt_eq Q split j (Q.simple i) s.val s.class_eq]
        change (s.val : X ⧸ Q.D)*(z : X ⧸ Q.D)*(s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
        dsimp only [z]
        rw [radicalAction_right_conjugation]
        simpa only [r,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
      apply (le_iSup (fun a : SL(2,F) => C.map (σ a)) (ν r))
      refine ⟨Additive.ofMul z,hz,?_⟩
      change Additive.ofMul (radicalAction Q split i (hV i) (ν.symm (ν r)) z) = _
      rw [MulEquiv.symm_apply_apply]
      dsimp only [z]
      rw [←MulAut.mul_apply,←map_mul,mul_inv_cancel,map_one]
      rfl
    apply top_unique
    intro v _
    have hv : (v.toMul : X ⧸ Q.D) ∈
        (simpleRoot Q split j : Set (X ⧸ Q.D)) *
          (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) :=
      remainder_product Q split hm i j hij ▸ v.toMul.property
    obtain ⟨a,ha,b,hb,hab⟩ := hv
    have hbM : b ∈ M := by
      rw [hM,←cross_root_eq Q split hm i j hij]
      exact hb
    have hh := W.add_mem (hAW a ha) (hCW (show Additive.ofMul (⟨b,hbM.1⟩ : V) ∈ C from hbM))
    have he : Additive.ofMul (⟨a,(opposite_roots_le_remainder Q split j i hij.symm).1 ha⟩ : V) +
        Additive.ofMul (⟨b,hbM.1⟩ : V) = v := by
      apply Additive.toMul.injective
      exact Subtype.ext hab
    exact he ▸ hh
  have hcard : Nat.card C ≤ Nat.card F := by
    let ec : C ≃ M.subgroupOf V :=
      { toFun := fun x => ⟨x.val.toMul,x.property⟩
        invFun := fun x => ⟨Additive.ofMul x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hroots : Nat.card (simpleRoot Q split j) = Nat.card (simpleRoot Q split i) := by
      have he := simpleRoot_card_eq_of_odd Q split (hm ▸ (by decide : Odd 3))
      have hall (k : Fin 2) : Nat.card (simpleRoot Q split k) = Nat.card (simpleRoot Q split 0) := by
        fin_cases k
        · rfl
        · exact he.symm
      exact (hall j).trans (hall i).symm
    rw [Nat.card_congr ec,Nat.card_congr (subgroupOfEquivOfLe (show M ≤ V from inf_le_left)).toEquiv,
      hM]
    simp only [rootAt,card_rightConjugate,hroots,GTwoSource.simpleRoot_card Q split i (hV i) μlocal,le_refl]
  have hne : σ ≠ 1 := by
    intro hh
    obtain ⟨r,hr⟩ := radicalAction_nontrivial Q split hm i (hV i)
    apply hr
    apply MulEquiv.ext
    intro v
    have he := congrArg (fun f : Representation (ZMod 2) SL(2,F) (Additive V) =>
      f (ν r) (Additive.ofMul v)) hh
    change Additive.ofMul (radicalAction Q split i (hV i) (ν.symm (ν r)) v) = Additive.ofMul v at he
    rw [MulEquiv.symm_apply_apply] at he
    exact congrArg Additive.toMul he
  obtain ⟨_,c,hc⟩ := RankOne.QuadraticRecognition.sl2_small_seed_natural σ S C hne hfix hseed hmove hcard
  refine ⟨c,fun r v => ?_⟩
  have he := hc (ν r) v
  change c (ρ (ν.symm (ν r)) v) = _ at he
  simpa only [MulEquiv.symm_apply_apply] using he
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TriangleStructure
