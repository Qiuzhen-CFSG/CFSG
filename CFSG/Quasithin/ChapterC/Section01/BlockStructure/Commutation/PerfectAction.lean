module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import Theory.Representation.EndFieldRep
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Perfect actors on normal short groups

A perfect actor centralizing X/O₂(X) centralizes the irreducible module
U(X)/C_U(X)(X): its image lies in the multiplicative group of a finite
endomorphism field. The three-subgroups lemma and [U(X),X]=U(X) then
lift this to U(X). The two-layer centralizer theorem finishes on X.

This is the perfect-actor case of Aschbacher--Smith C.1.10, printed p.124
(combined manuscript of 1 March 2004), used for the quasisimple branch
of C.1.9. The Schur and layer calculations are adapted from the checked
private proofs in Chapter15/.../FieldFourCentrality/SourceCubicActor/Commutation;
the original source is preserved. No later chapter is imported.
-/

public section
open scoped IsMulCommutative MonoidAlgebra
open Subgroup Representation

namespace CFSG.Quasithin.ChapterC.BlockCommutation.Schur
variable {A B W : Type*} [Group A] [Group B] [Group W]
  [Finite W] [IsElementaryAbelian 2 W]

private def linearAction (ρ : A →* MulAut W) : Representation (ZMod 2) A (Additive W) where
  toFun a := (ρ a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext w; exact DFunLike.congr_fun (map_one ρ) w
  map_mul' a b := by ext w; exact DFunLike.congr_fun (map_mul ρ a b) w

omit [Finite W] in
private theorem linearAction_irreducible (ρ : A →* MulAut W) [Nontrivial W]
    (hirr : ∀ D : Subgroup W, (∀ a w, w ∈ D → ρ a w ∈ D) → D = ⊥ ∨ D = ⊤) :
    IsIrreducible (linearAction ρ) := by
  constructor
  intro N
  let D : Subgroup W := N.toSubmodule.toAddSubgroup.toSubgroup
  have hd : D = ⊥ ∨ D = ⊤ := hirr D (fun a w hw => N.apply_mem_toSubmodule a hw)
  rcases hd with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro w hw
    exact (show w.toMul ∈ (⊥ : Subgroup W) from hb ▸ hw)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    exact (show w.toMul ∈ D from ht ▸ mem_top w.toMul)

set_option backward.isDefEq.respectTransparency false in
private theorem commuting_perfect_action [Nontrivial W] [Group.IsPerfect B]
    (ρ : A →* MulAut W) (σ : B →* MulAut W)
    (hirr : ∀ D : Subgroup W, (∀ a w, w ∈ D → ρ a w ∈ D) → D = ⊥ ∨ D = ⊤)
    (hc : ∀ a b, ρ a * σ b = σ b * ρ a) : σ = 1 := by
  let r := linearAction ρ
  let s := linearAction σ
  let : IsIrreducible r := linearAction_irreducible ρ hirr
  let t : B →* IntertwiningMap r r := {
    toFun := fun b => ⟨s b, fun a => by
      ext w
      exact DFunLike.congr_fun (hc a b).symm w⟩
    map_one' := by ext w; exact DFunLike.congr_fun (map_one s) w
    map_mul' := by intro a b; ext w; exact DFunLike.congr_fun (map_mul s a b) w }
  let e := IntertwiningMap.equivAlgEnd r
  let f := (e.toMonoidHom.comp t).toHomUnits
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : IsMulCommutative f.range := ⟨⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    exact Units.ext (mul_comm _ _)⟩⟩
  let : Subsingleton f.range := inferInstance
  have hf (b : B) : f b = 1 := by
    exact congrArg Subtype.val (Subsingleton.elim (⟨f b, b, rfl⟩ : f.range) 1)
  ext b w
  have ht : t b = 1 := e.toMulEquiv.injective (by
    rw [map_one]
    exact congrArg Units.val (hf b))
  exact DFunLike.congr_fun (congrArg IntertwiningMap.toLinearMap ht) (Additive.ofMul w)

end CFSG.Quasithin.ChapterC.BlockCommutation.Schur

namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace BlockCommutation

variable {L L' : Type*} [Group L] [Group L']

/-- Isomorphisms preserve the intrinsic commutator layer. -/
private theorem map_blockU (e : L ≃* L') : (blockU L).map e.toMonoidHom = blockU L' := by
  rw [blockU, map_commutator, pCore_map_iso,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

/-- The induced equivalence of the intrinsic commutator layers. -/
private def blockUEquiv (e : L ≃* L') : blockU L ≃* blockU L' :=
  (e.subgroupMap (blockU L)).trans (MulEquiv.subgroupCongr (map_blockU e))

private theorem blockUEquiv_val (e : L ≃* L') (u : blockU L) :
    (blockUEquiv e u : L') = e u := rfl

/-- The induced equivalence preserves the central fixed layer. -/
private theorem map_blockFixed (e : L ≃* L') :
    (blockFixed L).map (blockUEquiv e).toMonoidHom = blockFixed L' := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    change e w ∈ center L'
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    exact (map_mul e y (w : L)).symm.trans ((congrArg e (mem_center_iff.mp hw y)).trans
      (map_mul e (w : L) y))
  · intro hu
    refine ⟨(blockUEquiv e).symm u, ?_, (blockUEquiv e).apply_symm_apply u⟩
    change ((blockUEquiv e).symm u : L) ∈ center L
    apply mem_center_iff.mpr
    intro x
    apply e.injective
    simp only [map_mul]
    have he : e ((blockUEquiv e).symm u : L) = (u : L') :=
      congrArg Subtype.val ((blockUEquiv e).apply_symm_apply u)
    rw [he]
    exact mem_center_iff.mp hu (e x)

/-- The actual module quotients are transported through their fixed layers. -/
private def blockModuleEquiv (e : L ≃* L') : BlockModule L ≃* BlockModule L' :=
  QuotientGroup.congr _ _ (blockUEquiv e) (map_blockFixed e)


private def blockAut : MulAut L →* MulAut (BlockModule L) where
  toFun := blockModuleEquiv
  map_one' := by
    ext u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) u
    rfl
  map_mul' a b := by
    ext u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) u
    rfl

private theorem blockAut_mk (a : MulAut L) (u : blockU L) :
    blockAut a (QuotientGroup.mk' (blockFixed L) u) =
      QuotientGroup.mk' (blockFixed L) (blockUEquiv a u) := rfl

private theorem blockAction_irreducible (h : IsShort L)
    (ρ : L →* MulAut (BlockModule L))
    (hρ : ∀ (l : L) (u : blockU L),
      ρ l (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u))
    (D : Subgroup (BlockModule L))
    (hD : ∀ l w, w ∈ D → ρ l w ∈ D) : D = ⊥ ∨ D = ⊤ := by
  let q := QuotientGroup.mk' (blockFixed L)
  let N := (D.comap q).map (blockU L).subtype
  have hN : N.Normal := by
    constructor
    intro x hx l
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨blockConjugate L l u, ?_, rfl⟩
    change q (blockConjugate L l u) ∈ D
    rw [← hρ]
    exact hD l (q u) hu
  have hlo : blockU L ⊓ center L ≤ N := by
    intro x hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    change q ⟨x, hx.1⟩ ∈ D
    have he : q ⟨x, hx.1⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hx.2
    rw [he]
    exact D.one_mem
  rcases h.irreducible.2 N hN hlo (map_subtype_le _) with hz | ht
  · left
    apply bot_unique
    intro w hw
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) w
    have hu : (u : L) ∈ N := ⟨u, hw, rfl⟩
    rw [hz] at hu
    exact (QuotientGroup.eq_one_iff u).mpr hu.2
  · right
    apply top_unique
    intro w _
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) w
    have hu : (u : L) ∈ N := by rw [ht]; exact u.property
    obtain ⟨v, hv, he⟩ := hu
    have he' : v = u := Subtype.ext he
    exact he' ▸ hv

variable {D : Type*} [Group D] [Finite D]

private theorem perfect_normal_block_centralizes_layer (A B : Subgroup D)
    [A.Normal] [Group.IsPerfect B] (hA : IsShort A)
    (hc : ⁅A, B⁆ ≤ A.pCoreIn 2) :
    ⁅(blockU A).map A.subtype, B⁆ = ⊥ := by
  let ρ : D →* MulAut (BlockModule A) := blockAut.comp MulAut.conjNormal
  let r := ρ.comp A.subtype
  let s := ρ.comp B.subtype
  have hr (a : A) (u : blockU A) :
      r a (QuotientGroup.mk' (blockFixed A) u) =
        QuotientGroup.mk' (blockFixed A) (blockConjugate A a u) := rfl
  have hker : A.pCoreIn 2 ≤ ρ.ker := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA.core_le_moduleAction_ker r hr ha
  have hcomm (a : A) (b : B) : r a * s b = s b * r a := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅ρ (a : D), ρ (b : D)⁆ = 1
    rw [← map_commutatorElement]
    exact hker (hc (commutator_mem_commutator a.property b.property))
  let := hA.module_elementary
  let := hA.module_nontrivial
  have hs : s = 1 := Schur.commuting_perfect_action r s
    (blockAction_irreducible hA r hr) hcomm
  let U := (blockU A).map A.subtype
  let Z := (center A).map A.subtype
  have hUB : ⁅U, B⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨u, hu, rfl⟩ := hu
    let v : blockU A := ⟨u, hu⟩
    have he := DFunLike.congr_fun (DFunLike.congr_fun hs ⟨b, hb⟩)
      (QuotientGroup.mk' (blockFixed A) v)
    change QuotientGroup.mk' (blockFixed A) (blockUEquiv (MulAut.conjNormal b) v) =
      QuotientGroup.mk' (blockFixed A) v at he
    have hz := QuotientGroup.eq_iff_div_mem.mp he
    refine ⟨(blockUEquiv (MulAut.conjNormal b) v : A) / u, hz, ?_⟩
    simp only [blockUEquiv_val, commutatorElement_def, div_eq_mul_inv]
    rfl
  have hZA : ⁅Z, A⁆ = ⊥ := by
    rw [← A.range_subtype, MonoidHom.range_eq_map, ← map_commutator]
    simp only [commutator_top_right_eq_bot_iff_le_center.mpr le_rfl, Subgroup.map_bot]
  have hcoreU : ⁅A.pCoreIn 2, U⁆ = ⊥ := by
    rw [pCoreIn, ← map_commutator]
    simpa only [Subgroup.map_bot] using congrArg (Subgroup.map A.subtype)
      (commutator_eq_bot_iff_le_centralizer.mpr hA.core_centralizes_blockU)
  have h1 : ⁅⁅U, B⁆, A⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hUB le_rfl).trans hZA.le)
  have h2 : ⁅⁅B, A⁆, U⁆ = ⊥ := by
    rw [commutator_comm B A]
    exact le_bot_iff.mp ((commutator_mono hc le_rfl).trans hcoreU.le)
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  have hUA : ⁅U, A⁆ = U := by
    simpa only [U, blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype] using
      congrArg (Subgroup.map A.subtype)
      (commutator_isPPerfect_idempotent (⊤ : Subgroup A) (pCore 2 A)
        (hA.twoPerfect.of_surjective (topEquiv : (⊤ : Subgroup A) ≃* A).symm.toMonoidHom
          (topEquiv : (⊤ : Subgroup A) ≃* A).symm.surjective)
        pCore_isPGroup le_normalizer_of_normal)
  rwa [commutator_comm A U, hUA] at h3

/-- A perfect, two-perfect actor fixing the core quotient fixes a normal short group.
The two-perfect hypothesis is supplied directly by the other block in C.1.9. -/
theorem perfect_actor_centralizes (A B : Subgroup D) [A.Normal] [Group.IsPerfect B]
    (hA : IsShort A) (hB : IsPPerfect 2 B) (hc : ⁅A, B⁆ ≤ A.pCoreIn 2) :
    ⁅A, B⁆ = ⊥ := by
  have hU := perfect_normal_block_centralizes_layer A B hA hc
  have hBA : ⁅B, A⁆ ≤ (pCore 2 A).map A.subtype := by
    rw [commutator_comm]
    exact hc
  have hz := hA.centralizes_of_coreQuotient_and_blockU A B hB hBA
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hU))
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hz)

end BlockCommutation
end CFSG.Quasithin.ChapterC
