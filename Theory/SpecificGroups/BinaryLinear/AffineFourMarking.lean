module

public import Theory.SpecificGroups.BinaryLinear.AffinePointMarking
public import Theory.SpecificGroups.BinaryLinear.TransvectionFiveLocal.Defs
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

/-!
# Affine coordinates for the degree-five transvection centralizer

The homogeneous-coordinate embedding sends (v,a) to [[a,v],[0,1]].
A matrix commuting with I+E₀₄ has last row (0,0,0,0,1), so this embedding
restricts to an equivalence of the entire translation centralizer with the
entire transvection centralizer. The translation kernel maps exactly onto
the last-column root group. A binary change of basis aligns any nonzero
translation with the first coordinate while retaining every translation.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(2), p.213;
Aschbacher–Smith, 12.2.26–27, pp.806–807.
-/

@[expose] public noncomputable section

open Subgroup Matrix
namespace BinaryLinear.Affine.FourMarking
abbrev B := ZMod 2
abbrev Mat := Matrix (Fin 5) (Fin 5) B
abbrev SL4 := Matrix.SpecialLinearGroup (Fin 4) B
open BinaryLinear.TransvectionFiveLocal

def entries (a : Matrix (Fin 4) (Fin 4) B) (v : Fin 4 → B) : Mat :=
  !![a 0 0,a 0 1,a 0 2,a 0 3,v 0;
     a 1 0,a 1 1,a 1 2,a 1 3,v 1;
     a 2 0,a 2 1,a 2 2,a 2 3,v 2;
     a 3 0,a 3 1,a 3 2,a 3 3,v 3;
     0,0,0,0,1]

theorem entries_block (a : Matrix (Fin 4) (Fin 4) B) (v : Fin 4 → B) :
    entries a v = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks a (Matrix.of fun i (_ : Fin 1) => v i) 0
        (1 : Matrix (Fin 1) (Fin 1) B)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem entries_det (a : Matrix (Fin 4) (Fin 4) B) (v : Fin 4 → B) :
    (entries a v).det = a.det := by
  rw [entries_block, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem entries_mul (a b : Matrix (Fin 4) (Fin 4) B) (u v : Fin 4 → B) :
    entries (a * b) (u + a.mulVec v) = entries a u * entries b v := by
  simp only [entries_block]
  rw [← Matrix.coe_reindexRingEquiv]
  rw [← map_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_one]
  congr 1
  ext i j
  change u i + (a.mulVec v) i = (a.mulVec v) i + u i
  exact add_comm _ _

def embed : Model 4 →* SL where
  toFun x := ⟨entries x.right.val x.left.toAdd, (entries_det _ _).trans x.right.property⟩
  map_one' := by
    apply Subtype.ext
    change entries 1 0 = 1
    rw [entries_block]
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 1 0 0 1) = 1
    rw [Matrix.fromBlocks_one]
    exact (Matrix.reindexRingEquiv B finSumFinEquiv).map_one
  map_mul' x y := Subtype.ext (entries_mul x.right.val y.right.val x.left.toAdd y.left.toAdd)

theorem embed_block (x : Model 4) (i j : Fin 4) : embed x i.castSucc j.castSucc = x.right i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem embed_translation (x : Model 4) (i : Fin 4) : embed x i.castSucc 4 = x.left.toAdd i := by
  fin_cases i <;> rfl

theorem embed_lastRow (x : Model 4) (j : Fin 5) : embed x 4 j = if j = 4 then 1 else 0 := by
  fin_cases j <;> rfl

theorem embed_injective : Function.Injective embed := by
  intro x y he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    simpa only [embed_translation] using congrArg (fun a : SL => a i.castSucc 4) he
  · apply Subtype.ext
    ext i j
    simpa only [embed_block] using congrArg (fun a : SL => a i.castSucc j.castSucc) he

theorem mem_range_embed (g : SL) (hrow : ∀ j : Fin 5, g 4 j = if j = 4 then 1 else 0) :
    g ∈ embed.range := by
  let a : Matrix (Fin 4) (Fin 4) B := fun i j => g i.castSucc j.castSucc
  let v : Fin 4 → B := fun i => g i.castSucc 4
  have he : entries a v = g.val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [entries, a, v, hrow]
  have hd : a.det = 1 := by rw [← entries_det a v, he]; exact g.property
  exact ⟨⟨Multiplicative.ofAdd v, ⟨a, hd⟩⟩, Subtype.ext he⟩

def e0 : Multiplicative (Fin 4 → B) := Multiplicative.ofAdd ![1,0,0,0]

theorem embed_e0 : embed (SemidirectProduct.inl e0) = BinaryLinear.TransvectionFiveLocal.transvection := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem centralizer_lastRow (g : SL) (hg : g ∈ centralizer) :
    ∀ j : Fin 5, g 4 j = if j = 4 then 1 else 0 := by
  have hc := mem_centralizer_singleton_iff.mp hg
  have hz (j : Fin 5) (hj : j ≠ 4) : g 4 j = 0 := by
    have he := congrArg (fun a : SL => a 0 j) hc
    change ((g : Mat) * (1 + Matrix.single 0 4 1) : Mat) 0 j =
      ((1 + Matrix.single 0 4 1) * (g : Mat) : Mat) 0 j at he
    simpa [Matrix.add_mul, Matrix.mul_add, hj, eq_comm] using he.symm
  have h44 : g 4 4 = 1 := by
    apply (by decide : ∀ a : B, a ≠ 0 → a = 1)
    intro he
    apply g.det_ne_zero (Matrix.det_eq_zero_of_row_eq_zero 4 ?_)
    intro j
    by_cases hj : j = 4
    · simpa only [hj] using he
    · exact hz j hj
  intro j
  by_cases hj : j = 4
  · simpa only [hj, ite_true] using h44
  · simpa only [if_neg hj] using hz j hj

abbrev H := Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) e0

def centralizerHom : H →* centralizer := embed.comp H.subtype |>.codRestrict _ (by
  intro x
  apply mem_centralizer_singleton_iff.mpr
  change embed x.val * _ = _ * embed x.val
  rw [← embed_e0, ← map_mul, ← map_mul]
  exact congrArg embed (mem_centralizer_singleton_iff.mp x.property))

theorem centralizerHom_bijective : Function.Bijective centralizerHom := by
  constructor
  · intro x y he
    exact Subtype.ext (embed_injective (congrArg Subtype.val he))
  · intro g
    obtain ⟨x,hx⟩ := mem_range_embed g (centralizer_lastRow g g.property)
    have hxH : x ∈ H := by
      apply mem_centralizer_singleton_iff.mpr
      apply embed_injective
      rw [map_mul, map_mul, embed_e0, hx]
      exact mem_centralizer_singleton_iff.mp g.property
    exact ⟨⟨x,hxH⟩, Subtype.ext hx⟩

noncomputable def centralizerEquiv : H ≃* centralizer := MulEquiv.ofBijective centralizerHom centralizerHom_bijective

theorem centralizerEquiv_apply (x : H) : (centralizerEquiv x : SL) = embed x.val := rfl


private def translationWord (v : Multiplicative (Fin 4 → B)) : SL :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 4) (v.toAdd 0) *
  Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 5) ≠ 4) (v.toAdd 1) *
  Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 5) ≠ 4) (v.toAdd 2) *
  Matrix.SpecialLinearGroup.transvection (by decide : (3 : Fin 5) ≠ 4) (v.toAdd 3)

private theorem translationWord_val (v : Multiplicative (Fin 4 → B)) :
    (translationWord v).val = 1 + Matrix.single 0 4 (v.toAdd 0) +
      Matrix.single 1 4 (v.toAdd 1) + Matrix.single 2 4 (v.toAdd 2) +
      Matrix.single 3 4 (v.toAdd 3) := by
  simp [translationWord, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_of_ne, add_assoc]

theorem embed_inl_mem_column (v : Multiplicative (Fin 4 → B)) :
    embed (SemidirectProduct.inl v) ∈ naturalFactor := by
  have hw : embed (SemidirectProduct.inl v) = translationWord v := by
    apply Subtype.ext
    rw [translationWord_val]
    ext i j
    change entries 1 v.toAdd i j = _
    fin_cases i <;> fin_cases j <;> simp [entries, Matrix.single]
  rw [hw]
  have hr (i : Fin 5) (hi : i < 4) (c : B) :
      Matrix.SpecialLinearGroup.transvection (ne_of_lt hi) c ∈ naturalFactor := by
    rcases (by decide : ∀ c : B, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · exact subset_closure ⟨i,hi,rfl⟩
  exact naturalFactor.mul_mem (naturalFactor.mul_mem (naturalFactor.mul_mem
    (hr 0 (by decide) _) (hr 1 (by decide) _)) (hr 2 (by decide) _)) (hr 3 (by decide) _)

theorem column_eq_translation_range : naturalFactor =
    (embed.comp (SemidirectProduct.inl : Multiplicative (Fin 4 → B) →* Model 4)).range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i,hi,rfl⟩
    refine ⟨Multiplicative.ofAdd (Pi.single ⟨i.val,hi⟩ 1), ?_⟩
    apply Subtype.ext
    change entries 1 (Pi.single ⟨i.val,hi⟩ 1) = _
    fin_cases i <;> try exact ((by decide : ¬ (4 : Fin 5) < 4) hi).elim
    all_goals decide +kernel +revert
  · rintro _ ⟨v,rfl⟩
    exact embed_inl_mem_column v

theorem exists_rotation (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1) :
    ∃ a : SL4, action 4 a v = e0 := by
  have hv0 : v.toAdd ≠ 0 := hv
  have he0 : e0.toAdd ≠ 0 := by decide
  let ex := LinearEquiv.toSpanNonzeroSingleton B (Fin 4 → B) v.toAdd hv0
  let ey := LinearEquiv.toSpanNonzeroSingleton B (Fin 4 → B) e0.toAdd he0
  obtain ⟨g,hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  obtain ⟨a,rfl⟩ := (BinaryLinear.OuterCyclic.slEquivLinear 4).surjective g
  refine ⟨a, ?_⟩
  have hh := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at hh
  have ha : BinaryLinear.OuterCyclic.slEquivLinear 4 a v.toAdd = e0.toAdd := by
    simpa [ex,ey] using hh.symm
  exact congrArg Multiplicative.ofAdd ha

noncomputable def rotation (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1) : SL4 :=
  (exists_rotation v hv).choose

theorem rotation_apply (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1) :
    action 4 (rotation v hv) v = e0 := (exists_rotation v hv).choose_spec

def conjugation (a : SL4) : MulAut (Model 4) := MulAut.conj (SemidirectProduct.inr a)

theorem conjugation_inl (a : SL4) (u : Multiplicative (Fin 4 → B)) :
    conjugation a (SemidirectProduct.inl u) = SemidirectProduct.inl (action 4 a u) := by
  simpa only [conjugation, MulAut.conj_apply, map_inv] using
    (SemidirectProduct.inl_aut (φ := action 4) a u).symm

noncomputable def rotatedCentralizerEquiv (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1) :
    Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) v ≃* H :=
  let e := conjugation (rotation v hv)
  ((Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) v).equivMapOfInjective
    e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      rw [Theory.GroupTheory.CentralizerSmallKernelTransport.map_centralizer,
        conjugation_inl, rotation_apply]))

theorem rotatedCentralizerEquiv_apply (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1)
    (x : Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) v) :
    (rotatedCentralizerEquiv v hv x : Model 4) = conjugation (rotation v hv) x.val := rfl

noncomputable def pointEquiv (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1) :
    Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) v ≃* centralizer :=
  (rotatedCentralizerEquiv v hv).trans centralizerEquiv

theorem pointEquiv_inclusion (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1)
    (u : Multiplicative (Fin 4 → B)) :
    (pointEquiv v hv (Theory.GroupTheory.TranslationCentralizer.inclusion (action 4) v u) : SL) =
      embed (SemidirectProduct.inl (action 4 (rotation v hv) u)) := by
  rw [pointEquiv, MulEquiv.trans_apply, centralizerEquiv_apply,
    rotatedCentralizerEquiv_apply]
  exact congrArg embed (conjugation_inl (rotation v hv) u)

theorem pointEquiv_point (v : Multiplicative (Fin 4 → B)) (hv : v ≠ 1) :
    (pointEquiv v hv (Theory.GroupTheory.TranslationCentralizer.inclusion (action 4) v v) : SL) =
      BinaryLinear.TransvectionFiveLocal.transvection := by
  rw [pointEquiv_inclusion, rotation_apply, embed_e0]

end BinaryLinear.Affine.FourMarking
