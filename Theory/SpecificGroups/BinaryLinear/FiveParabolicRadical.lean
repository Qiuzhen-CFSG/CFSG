module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.MiddleTensor
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# The irreducible radical of the middle parabolic in SL₅(2)

In the natural decomposition F₂² ⊕ F₂³, the unipotent radical is the
additive group of 2-by-3 matrices. Conjugation by the two diagonal blocks
preserves no proper nonzero subgroup, by the irreducibility of the binary
tensor module. Thus every normal two-subgroup of this parabolic has order
one or sixty-four. In particular, there is no normal elementary eight-group.

An explicit change of natural coordinates identifies this stabilizer with
the literal two-space parabolic of the five-dimensional matrix group.
The shear construction adapts `BinaryLinear/FourParabolicRadical.lean`.
The source application is the tensor obstruction in Aschbacher--Smith,
12.5.8(1), printed p.820. Recognition of an ambient local subgroup as this
parabolic is a separate obligation.
-/

@[expose] public noncomputable section
open Subgroup Matrix
namespace BinaryLinear.FiveParabolicRadical
abbrev F := ZMod 2
abbrev Head := Fin 2 → F
abbrev Tail := Fin 3 → F
abbrev Mat := Matrix (Fin 2) (Fin 3) F
abbrev Space := Head × Tail
abbrev Lin := BinaryLinear.GL Space

/-- The marked two-space whose stabilizer is the 2+3 parabolic. -/
def plane : Submodule F Space := LinearMap.ker (LinearMap.snd F Head Tail)

/-- An upper block-unipotent linear automorphism. -/
def shear (A : Mat) : Lin where
  toFun v := (v.1 + A.mulVec v.2, v.2)
  invFun v := (v.1 - A.mulVec v.2, v.2)
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp [mulVec_add, add_add_add_comm]
  map_smul' a v := by simp [mulVec_smul, smul_add]

/-- The actual upper block-unipotent embedding. -/
def upper : Multiplicative Mat →* Lin where
  toFun A := shear A.toAdd
  map_one' := by ext v i <;> simp [shear]
  map_mul' A B := by
    apply LinearEquiv.ext
    intro v
    apply Prod.ext
    · change v.1 + (A.toAdd + B.toAdd).mulVec v.2 =
        (v.1 + B.toAdd.mulVec v.2) + A.toAdd.mulVec v.2
      rw [add_mulVec]
      abel
    · rfl

theorem upper_injective : Function.Injective upper := by
  intro A B h
  apply Multiplicative.toAdd.injective
  ext i j
  have hh := congrArg (fun g : Lin => (g (0, Pi.single j 1)).1 i) h
  simpa [upper, shear, mulVec_single] using hh

/-- The upper block group is exactly the geometric radical. -/
theorem range_upper : upper.range = BinaryLinear.radical plane := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    constructor
    · intro v hv
      change v.2 = 0 at hv
      apply Prod.ext <;> simp [upper, shear, hv]
    · intro v
      change v.2 - v.2 = 0
      exact sub_self _
  · intro g hg
    let f : Tail →ₗ[F] Head := (LinearMap.fst F Head Tail).comp
      (g.toLinearMap.comp (LinearMap.inr F Head Tail))
    refine ⟨Multiplicative.ofAdd (LinearMap.toMatrix' f), ?_⟩
    apply LinearEquiv.ext
    intro v
    have hfix := hg.1 (v.1, 0) (by simp [plane])
    have hdiff := hg.2 (0, v.2)
    change (g (0, v.2)).2 - (0, v.2).2 = 0 at hdiff
    have hsum := g.map_add (v.1, 0) (0, v.2)
    rw [hfix] at hsum
    simp only [Prod.mk_add_mk, add_zero, zero_add] at hsum
    rw [hsum]
    change (v.1 + (LinearMap.toMatrix' f).mulVec v.2, v.2) = _
    rw [LinearMap.toMatrix'_mulVec]
    refine Prod.ext rfl ?_
    simpa using (sub_eq_zero.mp hdiff).symm

/-- The radical has sixty-four elements. -/
theorem card_radical : Nat.card (BinaryLinear.radical plane) = 64 := by
  rw [← range_upper, ← Nat.card_congr (MonoidHom.ofInjective upper_injective).toEquiv]
  rw [Nat.card_congr Multiplicative.toAdd]
  simp [Mat, Matrix]

private def diagonal (a : BinaryLinear.GL Head) (b : BinaryLinear.GL Tail) : Lin := a.prodCongr b

private theorem diagonal_mem (a : BinaryLinear.GL Head) (b : BinaryLinear.GL Tail) :
    diagonal a b ∈ BinaryLinear.parabolic plane := by
  intro v
  change b v.2 = 0 ↔ v.2 = 0
  exact b.map_eq_zero_iff

private theorem conjugate_upper (a : BinaryLinear.GL Head) (b : BinaryLinear.GL Tail) (A : Mat) :
    diagonal a b * upper (Multiplicative.ofAdd A) * (diagonal a b)⁻¹ =
      upper (Multiplicative.ofAdd (LinearMap.toMatrix'
        (a.toLinearMap.comp ((Matrix.toLin' A).comp b.symm.toLinearMap)))) := by
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · simp [diagonal, upper, shear, LinearMap.toMatrix'_mulVec, map_add]
  · simp [diagonal, upper, shear]


private theorem matrix_left (a : Matrix.SpecialLinearGroup (Fin 2) F) (A : Mat) :
    LinearMap.toMatrix' ((OuterCyclic.slEquivLinear 2 a).toLinearMap.comp (Matrix.toLin' A)) =
      a.val * A := by
  apply (Matrix.toLin' : Mat ≃ₗ[F] (Tail →ₗ[F] Head)).injective
  ext v i
  simp only [Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe, OuterCyclic.slEquivLinear_apply, Matrix.mulVec_mulVec]

private theorem matrix_right (b : Matrix.SpecialLinearGroup (Fin 3) F) (A : Mat) :
    LinearMap.toMatrix' ((Matrix.toLin' A).comp (OuterCyclic.slEquivLinear 3 b).toLinearMap) =
      A * b.val := by
  apply (Matrix.toLin' : Mat ≃ₗ[F] (Tail →ₗ[F] Head)).injective
  ext v i
  simp only [Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe, OuterCyclic.slEquivLinear_apply, Matrix.mulVec_mulVec]

private theorem invariant_matrices (H : AddSubgroup Mat)
    (hleft : ∀ a : BinaryLinear.GL Head, ∀ A ∈ H,
      LinearMap.toMatrix' (a.toLinearMap.comp (Matrix.toLin' A)) ∈ H)
    (hright : ∀ b : BinaryLinear.GL Tail, ∀ A ∈ H,
      LinearMap.toMatrix' ((Matrix.toLin' A).comp b.toLinearMap) ∈ H) :
    H = ⊥ ∨ H = ⊤ := by
  let W : Subrepresentation Representation.SL5ExteriorSquare.middleTensorRepresentation :=
    { toSubmodule := AddSubgroup.toZModSubmodule 2 H
      apply_mem_toSubmodule := by
        intro g x hx
        let a := (Representation.SL5ExteriorSquare.parabolicLeviHom 2 (by decide) g).1
        let b := (Representation.SL5ExteriorSquare.parabolicLeviHom 2 (by decide) g).2
        have hh := hright (OuterCyclic.slEquivLinear 3 b.transpose) _
          (hleft (OuterCyclic.slEquivLinear 2 a) x hx)
        rw [matrix_right, matrix_left] at hh
        change Representation.SL5ExteriorSquare.middleTensorOperator g.val x ∈ H
        rw [Representation.SL5ExteriorSquare.middleTensorOperator_eq_mul]
        have ha : a.val = Representation.SL5ExteriorSquare.middleUpperBlock g.val := by
          ext i j
          exact Representation.SL5ExteriorSquare.parabolicLeviHom_fst_entry 2 (by decide) g i j
        have hb : b.val = Representation.SL5ExteriorSquare.middleLowerBlock g.val := by
          ext i j
          simpa only [Representation.SL5ExteriorSquare.middleLowerBlock,
            Representation.SL5ExteriorSquare.middleLowerIndex, Nat.add_comm] using
            Representation.SL5ExteriorSquare.parabolicLeviHom_snd_entry 2 (by decide) g i j
        simpa only [Matrix.SpecialLinearGroup.coe_transpose, ha, hb] using hh }
  let := Representation.SL5ExteriorSquare.middleTensorRepresentation_isIrreducible
  rcases eq_bot_or_eq_top W with hz | ht
  · left
    apply bot_unique
    intro x hx
    have : x ∈ W := hx
    rw [hz] at this
    exact this
  · right
    apply top_unique
    intro x _
    show x ∈ W
    rw [ht]
    trivial

/-- Conjugation by the parabolic has no nonzero proper invariant subgroup. -/
theorem radical_irreducible (W : Subgroup Lin) (hW : W ≤ BinaryLinear.radical plane)
    (hN : BinaryLinear.parabolic plane ≤ normalizer (W : Set Lin)) :
    W = ⊥ ∨ W = BinaryLinear.radical plane := by
  let H : AddSubgroup Mat :=
    { carrier := {A | upper (Multiplicative.ofAdd A) ∈ W}
      zero_mem' := by
        change upper 1 ∈ W
        rw [map_one]
        exact W.one_mem
      add_mem' := by
        intro A B hA hB
        change upper (Multiplicative.ofAdd A * Multiplicative.ofAdd B) ∈ W
        rw [map_mul]
        exact W.mul_mem hA hB
      neg_mem' := by
        intro A hA
        change upper (Multiplicative.ofAdd A)⁻¹ ∈ W
        rw [map_inv]
        exact W.inv_mem hA }
  have hc (a : BinaryLinear.GL Head) (b : BinaryLinear.GL Tail) (A : Mat) (hA : A ∈ H) :
      LinearMap.toMatrix' (a.toLinearMap.comp
        ((Matrix.toLin' A).comp b.symm.toLinearMap)) ∈ H := by
    have hh := le_set_normalizer_iff.mp hN (diagonal a b) (diagonal_mem a b)
      (upper (Multiplicative.ofAdd A)) hA
    rw [conjugate_upper] at hh
    exact hh
  have hl (a : BinaryLinear.GL Head) (A : Mat) (hA : A ∈ H) :
      LinearMap.toMatrix' (a.toLinearMap.comp (Matrix.toLin' A)) ∈ H := by
    have hh := hc a 1 A hA
    change LinearMap.toMatrix' (a.toLinearMap.comp
      ((Matrix.toLin' A).comp LinearMap.id)) ∈ H at hh
    simpa only [LinearMap.comp_id] using hh
  have hr (b : BinaryLinear.GL Tail) (A : Mat) (hA : A ∈ H) :
      LinearMap.toMatrix' ((Matrix.toLin' A).comp b.toLinearMap) ∈ H := by
    have hh := hc 1 b.symm A hA
    rw [LinearEquiv.symm_symm] at hh
    change LinearMap.toMatrix' (LinearMap.id.comp
      ((Matrix.toLin' A).comp b.toLinearMap)) ∈ H at hh
    simpa only [LinearMap.id_comp] using hh
  rcases invariant_matrices H hl hr with hz | ht
  · left
    apply bot_unique
    intro g hg
    obtain ⟨A, rfl⟩ := (show g ∈ upper.range from range_upper.symm ▸ hW hg)
    have ha : A.toAdd ∈ H := hg
    have ha0 : A.toAdd = 0 := by simpa only [hz, AddSubgroup.mem_bot] using ha
    have ha1 : A = 1 := Multiplicative.toAdd.injective ha0
    simp [ha1]
  · right
    apply le_antisymm hW
    intro g hg
    obtain ⟨A, rfl⟩ := (show g ∈ upper.range from range_upper.symm ▸ hg)
    exact (show A.toAdd ∈ H from ht ▸ AddSubgroup.mem_top _)

/-- Every normal two-subgroup of the actual 2+3 parabolic has order one or sixty-four. -/
theorem normal_two_subgroup_card (N : Subgroup (BinaryLinear.parabolic plane))
    [N.Normal] (hN : IsPGroup 2 N) : Nat.card N = 1 ∨ Nat.card N = 64 := by
  let P := BinaryLinear.parabolic plane
  let W := N.map P.subtype
  have hW : W ≤ BinaryLinear.radical plane := by
    rw [← SmallParabolicLevi.map_twoCore_eq_radical plane]
    exact map_mono (le_sSup ⟨inferInstance, hN⟩)
  have hn : P ≤ normalizer (W : Set Lin) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le N)).mp
    change ((N.map P.subtype).comap P.subtype).Normal
    rw [comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance
  have hc : Nat.card W = Nat.card N := card_map_of_injective P.subtype_injective
  rcases radical_irreducible W hW hn with he | he
  · left
    rw [← hc, he, card_bot]
  · right
    rw [← hc, he, card_radical]

/-- In particular, a normal elementary eight-group cannot occur in this parabolic. -/
theorem no_normal_eight (N : Subgroup (BinaryLinear.parabolic plane))
    [N.Normal] (hN : IsPGroup 2 N) : Nat.card N ≠ 8 := by
  have hc := normal_two_subgroup_card N hN
  omega

/-- The natural coordinates of the 2+3 block model. -/
def spaceEquiv : Space ≃ₗ[F] (Fin 5 → F) where
  toFun v := ![v.1 0, v.1 1, v.2 0, v.2 1, v.2 2]
  invFun v := (![v 0, v 1], ![v 2, v 3, v 4])
  left_inv v := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

/-- The coordinate map carries the first summand onto the marked two-space. -/
theorem spaceEquiv_mem_flag (v : Space) :
    spaceEquiv v ∈ Representation.SL5ExteriorSquare.naturalFlag 2 ↔ v ∈ plane := by
  change (∀ i : Fin 5, 2 ≤ i.val → ![v.1 0,v.1 1,v.2 0,v.2 1,v.2 2] i = 0) ↔ v.2 = 0
  simp [funext_iff, Fin.forall_fin_succ]

/-- Change coordinates without changing either stabilizer action. -/
def splitParabolicEquiv :
    BinaryLinear.parabolic (Representation.SL5ExteriorSquare.naturalFlag 2) ≃*
      BinaryLinear.parabolic plane := by
  let e := SmallParabolicLevi.linearGroupCongr spaceEquiv.symm
  have hm (g : OuterCyclic.LinearGroup 5) :
      e g ∈ BinaryLinear.parabolic plane ↔
        g ∈ BinaryLinear.parabolic (Representation.SL5ExteriorSquare.naturalFlag 2) := by
    constructor
    · intro hg v
      have hh := hg (spaceEquiv.symm v)
      rw [← spaceEquiv_mem_flag, ← spaceEquiv_mem_flag] at hh
      simpa only [e, SmallParabolicLevi.linearGroupCongr_apply, LinearEquiv.symm_symm,
        LinearEquiv.apply_symm_apply] using hh
    · intro hg v
      change spaceEquiv.symm (g (spaceEquiv v)) ∈ plane ↔ v ∈ plane
      rw [← spaceEquiv_mem_flag, LinearEquiv.apply_symm_apply, ← spaceEquiv_mem_flag]
      exact hg _
  have he : (BinaryLinear.parabolic (Representation.SL5ExteriorSquare.naturalFlag 2)).map
      e.toMonoidHom = BinaryLinear.parabolic plane := by
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      exact (hm g).mpr hg
    · intro g hg
      refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
      apply (hm (e.symm g)).mp
      simpa only [MulEquiv.apply_symm_apply] using hg
  exact (e.subgroupMap _).trans (MulEquiv.subgroupCongr he)

/-- The literal two-space parabolic in SL₅(2), in 2+3 coordinates. -/
def matrixParabolicEquiv : Representation.SL5ExteriorSquare.parabolic 2 ≃*
    BinaryLinear.parabolic plane :=
  (Representation.SL5ExteriorSquare.parabolicLinearEquiv 2).trans splitParabolicEquiv

/-- The original matrix model also has no normal two-subgroup of order eight. -/
theorem matrix_no_normal_eight (N : Subgroup (Representation.SL5ExteriorSquare.parabolic 2))
    [N.Normal] (hN : IsPGroup 2 N) : Nat.card N ≠ 8 := by
  let e := matrixParabolicEquiv
  let B := N.map e.toMonoidHom
  let : B.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hc := no_normal_eight B (hN.map e.toMonoidHom)
  rwa [card_map_of_injective e.injective] at hc

end BinaryLinear.FiveParabolicRadical
