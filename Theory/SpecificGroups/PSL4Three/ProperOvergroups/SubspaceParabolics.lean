module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.Geometry
public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Theory.GroupTheory.SolvableLayersEmbeddingConstructions
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Normal layers in every subspace parabolic of PSL₄(3)

The actual stabilizer acts on its invariant subspace `W` and on `Vec / W`.
The simultaneous kernel is abelian: its elements fix `W` pointwise and send
`v` to `v + w` for some `w ∈ W`.

For a two-dimensional subspace both actions have solvable target GL₂(3), so
the stabilizer and its projective image are solvable. The GL₂(3) argument is
adapted from `PSL3Three/ParabolicSolvability.lean`, using the proved binary
tetrahedral isomorphism SL₂(3) ≃ Q₈ ⋊ C₃.

For a line or hyperplane the three-dimensional action has solvable kernel.
Twisting its matrix `A` to `det(A) A` kills every scalar matrix over F₃.
This representation therefore descends to the actual projective image; its
kernel remains solvable. The first isomorphism theorem then constructs the
normal layers and the faithful map from their quotient into GL₃(3).

This is the elementary parabolic input to Aschbacher–Smith, Theorem 0.1.2(4),
printed p.4, and condition K, printed pp.4 and 482 of `refs/quasithin.pdf`.
The exhaustive proper-overgroup cover is assembled separately.
-/

namespace Matrix.PSL4Three.ProperOvergroups
namespace SubspaceParabolics

private abbrev F := ZMod 3
private abbrev GLn (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) F

private noncomputable def toMatrices {M : Type*} [AddCommGroup M] [Module F M]
    {n : ℕ} (b : Module.Basis (Fin n) F M) : (M ≃ₗ[F] M) ≃* GLn n :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F M).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

private theorem toMatrices_scalar {M : Type*} [AddCommGroup M] [Module F M]
    {n : ℕ} (b : Module.Basis (Fin n) F M) (f : M ≃ₗ[F] M) (a : Fˣ)
    (hf : ∀ v, f v = (a : F) • v) :
    toMatrices b f = GeneralLinearGroup.scalar (Fin n) a := by
  apply Units.ext
  change LinearMap.toMatrix b b f.toLinearMap = Matrix.scalar (Fin n) (a : F)
  have he : f.toLinearMap = (a : F) • (1 : M →ₗ[F] M) := by
    ext v
    exact hf v
  rw [he, map_smul, LinearMap.toMatrix_one]
  ext i j
  simp [Matrix.one_apply, Matrix.scalar, Matrix.diagonal_apply]

/-- The determinant twist kills scalar matrices in odd dimension three over F₃. -/
private def determinantTwist : GLn 3 →* GLn 3 where
  toFun g := GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det g) * g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, GeneralLinearGroup.scalar_commute, mul_assoc]

private theorem determinantTwist_scalar (a : Fˣ) :
    determinantTwist (GeneralLinearGroup.scalar (Fin 3) a) = 1 := by
  change GeneralLinearGroup.scalar _ (GeneralLinearGroup.det
    (GeneralLinearGroup.scalar (Fin 3) a)) * GeneralLinearGroup.scalar _ a = 1
  rw [GeneralLinearGroup.det_scalar, ← map_mul]
  have h : a ^ Fintype.card (Fin 3) * a = 1 := by
    have ha : ∀ a : Fˣ, a ^ 4 = 1 := by decide
    simpa [pow_succ] using ha a
  rw [h, map_one]

private theorem determinantTwist_ker_isSolvable : Group.IsSolvable determinantTwist.ker := by
  let d := GeneralLinearGroup.det.comp determinantTwist.ker.subtype
  apply Group.isSolvable_of_isSolvable_injective (f := d)
  intro g h he
  apply Subtype.ext
  have hg : GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det g.val) * g.val = 1 :=
    g.property
  have hh : GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det h.val) * h.val = 1 :=
    h.property
  change GeneralLinearGroup.det g.val = GeneralLinearGroup.det h.val at he
  rw [he] at hg
  exact mul_left_cancel (hg.trans hh.symm)

private theorem gl1_isSolvable : Group.IsSolvable (GLn 1) := by
  apply Group.isSolvable_of_comm
  intro g h
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

private theorem gl2_isSolvable : Group.IsSolvable (GLn 2) := by
  let hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
  let : Group.IsNilpotent (QuaternionGroup 2) := hQ.isNilpotent
  let : Group.IsSolvable
      (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3)) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply Group.isSolvable_of_surjective
      (f := GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toMonoidHom)
    exact GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.surjective
  let det := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
  apply Group.isSolvable_of_ker_le_range (SpecialLinearGroup.toGL (R := F)) det
  intro g hg
  let y : Matrix.SpecialLinearGroup (Fin 2) F := ⟨(g : Matrix (Fin 2) (Fin 2) F), by
    have h := congr_arg Units.val hg
    change Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 at h
    exact h⟩
  refine ⟨y, ?_⟩
  apply Units.ext
  rfl

private theorem linearEquiv_isSolvable {M : Type*} [AddCommGroup M] [Module F M]
    [Module.Finite F M] {n : ℕ} (hn : Module.finrank F M = n)
    (hs : Group.IsSolvable (GLn n)) : Group.IsSolvable (M ≃ₗ[F] M) := by
  let := hs
  exact Group.isSolvable_of_isSolvable_injective
    (f := (toMatrices (Module.finBasisOfFinrankEq F M hn)).toMonoidHom)
    (toMatrices _).injective

open scoped Pointwise

private theorem map_eq (W : Submodule (ZMod 3) Vec) (g : parabolic W) :
    W.map (SpecialLinearGroup.toLin' g.val).toLinearMap = W := by
  apply SetLike.coe_injective
  change (fun v => g.val • v) '' (W : Set Vec) = (W : Set Vec)
  exact MulAction.mem_stabilizer_iff.mp g.property

private noncomputable def subspaceAction (W : Submodule (ZMod 3) Vec) :
    parabolic W →* (W ≃ₗ[ZMod 3] W) where
  toFun g := (SpecialLinearGroup.toLin' g.val).ofSubmodules W W (map_eq W g)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change SpecialLinearGroup.toLin' (1 : SL) (v : Vec) = v
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change SpecialLinearGroup.toLin' (g.val * h.val) v =
      SpecialLinearGroup.toLin' g.val (SpecialLinearGroup.toLin' h.val v)
    rw [map_mul]
    rfl

private noncomputable def quotientAction (W : Submodule (ZMod 3) Vec) :
    parabolic W →* ((Vec ⧸ W) ≃ₗ[ZMod 3] (Vec ⧸ W)) where
  toFun g := Submodule.Quotient.equiv W W (SpecialLinearGroup.toLin' g.val) (map_eq W g)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      change W.mkQ (SpecialLinearGroup.toLin' (1 : SL) (v : Vec)) = W.mkQ v
      simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      change W.mkQ (SpecialLinearGroup.toLin' (g.val * h.val) v) =
        W.mkQ (SpecialLinearGroup.toLin' g.val (SpecialLinearGroup.toLin' h.val v))
      rw [map_mul]
      rfl

private noncomputable def jointAction (W : Submodule (ZMod 3) Vec) :=
  (subspaceAction W).prod (quotientAction W)

private theorem jointAction_ker_isSolvable (W : Submodule (ZMod 3) Vec) :
    Group.IsSolvable (jointAction W).ker := by
  apply Group.isSolvable_of_comm
  intro g h
  have fixed (a : (jointAction W).ker) (v : Vec) (hv : v ∈ W) :
      SpecialLinearGroup.toLin' a.val.val v = v := by
    have ha := congrArg Prod.fst a.property
    exact congrArg Subtype.val (LinearEquiv.congr_fun ha ⟨v, hv⟩)
  have diff (a : (jointAction W).ker) (v : Vec) :
      SpecialLinearGroup.toLin' a.val.val v - v ∈ W := by
    apply (Submodule.Quotient.eq W).mp
    exact LinearEquiv.congr_fun (congrArg Prod.snd a.property) (W.mkQ v)
  apply Subtype.ext
  apply Subtype.ext
  apply SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  change SpecialLinearGroup.toLin' (g.val.val * h.val.val) v =
    SpecialLinearGroup.toLin' (h.val.val * g.val.val) v
  simp only [map_mul, LinearEquiv.mul_apply]
  have hgh := fixed g _ (diff h v)
  have hhg := fixed h _ (diff g v)
  rw [map_sub] at hgh hhg
  calc
    _ = (SpecialLinearGroup.toLin' h.val.val v - v) +
        SpecialLinearGroup.toLin' g.val.val v := sub_eq_iff_eq_add.mp hgh
    _ = (SpecialLinearGroup.toLin' g.val.val v - v) +
        SpecialLinearGroup.toLin' h.val.val v := by abel
    _ = _ := (sub_eq_iff_eq_add.mp hhg).symm

variable {G H K : Type*} [Group G] [Group H] [Group K]

private theorem ker_comp_isSolvable (f : G →* H) (g : H →* K)
    [Group.IsSolvable f.ker] [Group.IsSolvable g.ker] :
    Group.IsSolvable (g.comp f).ker :=
  Subgroup.isSolvable_comap_of_solvable_ker f g.ker

private theorem pair_left_ker_isSolvable (f : G →* H) (g : G →* K)
    [Group.IsSolvable (f.prod g).ker] [Group.IsSolvable K] :
    Group.IsSolvable f.ker := by
  let i : (f.prod g).ker →* f.ker :=
    (f.prod g).ker.subtype.codRestrict _ (by
      intro x
      exact congrArg Prod.fst x.property)
  apply Group.isSolvable_of_ker_le_range i (g.comp f.ker.subtype)
  intro x hx
  exact ⟨⟨x.val, Prod.ext x.property hx⟩, Subtype.ext rfl⟩

private theorem pair_right_ker_isSolvable (f : G →* H) (g : G →* K)
    [Group.IsSolvable (f.prod g).ker] [Group.IsSolvable H] :
    Group.IsSolvable g.ker := by
  let i : (f.prod g).ker →* g.ker :=
    (f.prod g).ker.subtype.codRestrict _ (by
      intro x
      exact congrArg Prod.snd x.property)
  apply Group.isSolvable_of_ker_le_range i (f.comp g.ker.subtype)
  intro x hx
  exact ⟨⟨x.val, Prod.ext hx x.property⟩, Subtype.ext rfl⟩

private theorem ker_postcomp_injective (f : G →* H) (g : H →* K)
    (hg : Function.Injective g) [Group.IsSolvable f.ker] :
    Group.IsSolvable (g.comp f).ker := by
  have he : (g.comp f).ker = f.ker := by
    ext x
    change g (f x) = 1 ↔ f x = 1
    rw [← map_one g, hg.eq_iff]
  rw [he]
  infer_instance

private theorem descend_solvable_ker (p : G →* H) (hp : Function.Surjective p)
    (f : G →* K) (hpf : p.ker ≤ f.ker) [Group.IsSolvable f.ker] :
    Theory.GroupTheory.SolvableLayersEmbedding H K := by
  let d : H →* K := p.liftOfSurjective hp ⟨f, hpf⟩
  have hd (x : G) : d (p x) = f x := by simp [d]
  let j : f.ker →* d.ker :=
    (p.comp f.ker.subtype).codRestrict _ (fun x => by
      change d (p x.val) = 1
      rw [hd]
      exact x.property)
  have hj : Function.Surjective j := by
    intro y
    obtain ⟨x, hx⟩ := hp y.val
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x = 1
    rw [← hd, hx]
    exact y.property
  let : Group.IsSolvable d.ker := Group.isSolvable_of_surjective hj
  exact Theory.GroupTheory.SolvableLayersEmbedding.of_solvable_ker d

private noncomputable def projectParabolicMap (W : Submodule F Vec) :
    parabolic W →* projectiveParabolic W :=
  (project.comp (parabolic W).subtype).codRestrict _ (fun g => ⟨g.val, g.property, rfl⟩)

private theorem projectParabolicMap_surjective (W : Submodule F Vec) :
    Function.Surjective (projectParabolicMap W) := by
  intro y
  obtain ⟨g, hg, hgy⟩ := y.property
  exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩

private theorem central_scalar (W : Submodule F Vec) (g : parabolic W)
    (hg : g ∈ (projectParabolicMap W).ker) :
    ∃ a : Fˣ, ∀ v, SpecialLinearGroup.toLin' g.val v = (a : F) • v := by
  have hp : project g.val = 1 := congrArg Subtype.val hg
  obtain ⟨a, ha, he⟩ := SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff _).mp hp)
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz] at ha
  refine ⟨Units.mk0 a ha0, ?_⟩
  intro v
  change (g.val : Matrix (Fin 4) (Fin 4) F) *ᵥ v = a • v
  rw [← he]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

private theorem layers_of_three_action (W : Submodule F Vec)
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Finite F M]
    (hM : Module.finrank F M = 3) (f : parabolic W →* (M ≃ₗ[F] M))
    [Group.IsSolvable f.ker]
    (hc : ∀ g ∈ (projectParabolicMap W).ker, ∃ a : Fˣ, ∀ v, f g v = (a : F) • v) :
    HasSmallLayers (projectiveParabolic W) := by
  let b := Module.finBasisOfFinrankEq F M hM
  let e := toMatrices b
  let r := e.toMonoidHom.comp f
  let : Group.IsSolvable r.ker := ker_postcomp_injective f e.toMonoidHom e.injective
  let : Group.IsSolvable determinantTwist.ker := determinantTwist_ker_isSolvable
  let : Group.IsSolvable (determinantTwist.comp r).ker :=
    ker_comp_isSolvable r determinantTwist
  apply Or.inl
  apply descend_solvable_ker (projectParabolicMap W) (projectParabolicMap_surjective W)
    (determinantTwist.comp r)
  intro g hg
  obtain ⟨a, ha⟩ := hc g hg
  change determinantTwist (toMatrices b (f g)) = 1
  rw [toMatrices_scalar b (f g) a ha, determinantTwist_scalar]

private theorem line_layers (W : Submodule F Vec) (hW : Module.finrank F W = 1) :
    HasSmallLayers (projectiveParabolic W) := by
  have hdim := W.finrank_quotient_add_finrank
  have hQ : Module.finrank F (Vec ⧸ W) = 3 := by
    simpa [hW, Vec, Module.finrank_pi, F] using hdim
  let : Group.IsSolvable (W ≃ₗ[F] W) := linearEquiv_isSolvable hW gl1_isSolvable
  let : Group.IsSolvable ((subspaceAction W).prod (quotientAction W)).ker :=
    jointAction_ker_isSolvable W
  let : Group.IsSolvable (quotientAction W).ker :=
    pair_right_ker_isSolvable (subspaceAction W) (quotientAction W)
  apply layers_of_three_action W hQ (quotientAction W)
  intro g hg
  obtain ⟨a, ha⟩ := central_scalar W g hg
  refine ⟨a, ?_⟩
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change W.mkQ (SpecialLinearGroup.toLin' g.val v) = (a : F) • W.mkQ v
    rw [ha, map_smul]

private theorem hyperplane_layers (W : Submodule F Vec) (hW : Module.finrank F W = 3) :
    HasSmallLayers (projectiveParabolic W) := by
  have hdim := W.finrank_quotient_add_finrank
  have hQ : Module.finrank F (Vec ⧸ W) = 1 := by
    simpa [hW, Vec, Module.finrank_pi, F] using hdim
  let : Group.IsSolvable ((Vec ⧸ W) ≃ₗ[F] (Vec ⧸ W)) :=
    linearEquiv_isSolvable hQ gl1_isSolvable
  let : Group.IsSolvable ((subspaceAction W).prod (quotientAction W)).ker :=
    jointAction_ker_isSolvable W
  let : Group.IsSolvable (subspaceAction W).ker :=
    pair_left_ker_isSolvable (subspaceAction W) (quotientAction W)
  apply layers_of_three_action W hW (subspaceAction W)
  intro g hg
  obtain ⟨a, ha⟩ := central_scalar W g hg
  refine ⟨a, ?_⟩
  intro v
  apply Subtype.ext
  exact ha v

private theorem plane_layers (W : Submodule F Vec) (hW : Module.finrank F W = 2) :
    HasSmallLayers (projectiveParabolic W) := by
  have hdim := W.finrank_quotient_add_finrank
  have hQ : Module.finrank F (Vec ⧸ W) = 2 := by
    simpa [hW, Vec, Module.finrank_pi, F] using hdim
  let : Group.IsSolvable (W ≃ₗ[F] W) := linearEquiv_isSolvable hW gl2_isSolvable
  let : Group.IsSolvable ((Vec ⧸ W) ≃ₗ[F] (Vec ⧸ W)) :=
    linearEquiv_isSolvable hQ gl2_isSolvable
  let : Group.IsSolvable (jointAction W).ker := jointAction_ker_isSolvable W
  let : Group.IsSolvable (parabolic W) :=
    Group.isSolvable_of_ker_le_range (jointAction W).ker.subtype (jointAction W) (by simp)
  let : Group.IsSolvable (projectiveParabolic W) :=
    Group.isSolvable_of_surjective (projectParabolicMap_surjective W)
  exact Or.inl (Theory.GroupTheory.SolvableLayersEmbedding.of_solvable _ _)

end SubspaceParabolics

/-- Every nonzero proper subspace stabilizer has actual solvable normal layers
with remaining quotient faithfully represented in one of the small targets. -/
public theorem subspaceParabolic_hasSmallLayers (W : Submodule (ZMod 3) Vec)
    (h0 : W ≠ ⊥) (h4 : W ≠ ⊤) : HasSmallLayers (projectiveParabolic W) := by
  have hpos : 0 < Module.finrank (ZMod 3) W :=
    Nat.pos_of_ne_zero (fun h => h0 (Submodule.finrank_eq_zero.mp h))
  have hlt : Module.finrank (ZMod 3) W < 4 := by
    have h := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr h4)
    simpa [Vec, Module.finrank_pi] using h
  interval_cases hd : Module.finrank (ZMod 3) W
  · exact SubspaceParabolics.line_layers W hd
  · exact SubspaceParabolics.plane_layers W hd
  · exact SubspaceParabolics.hyperplane_layers W hd

end Matrix.PSL4Three.ProperOvergroups
