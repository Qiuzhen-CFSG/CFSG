module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalModuleSetup
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.Representation.CommutingCubicCentralCover
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerNonFF

/-!
# Literal field-four orthogonal identifications and central covers

Finite-field uniqueness and determinant coordinates transport an actual
orthogonal identification to the carrier used in the source contradiction.
A commutator-generated central cover of this module has zero kernel:
fixed-point-free cubic matrices in its two commuting factors apply the
proved cubic-trace splitting lemma. Finally the full-normalizer rank bound
excludes FF modules for any ambient action containing this normal model.
These results transport or lift an identification; they do not construct
one from the source hypotheses.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953; D.3.7 and
Remark I.1.5, printed pp.197–199 and408.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

private def slFieldEquiv {F E : Type*} [Field F] [Field E]
    (f : F ≃+* E) : SL(2,F) ≃* SL(2,E) where
  toFun := Matrix.SpecialLinearGroup.map f.toRingHom
  invFun := Matrix.SpecialLinearGroup.map f.symm.toRingHom
  left_inv g := by ext i j; exact f.symm_apply_apply (g.val i j)
  right_inv g := by ext i j; exact f.apply_symm_apply (g.val i j)
  map_mul' := (Matrix.SpecialLinearGroup.map f.toRingHom).map_mul

private def matrixFieldEquiv {F E : Type*} [Field F] [Field E]
    [Algebra (ZMod 2) F] [Algebra (ZMod 2) E] (f : F ≃+* E) :
    Mat (F := F) ≃ₗ[ZMod 2] Mat (F := E) :=
  let a := f.mapMatrix.toAddEquiv
  LinearEquiv.ofBijective (a.toAddMonoidHom.toZModLinearMap 2) a.bijective

private theorem matrixFieldEquiv_intertwines {F E : Type*} [Field F] [Field E]
    [Algebra (ZMod 2) F] [Algebra (ZMod 2) E] (f : F ≃+* E)
    (g : PairSL (F := F)) (v : Mat (F := F)) :
    matrixFieldEquiv f (ClassicalOrthogonal.FourPlusMatrix.representation g v) =
      ClassicalOrthogonal.FourPlusMatrix.representation ((slFieldEquiv f).prodCongr (slFieldEquiv f) g) (matrixFieldEquiv f v) := by
  change (g.1.val * v * g.2⁻¹.val).map f =
    (slFieldEquiv f g.1).val * v.map f * (slFieldEquiv f g.2)⁻¹.val
  rw [Matrix.map_mul, Matrix.map_mul]
  change _ = g.1.val.map f * v.map f * (slFieldEquiv f g.2)⁻¹.val
  rw [← map_inv]
  rfl

/-- Transfer a genuine whole-module orthogonal identification over a field
of order four to the concrete carrier used by the source contradiction. -/
theorem orthogonalFour_of_identification
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (N : Subgroup D)
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (hF : Nat.card F = 4)
    (d : F918Sections.Refinement.OrthogonalIdentification ρ N F) :
    HasOrthogonalFourOrbit ρ N := by
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* OrthogonalEight.F := FiniteField.ringEquivOfCardEq
    (by simpa only [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field] using hF)
  let j := (slFieldEquiv f).prodCongr (slFieldEquiv f)
  let a := (d.groupEquiv.trans (projectiveEquiv (F := F)).symm).trans
    (j.trans Binary.orthogonalEquiv)
  let c := (coordinates (F := F)).restrictScalars (ZMod 2)
  let b := ((d.linearEquiv.trans c).trans (matrixFieldEquiv f)).trans
    Binary.binaryCoordinates.symm
  refine ⟨a, b, ?_⟩
  intro g v
  apply Binary.binaryCoordinates.injective
  simp only [b, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change matrixFieldEquiv f (coordinates (d.linearEquiv (ρ g v))) =
    Binary.binaryCoordinates (OrthogonalEight.action (a g) (b v))
  rw [d.equivariant]
  have hc : coordinates (F918Sections.Refinement.projectiveNatural F
      (d.groupEquiv g) (d.linearEquiv v)) =
      ClassicalOrthogonal.FourPlusMatrix.representation ((projectiveEquiv (F := F)).symm (d.groupEquiv g))
        (coordinates (d.linearEquiv v)) := by
    change coordinates (projectiveElementaryNatural (formD 2 F)
      (d.groupEquiv g) (d.linearEquiv v)) = _
    simpa only [MulEquiv.apply_symm_apply] using
      projectiveEquiv_coordinates ((projectiveEquiv (F := F)).symm (d.groupEquiv g))
        (d.linearEquiv v)
  rw [hc, matrixFieldEquiv_intertwines]
  change ClassicalOrthogonal.FourPlusMatrix.representation (j ((projectiveEquiv (F := F)).symm (d.groupEquiv g)))
      (matrixFieldEquiv f (coordinates (d.linearEquiv v))) =
    Binary.binaryCoordinates (ClassicalOrthogonal.projectiveElementaryNatural
      (ClassicalOrthogonal.formD 2 OrthogonalEight.F)
      (Binary.orthogonalEquiv (j ((projectiveEquiv (F := F)).symm (d.groupEquiv g)))) (b v))
  rw [Binary.binaryCoordinates_projective_equivariant]
  change _ = Binary.action _ (Binary.binaryCoordinates (Binary.binaryCoordinates.symm _))
  rw [LinearEquiv.apply_symm_apply]
  rfl

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

private def cubic : SpecialLinearGroup (Fin 2) Binary.F :=
  ⟨!![0,1;1,1], by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩

private theorem cubic_pow_three : cubic ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  apply Subtype.ext
  change (cubic * cubic * cubic).val = (1 : SpecialLinearGroup (Fin 2) Binary.F).val
  change !![0,1;1,1] * !![0,1;1,1] * !![0,1;1,1] = (1 : Matrix (Fin 2) (Fin 2) Binary.F)
  funext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]

private theorem cubic_left_fixed (v : Binary.V)
    (h : Binary.action (cubic,1) v = v) : v = 0 := by
  have he : cubic.val * v = v := by
    change cubic.val * v * ((1 : SpecialLinearGroup (Fin 2) Binary.F)⁻¹).val = v at h
    rw [inv_one] at h
    change cubic.val * v * (1 : Matrix (Fin 2) (Fin 2) Binary.F) = v at h
    simpa only [mul_one] using h
  have h0 (j : Fin 2) : v 1 j = v 0 j := by
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using
      congrArg (fun w : Binary.V => w 0 j) he
  have h1 (j : Fin 2) : v 0 j = 0 := by
    have hh := congrArg (fun w : Binary.V => w 1 j) he
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using hh
  funext i j
  fin_cases i
  · exact h1 j
  · exact (h0 j).trans (h1 j)

private theorem cubic_right_fixed (v : Binary.V)
    (h : Binary.action (1,cubic) v = v) : v = 0 := by
  have he : v = v * cubic.val := by
    have hh := congrArg (fun w : Binary.V => w * cubic.val) h
    change ((1 : SpecialLinearGroup (Fin 2) Binary.F).val * v * cubic⁻¹.val) * cubic.val = _ at hh
    change (1 * v * cubic⁻¹.val) * cubic.val = _ at hh
    rw [one_mul, mul_assoc, show cubic⁻¹.val * cubic.val = 1 from
      congrArg Subtype.val (inv_mul_cancel cubic), mul_one] at hh
    exact hh
  have h0 (i : Fin 2) : v i 0 = v i 1 := by
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using
      congrArg (fun w : Binary.V => w i 0) he
  have h1 (i : Fin 2) : v i 0 = 0 := by
    have hh := congrArg (fun w : Binary.V => w i 1) he.symm
    simpa [cubic,Matrix.mul_apply,Fin.sum_univ_two] using hh
  funext i j
  fin_cases j
  · exact h1 i
  · exact (h0 i).symm.trans (h1 i)

/-- A commutator-generated central cover of the literal orthogonal module
has zero kernel. Commuting fixed-free cubic actors give the splitting;
no cohomology, semisimplicity or extension-class premise is assumed. -/
theorem orthogonal_quotient_is_whole
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (N : Subgroup D) (W : Subrepresentation ρ)
    (hc : W.toSubmodule ≤ fixedSpace ρ N)
    (hfull : subspaceCommutator ρ ⊤ N = ⊤)
    (hm : HasOrthogonalFourOrbit W.quotientRepresentation N) :
    W = ⊥ ∧ HasOrthogonalFourOrbit ρ N := by
  obtain ⟨f,e,he⟩ := hm
  let a : Binary.G ≃* N := Binary.orthogonalEquiv.trans f.symm
  let τ : Representation (ZMod 2) Binary.G U := ρ.comp (N.subtype.comp a.toMonoidHom)
  let b := e.trans Binary.binaryCoordinates
  let p : τ.IntertwiningMap Binary.action := {
    toLinearMap := b.toLinearMap.comp W.toSubmodule.mkQ
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro u
      change Binary.binaryCoordinates (e (W.toSubmodule.mkQ (ρ (a g) u))) = _
      rw [← W.quotientRepresentation_mk,he]
      change Binary.binaryCoordinates (projectiveElementaryNatural
        (formD 2 Binary.F) (f (a g)) (e (W.toSubmodule.mkQ u))) = _
      have ha : f (a g) = Binary.orthogonalEquiv g := f.apply_symm_apply _
      rw [ha,Binary.binaryCoordinates_projective_equivariant]
      rfl }
  have hp : OneCohomology.IsCover p := by
    refine ⟨b.surjective.comp W.toSubmodule.mkQ_surjective, ?_, ?_⟩
    · intro u hu g
      have hq : W.toSubmodule.mkQ u = 0 :=
        b.injective (show b (W.toSubmodule.mkQ u) = b 0 from hu.trans b.map_zero.symm)
      exact hc ((Submodule.Quotient.mk_eq_zero _).mp hq) (a g)
    · have hle : subspaceCommutator ρ ⊤ N ≤ Coinvariants.ker τ := by
        apply Submodule.span_le.mpr
        rintro _ ⟨g,hg,u,_,rfl⟩
        obtain ⟨j,hj⟩ := a.surjective ⟨g,hg⟩
        have hval : (a j : D) = g := congrArg Subtype.val hj
        rw [← hval]
        exact Coinvariants.sub_mem_ker j u
      exact top_unique (hfull ▸ hle)
  have hinj := OneCohomology.injective_of_cover_product_cubics p hp cubic
    cubic_pow_three cubic cubic_left_fixed cubic_right_fixed
  have hW : W = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro u hu
    have hq : W.toSubmodule.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hu
    apply hinj
    change b (W.toSubmodule.mkQ u) = b (W.toSubmodule.mkQ 0)
    simp only [hq,map_zero]
  let q := LinearEquiv.ofBijective W.toSubmodule.mkQ
    ⟨fun x y h => hinj (congrArg b h), W.toSubmodule.mkQ_surjective⟩
  refine ⟨hW,f,q.trans e,?_⟩
  intro g u
  change e (W.toSubmodule.mkQ (ρ g u)) = _
  rw [← W.quotientRepresentation_mk]
  exact he g _

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix

/-- A normally embedded literal orthogonal field-four action excludes FF
modules even when the ambient action has kernel. -/
theorem orthogonal_image_not_ff
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (N : Subgroup D) [N.Normal]
    (hm : HasOrthogonalFourOrbit ρ N) :
    ¬ IsFFModule (imageRepresentation ρ) := by
  obtain ⟨f,e,he⟩ := hm
  let a := f.trans Binary.orthogonalEquiv.symm
  let b : Representation.Equiv (ρ.comp N.subtype) (Binary.action.comp a.toMonoidHom) := {
    __ := e.trans Binary.binaryCoordinates
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro u
      change Binary.binaryCoordinates (e (ρ g u)) = _
      rw [he]
      have hf : f g = Binary.orthogonalEquiv (a g) :=
        (Binary.orthogonalEquiv.apply_symm_apply (f g)).symm
      change Binary.binaryCoordinates (projectiveElementaryNatural
        (formD 2 Binary.F) (f g) (e u)) = _
      rw [hf,Binary.binaryCoordinates_projective_equivariant]
      rfl }
  let : N.subtype.range.Normal := by
    rw [N.range_subtype]
    infer_instance
  exact Binary.image_not_ff_of_marked_normal_range ρ N.subtype a.toMonoidHom a.surjective b

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
