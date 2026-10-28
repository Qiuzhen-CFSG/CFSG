module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.HermitianDescent

/-!
# The original absolute tensor in canonical Hermitian coordinates

Embed the canonical quadratic field in the given splitting field through
the supplied matrix-field embedding. Equal cardinalities identify the
actual Schur field with the canonical Frobenius fixed field, compatibly
with both embeddings. Scalar-extension comparison and descent then give
a binary intertwiner on the original carrier. The dual alternative is
absorbed by inverse transpose of the covering group.

Source: Aschbacher–Smith K.3.2(c), printed pp.454–456, and GLS III 2.8.8.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Representation.HermitianTensorThree

def fieldSL {D E : Type*} [Field D] [Field E] (e : D ≃+* E) :
    SL(3,D) ≃* SL(3,E) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by ext i j; exact e.symm_apply_apply (g.val i j)
  right_inv g := by ext i j; exact e.apply_symm_apply (g.val i j)
  map_mul' := map_mul _

variable (n : ℕ) [NeZero n]
variable {B K : Type*} [Field B] [Field K]

omit [NeZero n] in
theorem naturalOver_precompose (e : E n ≃+* B) (ι : B →+* K) :
    (naturalOver (E n) (ι.comp e.toRingHom)).comp (fieldSL e.symm).toMonoidHom =
      naturalOver B ι := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  change (((g.val.map e.symm.toRingHom).map (ι.comp e.toRingHom)).mulVec v) i =
    ((g.val.map ι).mulVec v) i
  congr 2
  ext i j
  exact congrArg ι (e.apply_symm_apply (g.val i j))

omit [NeZero n] in
theorem twistedOver_precompose (e : E n ≃+* B) (ι : B →+* K)
    (σ : B ≃+* B) (hs : ∀ a, σ a = a ^ (2 ^ n)) :
    (twistedTensorOver (E n) (ι.comp e.toRingHom) (sigma n)).comp
        (fieldSL e.symm).toMonoidHom = twistedTensorOver B ι σ := by
  have he : ((ι.comp e.toRingHom).comp (sigma n).toRingHom).comp e.symm.toRingHom =
      ι.comp σ.toRingHom := by
    ext a
    change ι (e (sigma n (e.symm a))) = ι (σ a)
    rw [show sigma n (e.symm a) = (e.symm a) ^ (2 ^ n) from
      iterateFrobeniusEquiv_def _ _ _ _, map_pow, e.apply_symm_apply, hs]
  have hn := naturalOver_precompose n e ι
  have ht : (naturalOver (E n) ((ι.comp e.toRingHom).comp (sigma n).toRingHom)).comp
      (fieldSL e.symm).toMonoidHom = naturalOver B (ι.comp σ.toRingHom) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    funext i
    change ((((g.val.map e.symm.toRingHom).map
      ((ι.comp e.toRingHom).comp (sigma n).toRingHom))).mulVec v) i =
      ((g.val.map (ι.comp σ.toRingHom)).mulVec v) i
    congr 2
    ext i j
    exact RingHom.congr_fun he (g.val i j)
  change Representation.tprod ((naturalOver (E n) (ι.comp e.toRingHom)).comp
      (fieldSL e.symm).toMonoidHom)
    ((naturalOver (E n) ((ι.comp e.toRingHom).comp (sigma n).toRingHom)).comp
      (fieldSL e.symm).toMonoidHom) = _
  rw [hn, ht]
  rfl

local instance : Module (ZMod 2) (F n) := (fixedBinaryAlgebra n).toModule

/-- The scalar extension of the pulled-back Hermitian model is the given
twisted tensor, with the original coefficient embedding. -/
def hermitianAbsoluteEquiv (e : E n ≃+* B) (ι : B →+* K)
    (σ : B ≃+* B) (hs : ∀ a, σ a = a ^ (2 ^ n)) :
    letI := (ι.comp e.toRingHom).toAlgebra
    letI := ((ι.comp e.toRingHom).comp (F n).subtype).toAlgebra
    (extendScalars K ((action n).comp (fieldSL e.symm).toMonoidHom)).Equiv
      (twistedTensorOver B ι σ) := by
  letI := (ι.comp e.toRingHom).toAlgebra
  letI := ((ι.comp e.toRingHom).comp (F n).subtype).toAlgebra
  letI : IsScalarTower (F n) (E n) K := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  let f := (fieldSL e.symm).toMonoidHom
  let t := (action n).comp f
  let et := precomposeEquiv (HermitianDescent.scalarExtensionTensorRepresentationEquiv n) f
  let eb := precomposeEquiv (twistedTensorBaseChange (K := K) (sigma n)) f
  have hm : (twistedTensorOver (E n) (algebraMap (E n) K) (sigma n)).comp f =
      twistedTensorOver B ι σ := twistedOver_precompose n e ι σ hs
  rw [← hm]
  exact (extendScalars_comp (E n) t (F'' := K)).toRepresentationEquiv.symm.trans
    ((BinaryFieldDescent.extendEquiv et).trans eb)

variable [Finite B] [CharP B 2]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(3,B) V) [IsIrreducible ρ]

omit [CharP B 2] in
/-- The original binary tensor has the canonical Hermitian action after
an actual field identification and, in the dual case, inverse transpose. -/
theorem exists_binary_hermitian_equiv
    (hcard : Nat.card B = 2 ^ (2 * n)) (hdegree : schurDegree ρ = n)
    (hmodel : HasAbsoluteTwistedModel ρ n) :
    ∃ a : Cover n ≃* SL(3,B),
      Nonempty (Representation.Equiv (ρ.comp a.toMonoidHom) (binaryAction n)) := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Fintype (E n) := Fintype.ofFinite (E n)
  let e : E n ≃+* B := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_E n, hcard])
  obtain ⟨σ, hσ, ι, hm⟩ := hmodel
  let K := SplittingField ρ
  let κ : E n →+* K := ι.comp e.toRingHom
  let : CharP K 2 := charP_of_injective_ringHom κ.injective 2
  let : Algebra (E n) K := κ.toAlgebra
  let : Algebra (F n) K := (κ.comp (F n).subtype).toAlgebra
  obtain ⟨s, hs⟩ := FiniteField.exists_compatible_binary_fixedField_equiv
    (algebraMap (SchurField ρ) K) κ (sigma n) n
    (Nat.pos_of_ne_zero (NeZero.ne n))
    (by rw [schurField_natCard ρ, hdegree]) (card_E n)
    (fun a => iterateFrobeniusEquiv_def _ _ _ _)
  change SchurField ρ ≃+* F n at s
  let : Module (F n) V := BinaryFieldDescent.scalarModule ρ s
  let : Finite V := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite (F n) V := Module.Finite.of_finite
  let τ := BinaryFieldDescent.scalarRep ρ s
  let t := (action n).comp (fieldSL e.symm).toMonoidHom
  let eS := BinaryFieldDescent.scalarExtensionEquiv ρ s hs
  let eH := hermitianAbsoluteEquiv n e ι σ hσ
  rcases hm with hm | hm
  · obtain ⟨ea⟩ := hm
    obtain ⟨ed⟩ := BinaryFieldDescent.equiv_of_extendScalars (K := K) τ t
      ⟨eS.symm.trans (ea.trans eH.symm)⟩
    let eb := BinaryFieldDescent.restrictBinaryEquiv ed
    refine ⟨fieldSL e, ⟨.mk eb.toLinearEquiv ?_⟩⟩
    intro g
    apply LinearMap.ext
    intro v
    have hh := LinearMap.congr_fun (eb.isIntertwining' (fieldSL e g)) v
    change eb.toLinearEquiv (ρ (fieldSL e g) v) =
      action n (fieldSL e.symm (fieldSL e g)) (eb.toLinearEquiv v) at hh
    have he : fieldSL e.symm (fieldSL e g) = g := (fieldSL e).left_inv g
    rw [he] at hh
    exact hh
  · obtain ⟨ea⟩ := hm
    let td := t.comp (graph B).toMonoidHom
    let eD := (precomposeEquiv eH (graph B).toMonoidHom).trans
      (tensorOverGraphDual ι σ)
    obtain ⟨ed⟩ := BinaryFieldDescent.equiv_of_extendScalars (K := K) τ td
      ⟨eS.symm.trans (ea.trans eD.symm)⟩
    let eb := BinaryFieldDescent.restrictBinaryEquiv ed
    let a := (fieldSL e).trans (graph B)
    refine ⟨a, ⟨.mk eb.toLinearEquiv ?_⟩⟩
    intro g
    apply LinearMap.ext
    intro v
    have hh := LinearMap.congr_fun (eb.isIntertwining' (a g)) v
    change eb.toLinearEquiv (ρ (a g) v) =
      action n (fieldSL e.symm (graph B (a g))) (eb.toLinearEquiv v) at hh
    have he : fieldSL e.symm (graph B (a g)) = g := by
      change fieldSL e.symm (graph B (graph B (fieldSL e g))) = g
      rw [show graph B (graph B (fieldSL e g)) = fieldSL e g from
        (graph B).left_inv (fieldSL e g)]
      exact (fieldSL e).left_inv g
    rw [he] at hh
    exact hh

end CFSG.Quasithin.ChapterK.Linear.Recognition.TwistedExclusion
