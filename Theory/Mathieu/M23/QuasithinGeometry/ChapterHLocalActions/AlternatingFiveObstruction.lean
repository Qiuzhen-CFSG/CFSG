module
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.HexSemilinear
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The alternating A₅ module does not occur in the natural ΓL₂(4) plane

Every perfect subgroup of ΓL₂(4) fixes the field coefficients and has
determinant one. Consequently an injective A₅ action in this native
semilinear group is a faithful SL₂ action on the same actual F₄ plane.
The cubic fixed-vector obstruction excludes an equivariant injection of
the alternating five-letter module. This is the quintet-core obstruction
for the original C.3.1 A₅ specialization in M₂₂ and M₂₃.
-/

public section
open Matrix
open scoped MatrixGroups
namespace Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.HexSemilinear
open Representation.SL2FourNatural

theorem no_alternatingFive_natural_injection
    (f : alternatingGroup (Fin 5) →* Gamma) (hf : Function.Injective f)
    (e : BinaryPermutation.natural (Fin 5) →+ V) (he : Function.Injective e)
    (hact : ∀ a v, e (BinaryPermutation.naturalRepresentation (Fin 5) a.val v) =
      natural (f a) (e v)) : False := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hcomm (σ τ : F ≃+* F) : σ * τ = τ * σ := by
    rcases fieldAutomorphism_cases σ with rfl | rfl <;>
      rcases fieldAutomorphism_cases τ with rfl | rfl <;> simp
  let : IsMulCommutative (F ≃+* F) := ⟨⟨hcomm⟩⟩
  let r := SemidirectProduct.rightHom.comp f
  let : Group.IsPerfect r.range := Group.IsPerfect.range r
  have hr (a : alternatingGroup (Fin 5)) : (f a).right = 1 :=
    congrArg Subtype.val (show (⟨r a,⟨a,rfl⟩⟩ : r.range) = 1 from Subsingleton.elim _ _)
  let l : alternatingGroup (Fin 5) →* GL (Fin 2) F :=
    { toFun a := (f a).left
      map_one' := by rw [map_one]; rfl
      map_mul' a b := by
        rw [map_mul]
        change (f a).left * Matrix.GeneralLinearGroup.coefficientAction F (f a).right (f b).left = _
        rw [hr,map_one]
        rfl }
  let d := Matrix.GeneralLinearGroup.det.comp l
  let : Group.IsPerfect d.range := Group.IsPerfect.range d
  have hd (a : alternatingGroup (Fin 5)) : ((l a).val).det = 1 :=
    congrArg (fun x : d.range => (x.val : F))
      (show (⟨d a,⟨a,rfl⟩⟩ : d.range) = 1 from Subsingleton.elim _ _)
  let s : alternatingGroup (Fin 5) →* SL(2,F) :=
    { toFun a := ⟨(l a).val,hd a⟩
      map_one' := by apply Subtype.ext; exact congrArg (fun g : GL (Fin 2) F => g.val) l.map_one
      map_mul' a b := by apply Subtype.ext; exact congrArg (fun g : GL (Fin 2) F => g.val) (l.map_mul a b) }
  have hs : Function.Injective s := by
    intro a b hab
    apply hf
    apply SemidirectProduct.ext
    · apply Units.ext
      exact congrArg Subtype.val hab
    · rw [hr,hr]
  apply BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_natural_injection s hs e he
  intro a v
  rw [hact,natural_apply,hr]
  rfl
end Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.HexSemilinear
