module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.FactorSign
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane
public import Mathlib.LinearAlgebra.Dimension.Finite
/-!
# The factor sign of a singular-plane stabilizer

An isometry preserving a totally singular plane in the binary plus space has
trivial product of its two factor signs. A finite certificate checks two
independent singular vectors and their mixed sums with the images. The final
lemma applies that certificate to any invariant singular submodule of dimension
at least two, retaining the wreath convention without a sign for interchanging
planes.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup
namespace BinaryFourPlus
private instance : DecidableEq Wreath := (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm
private def eval (a : Wreath) (v : V) : V :=
  if a.right=1 then (planeLinear (a.left 1) v.1,planeLinear (a.left swapIndex) v.2)
  else (planeLinear (a.left 1) v.2,planeLinear (a.left swapIndex) v.1)
private theorem eval_eq (a : Wreath) (v : V) : eval a v=(wreathToIsometry a).val v :=
  (wreathToIsometry_apply a v).symm
private def singularPair (v w : V) : Prop :=
  v≠0 ∧ w≠0 ∧ v≠w ∧ q v=0 ∧ q w=0 ∧ q (v+w)=0
private instance (v w : V) : Decidable (singularPair v w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
private def compatiblePair (a : Wreath) (v w : V) : Prop :=
  q (v+eval a v)=0 ∧ q (w+eval a v)=0 ∧ q (v+eval a w)=0 ∧ q (w+eval a w)=0
private instance (a : Wreath) (v w : V) : Decidable (compatiblePair a v w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
private theorem pair_sign_certificate : ∀ v w : V, singularPair v w →
    ∀ a : Wreath, compatiblePair a v w → factorSign a=1 := by
  decide +kernel

theorem invariant_singular_plane_factorSign_one (W : Submodule (ZMod 2) V)
    (hd : 2≤Module.finrank (ZMod 2) W) (hs : ∀v∈W,q v=0)
    (a : Wreath) (hi : ∀v∈W,(wreathToIsometry a).val v∈W) : factorSign a=1 := by
  classical
  have hW : W≠⊥ := by intro he;rw [he,finrank_bot] at hd;omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : ∃w∈W,w≠0 ∧ v≠w := by
    by_contra! hh
    have hle : Module.finrank (ZMod 2) W≤1 := by
      apply finrank_le_one (⟨v,hv⟩:W)
      intro w
      by_cases hw0 : (w:V)=0
      · exact ⟨0,Subtype.ext (by simpa using hw0.symm)⟩
      · exact ⟨1,Subtype.ext (by simpa using hh w w.property hw0)⟩
    omega
  obtain ⟨w,hw,hw0,hvw⟩ := hw
  apply pair_sign_certificate v w ⟨hv0,hw0,hvw,hs v hv,hs w hw,hs _ (W.add_mem hv hw)⟩ a
  change q (v+eval a v)=0 ∧ q (w+eval a v)=0 ∧
    q (v+eval a w)=0 ∧ q (w+eval a w)=0
  simp only [eval_eq]
  exact ⟨hs _ (W.add_mem hv (hi v hv)),hs _ (W.add_mem hw (hi v hv)),
    hs _ (W.add_mem hv (hi w hw)),hs _ (W.add_mem hw (hi w hw))⟩
end BinaryFourPlus
