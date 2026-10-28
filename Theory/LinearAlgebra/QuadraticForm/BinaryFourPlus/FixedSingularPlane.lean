module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularPlaneCubic
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SwappingTwelve
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane

/-! A nonidentity isometry fixing a singular plane pointwise fixes exactly
that plane and swaps the two anisotropic coordinates. The finite certificate
uses the sixteen vectors and seventy-two actors, with singular independent
pairs as its only inputs. Source:14.3.18(6), the uniqueness of A in AU. -/

public section
open Subgroup Module
namespace BinaryFourPlus
private instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).injective.decidableEq
private instance : Fintype Wreath := Fintype.ofEquiv _
  (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) C2).symm
private def eval (a:Wreath) (v:V) : V :=
  if a.right=1 then (planeLinear (a.left 1) v.1,planeLinear (a.left swapIndex) v.2)
  else (planeLinear (a.left 1) v.2,planeLinear (a.left swapIndex) v.1)
private theorem eval_eq (a:Wreath) (v:V) : eval a v=(wreathToIsometry a).val v :=
  (wreathToIsometry_apply a v).symm
private def independentSingular (v w:V) : Prop :=
  v≠0 ∧ w≠0 ∧ v≠w ∧ q v=0 ∧ q w=0 ∧ q (v+w)=0
private instance (v w:V) : Decidable (independentSingular v w) :=
  inferInstanceAs (Decidable (_∧_∧_∧_∧_∧_))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 2000 in
private theorem fixed_plane_certificate : ∀v w:V, independentSingular v w →
    ∀a:Wreath, a≠1 → eval a v=v → eval a w=w →
      a.right≠1 ∧ ∀z:V,eval a z=z → z=0 ∨ z=v ∨ z=w ∨ z=v+w := by
  decide +kernel

/-- A nonidentity actor fixing a singular plane pointwise fixes exactly that
plane and lies in the swapping coset of the literal wreath action. -/
theorem fixed_singular_plane
    (a:Wreath) (ha:a≠1) (S:Submodule (ZMod 2) V)
    (hd:2≤finrank (ZMod 2) S) (hs:∀v∈S,q v=0)
    (hi:∀v∈S,(wreathToIsometry a).val v=v) :
    a.right≠1 ∧ ∀z:V,(wreathToIsometry a).val z=z → z∈S := by
  classical
  have hS:S≠⊥ := by intro he;rw [he,finrank_bot] at hd;omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hw:∃w∈S,w≠0∧v≠w := by
    by_contra! hh
    have hle:finrank (ZMod 2) S≤1 := by
      apply finrank_le_one (⟨v,hv⟩:S)
      intro w
      by_cases hw0:(w:V)=0
      · exact ⟨0,Subtype.ext (by simpa using hw0.symm)⟩
      · exact ⟨1,Subtype.ext (by simpa using hh w w.property hw0)⟩
    omega
  obtain ⟨w,hw,hw0,hvw⟩ := hw
  obtain ⟨hpar,hfix⟩ := fixed_plane_certificate v w
    ⟨hv0,hw0,hvw,hs v hv,hs w hw,hs _ (S.add_mem hv hw)⟩ a ha
    ((eval_eq a v).trans (hi v hv)) ((eval_eq a w).trans (hi w hw))
  refine ⟨hpar,?_⟩
  intro z hz
  rcases hfix z ((eval_eq a z).trans hz) with rfl|rfl|rfl|rfl
  · exact S.zero_mem
  · exact hv
  · exact hw
  · exact S.add_mem hv hw
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem swapping_centralizer_card_certificate : ∀a:Wreath,
    a.right≠1 → a^2=1 → Fintype.card {x:Wreath // x*a=a*x}=12 := by
  decide +kernel

/-- A swapping involution has the direct-product centralizer C₂×S₃. -/
theorem swapping_involution_centralizer_equiv (a:Wreath) (ha:a.right≠1) (ha2:a^2=1) :
    Nonempty (centralizer ({a}:Set Wreath) ≃* (C2 × Equiv.Perm (Fin 3))) := by
  let C := centralizer ({a}:Set Wreath)
  have hC:Nat.card C=12 := by
    let j:C ≃ {x:Wreath // x*a=a*x} :=
      Equiv.subtypeEquivRight (fun _=>mem_centralizer_singleton_iff)
    rw [Nat.card_congr j,Nat.card_eq_fintype_card]
    exact swapping_centralizer_card_certificate a ha ha2
  obtain ⟨e,_⟩ := swapping_twelve_equiv C hC
    (⟨a,mem_centralizer_singleton_iff.mpr rfl⟩:C) ha
  exact ⟨e.trans MulEquiv.prodComm⟩
end BinaryFourPlus
