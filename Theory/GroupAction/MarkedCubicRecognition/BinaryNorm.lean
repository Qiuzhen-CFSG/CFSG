module
public import Theory.GroupAction.MarkedCubicRecognition.Models
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod
public import Theory.GroupAction.CardFourCubic
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Cubic norms in a binary Heisenberg action

The product of the two cubic norm operators detects the central norm.
Consequently a vector fixed by the second cubic and killed by the first
cubic norm is fixed by the center. A nontrivial cubic action on a literal
four-group supplies the required vanishing norm.

This is the binary action calculation used to exclude the marked
Heisenberg alternative in Aschbacher–Smith, 14.5.13 and the following
proof of 14.5.3, printed p.1017, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace MarkedCubicRecognition
private theorem mul_coordinates (a b c d e f : ZMod 3) :
    (HeisenbergPrime.mk a b c) * (HeisenbergPrime.mk d e f) =
      HeisenbergPrime.mk (a+d) (b+e) (c+f+a*e) := rfl
private theorem one_coordinates : (1 : HeisenbergPrime 3) = ⟨0,0,0⟩ := rfl

private def normElement (x : HeisenbergPrime 3) : MonoidAlgebra (ZMod 2) (HeisenbergPrime 3) :=
  MonoidAlgebra.single 1 1 + MonoidAlgebra.single x 1 + MonoidAlgebra.single (x ^ 2) 1
private def centralGenerator : HeisenbergPrime 3 := ⟨0,0,1⟩

private theorem norm_identity :
    normElement rightGenerator * normElement leftGenerator * normElement rightGenerator =
      normElement rightGenerator + normElement rightGenerator + normElement rightGenerator +
        normElement centralGenerator *
        (MonoidAlgebra.single leftGenerator 1 + MonoidAlgebra.single (leftGenerator ^ 2) 1) *
          normElement rightGenerator := by
  simp only [normElement,add_mul,mul_add,MonoidAlgebra.single_mul_single,
    one_mul,mul_one,pow_two,leftGenerator,rightGenerator,centralGenerator,
    mul_coordinates]
  norm_num
  simp only [show (3 : ZMod 3) = 0 from rfl, show (4 : ZMod 3) = 1 from rfl, one_coordinates]
  abel

private theorem central_norm_fixed :
    MonoidAlgebra.single centralGenerator (1 : ZMod 2) * normElement centralGenerator =
      normElement centralGenerator := by
  simp only [normElement,mul_add,MonoidAlgebra.single_mul_single,
    mul_one,pow_two,centralGenerator,mul_coordinates]
  norm_num
  rw [one_coordinates]
  abel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A vector fixed by the second cubic and killed by the first cubic norm
is fixed by the Heisenberg center. -/
theorem heisenberg_cubic_norm_center_fixed
    (ρ : Representation (ZMod 2) (HeisenbergPrime 3) V) (v : V)
    (hy : ρ rightGenerator v = v)
    (hx : v + ρ leftGenerator v + ρ (leftGenerator ^ 2) v = 0) :
    ∀ z ∈ center (HeisenbergPrime 3), ρ z v = v := by
  have hy2 : ρ (rightGenerator ^ 2) v = v := by
    rw [pow_two,map_mul,Module.End.mul_apply,hy,hy]
  have hny : ρ.asAlgebraHom (normElement rightGenerator) v = v := by
    simp only [normElement,map_add,LinearMap.add_apply,asAlgebraHom_single,
      one_smul,map_one,Module.End.one_apply,hy,hy2]
    rw [ZModModule.add_self,zero_add]
  have hnx : ρ.asAlgebraHom (normElement leftGenerator) v = 0 := by
    simpa only [normElement,map_add,LinearMap.add_apply,asAlgebraHom_single,
      one_smul,map_one,Module.End.one_apply] using hx
  let w := ρ.asAlgebraHom
    (MonoidAlgebra.single leftGenerator 1 + MonoidAlgebra.single (leftGenerator ^ 2) 1) v
  have hv : 0 = v + ρ.asAlgebraHom (normElement centralGenerator) w := by
    have hh := congrArg (fun a => ρ.asAlgebraHom a v) norm_identity
    simpa only [map_mul,Module.End.mul_apply,map_add,LinearMap.add_apply,hny,hnx,map_zero,w,ZModModule.add_self,zero_add] using hh
  have hc : ρ centralGenerator v = v := by
    have he := congrArg (fun a => ρ.asAlgebraHom a w) central_norm_fixed
    simp only [map_mul,Module.End.mul_apply,asAlgebraHom_single,one_smul] at he
    have hv' : v = - ρ.asAlgebraHom (normElement centralGenerator) w :=
      eq_neg_of_add_eq_zero_left hv.symm
    rw [hv',map_neg,he]
  intro z hz
  rcases z with ⟨a,b,c⟩
  obtain ⟨ha,hb⟩ := HeisenbergPrime.mem_center_iff _ |>.mp hz
  dsimp at ha hb
  subst a
  subst b
  rcases c with ⟨c,hc3⟩
  interval_cases c
  · exact congrArg (fun g => ρ g v) (show (⟨0,0,0⟩ : HeisenbergPrime 3) = 1 from rfl) |>.trans (by simp)
  · exact hc
  · have he : (⟨0,0,2⟩ : HeisenbergPrime 3) = centralGenerator ^ 2 := by ext <;> norm_num [centralGenerator,pow_two]
    change ρ (⟨0,0,2⟩ : HeisenbergPrime 3) v = v
    rw [he,pow_two,map_mul,Module.End.mul_apply,hc,hc]

open scoped IsMulCommutative in
private theorem cubic_norm_four {P : Type*} [Group P] [Finite P]
    [IsMulCommutative P] (hP : Nat.card P = 4) (a : MulAut P)
    (ha : a ^ 3 = 1) (hne : a ≠ 1) (v : P) :
    v * a v * (a ^ 2) v = 1 := by
  by_contra hn
  apply Theory.GroupAction.CardFourCubic.moves_nonidentity hP a ha hne _ hn
  have hc : a (a (a v)) = v := by
    have hh := congrArg (fun b : MulAut P => b v) ha
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using hh
  simp only [map_mul, pow_two, MulAut.mul_apply]
  rw [hc]
  ac_rfl

/-- The literal invariant plane suffices for the norm relation. -/
theorem heisenberg_center_fixed_of_four_plane
    {W P : Type*} [Group W] [IsElementaryAbelian 2 W]
    [Group P] [Finite P] [IsMulCommutative P]
    (α : HeisenbergPrime 3 →* MulAut W)
    (j : P →* W) (a : MulAut P) (hP : Nat.card P = 4)
    (ha : a ^ 3 = 1) (hne : a ≠ 1)
    (hequiv : ∀ w, j (a w) = α leftGenerator (j w))
    (v : P) (hy : α rightGenerator (j v) = j v) :
    ∀ z ∈ center (HeisenbergPrime 3), α z (j v) = j v := by
  let ρ := elementaryRepresentation (p := 2) α
  have hx : Additive.ofMul (j v) + ρ leftGenerator (Additive.ofMul (j v)) +
      ρ (leftGenerator ^ 2) (Additive.ofMul (j v)) = 0 := by
    have hh := congrArg j (cubic_norm_four hP a ha hne v)
    simp only [map_mul, map_one] at hh
    apply Additive.toMul.injective
    change j v * α leftGenerator (j v) * α (leftGenerator ^ 2) (j v) = 1
    rw [pow_two, map_mul, MulAut.mul_apply, ←hequiv, ←hequiv]
    exact hh
  have hc := heisenberg_cubic_norm_center_fixed ρ (Additive.ofMul (j v)) hy hx
  intro z hz
  exact congrArg Additive.toMul (hc z hz)

end MarkedCubicRecognition
