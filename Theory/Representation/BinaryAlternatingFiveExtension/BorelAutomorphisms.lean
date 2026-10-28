module
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel

/-!
# The central twist in the ordinary binary affine overlap

The point stabilizer A₄ acts on the five-point binary core as its full
four-dimensional permutation module. Its additive centralizer consists
of the identity and `x ↦ x + x₄ z`, where `z` is the fixed all-one
four-vector. A three-cycle fixes only four vectors; the orbit of one
basis vector then determines an equivariant additive map.

The second map extends to an automorphism of the actual affine overlap
`BorelModel`. It fixes the two-residual pointwise and sends the chosen
complementary translation `u` to `u + z`. The final theorem applies the
centralizer calculation to a literal overlap automorphism after its
quotient action has been corrected. It does not assert that arbitrary
marked endpoint maps already agree on the overlap.

Source: Aschbacher--Smith 13.5.17, printed p.922, ordinary U₄(2) branch.
This is one input to the endpoint restriction-product calculation.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension.Overlap
open AlternatingFiveFlag AlternatingFiveBorel FiveCentralizerGeometry

private instance : DecidablePred (· ∈ B) := fun g =>
  inferInstanceAs (Decidable (g.val 4=4))
private instance : Fintype B := Subtype.fintype _

private def fixedCubic : B := ⟨⟨Equiv.swap 1 2 * Equiv.swap 2 3, by
  rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩

private theorem fixed_cubic_vectors : ∀ x : Space,
    rho fixedCubic.val.val x=x → x=0 ∨ x=z ∨ x=u ∨ x=u+z := by decide +kernel

private theorem cubic_fixes_u : rho fixedCubic.val.val u=u := by decide +kernel
private theorem move_u : rho c₀.val.val u≠u := by decide +kernel
private theorem u_ne_zero : u≠0 := by decide +kernel

private theorem span : ∀ v : Space, ∃ a b c d : Bool,
    v = (if a then u else 0) + (if b then rho c₀.val.val u else 0) +
      (if c then rho c₁.val.val u else 0) + (if d then rho c₂.val.val u else 0) := by
  decide +kernel

private theorem equivariant_ext (f g : Space →+ Space)
    (hf : ∀ b : B, ∀ x, f (rho b.val.val x)=rho b.val.val (f x))
    (hg : ∀ b : B, ∀ x, g (rho b.val.val x)=rho b.val.val (g x))
    (hu : f u=g u) : f=g := by
  ext x
  obtain ⟨a,b,c,d,rfl⟩ := span x
  simp only [map_add]
  have he (t : Bool) (v : Space) (hv : f v=g v) :
      f (if t then v else 0)=g (if t then v else 0) := by cases t <;> simp [hv]
  rw [he a u hu,
    he b _ (by rw [hf,hg,hu]),
    he c _ (by rw [hf,hg,hu]),
    he d _ (by rw [hf,hg,hu])]

/-- The binary transvection along the marked fixed line. -/
def twist : Space →+ Space where
  toFun x := x + x.val 4 • z
  map_zero' := by simp
  map_add' x y := by
    change (x+y)+(x.val 4+y.val 4) • z = (x+x.val 4 • z)+(y+y.val 4 • z)
    simp only [add_smul]
    abel

theorem twist_equivariant (b : B) (x : Space) :
    twist (rho b.val.val x) = rho b.val.val (twist x) := by
  change rho b.val.val x + (rho b.val.val x).val 4 • z =
    rho b.val.val (x+x.val 4 • z)
  rw [map_add,map_smul, (fixes_z_iff b.val.val).mpr b.property]
  congr 2
  change x.val (b.val.val.symm 4)=x.val 4
  rw [b.val.val.symm_apply_eq.mpr b.property.symm]

/-- The A₄ centralizer of the original additive core has exactly these two actions. -/
theorem centralizer_cases (f : Space ≃+ Space)
    (hf : ∀ b : B, ∀ x, f (rho b.val.val x)=rho b.val.val (f x)) :
    (∀ x, f x=x) ∨ (∀ x, f x=twist x) := by
  have hfixed : rho fixedCubic.val.val (f u)=f u := by rw [←hf,cubic_fixes_u]
  rcases fixed_cubic_vectors (f u) hfixed with h|h|h|h
  · exact (u_ne_zero (f.injective (h.trans f.map_zero.symm))).elim
  · have he : f (rho c₀.val.val u)=f u := by rw [hf,h,(fixes_z_iff c₀.val.val).mpr c₀.property]
    exact (move_u (f.injective he)).elim
  · left
    have he := equivariant_ext f.toAddMonoidHom (AddMonoidHom.id Space) hf
      (fun _ _ => rfl) h
    exact fun x => DFunLike.congr_fun he x
  · right
    have hu : f u=twist u := by
      change f u = u + u.val 4 • z
      simpa only [show u.val 4=(1:ZMod 2) from rfl,one_smul] using h
    have he := equivariant_ext f.toAddMonoidHom twist hf twist_equivariant hu
    exact fun x => DFunLike.congr_fun he x


theorem twist_involutive : Function.Involutive twist := by
  intro x
  have hz : z.val 4 = 0 := rfl
  change (x+x.val 4 • z) + (x+x.val 4 • z).val 4 • z = x
  have he : (x+x.val 4 • z).val 4 = x.val 4 := by
    change x.val 4 + x.val 4 * z.val 4 = x.val 4
    rw [hz,mul_zero,add_zero]
  rw [he,add_assoc,←add_smul,CharTwo.add_self_eq_zero,zero_smul,add_zero]

/-- The transvection is its own inverse. -/
def twistEquiv : Space ≃+ Space where
  toFun := twist
  invFun := twist
  left_inv := twist_involutive
  right_inv := twist_involutive
  map_add' := twist.map_add

/-- The actual affine overlap automorphism, preserving the A₄ coordinate. -/
def borelTwist : MulAut BorelModel :=
  SemidirectProduct.congr (AddEquiv.toMultiplicative twistEquiv) (MulEquiv.refl B) (by
    intro b
    apply MulEquiv.ext
    intro x
    exact twist_equivariant b x.toAdd)

theorem borelTwist_left (x : BorelModel) :
    (borelTwist x).left = Multiplicative.ofAdd (twist x.left.toAdd) := rfl

theorem borelTwist_right (x : BorelModel) : (borelTwist x).right = x.right := rfl

/-- The twist fixes the overlap two-residual pointwise. -/
theorem borelTwist_fixed_residual (x : BorelModel) (hx : x ∈ pResidual 2 BorelModel) :
    borelTwist x=x := by
  rw [residualModel_eq] at hx
  have hh : x.left.toAdd.val 4=0 := hx
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (x.left.toAdd+x.left.toAdd.val 4 • z)=x.left
    rw [hh,zero_smul,add_zero]
    rfl
  · rfl

/-- Its effect on the complementary module direction is multiplication by the root involution. -/
theorem borelTwist_moves_u : borelTwist (SemidirectProduct.inl (Multiplicative.ofAdd u)) =
    SemidirectProduct.inl (Multiplicative.ofAdd (u+z)) := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (u+u.val 4 • z)=Multiplicative.ofAdd (u+z)
    rw [show u.val 4=(1:ZMod 2) from rfl,one_smul]
  · rfl

private theorem conjugate_translation (x : BorelModel) (v : V) :
    x * SemidirectProduct.inl v * x⁻¹ = SemidirectProduct.inl (borelAction x.right v) := by
  ext <;> simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
    mul_comm,mul_left_comm]

/-- After the quotient action has been corrected, the kernel action of an
actual overlap automorphism has exactly the two indicated possibilities. -/
theorem quotient_fixed_module_cases (α : MulAut BorelModel) (f : Space ≃+ Space)
    (hα : ∀ v : Space, α (SemidirectProduct.inl (Multiplicative.ofAdd v)) =
      SemidirectProduct.inl (Multiplicative.ofAdd (f v)))
    (hq : ∀ x : BorelModel, (α x).right=x.right) :
    (∀ x, f x=x) ∨ (∀ x, f x=twist x) := by
  apply centralizer_cases f
  intro b v
  have he := congrArg α (conjugate_translation (SemidirectProduct.inr b)
    (Multiplicative.ofAdd v))
  rw [map_mul,map_mul,map_inv,hα,conjugate_translation,hq] at he
  have hf := hα (rho b.val.val v)
  have he' := he.trans hf
  exact (congrArg (fun x : BorelModel => x.left.toAdd) he').symm

end BinaryPermutation.AlternatingFiveExtension.Overlap
