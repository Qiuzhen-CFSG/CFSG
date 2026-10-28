module
public import Theory.Representation.ThreeWeightSquare.CentralPreimage
public import Theory.Representation.ThreeWeightSquare.Matrices
/-!
# Three-weight square actions through the actual central quotient

The full preimage of a nondefining p-subgroup is abelian and has invertible
order in the natural field. Restrict a compatible cover automorphism to
that preimage, apply the literal three-weight matrix theorem, and descend
its square-one conclusion through the original quotient map.
Source: the odd degree-three cases of Aschbacher–Smith A.3.15 and 1.3.4.
-/
public section
noncomputable section
namespace Representation.ThreeWeightSquare
open Subgroup
variable {F G H : Type*} [Field F] [Finite F] [Group G] [Finite G] [Group H]
variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [CharP F q]

/-- Restrict an automorphism to an invariant subgroup. -/
def invariantAut (α : MulAut G) (C : Subgroup G)
    (hC : ∀ x, α x ∈ C ↔ x ∈ C) : MulAut C where
  toFun x := ⟨α x,hC _ |>.mpr x.property⟩
  invFun x := ⟨α.symm x,by
    apply (hC (α.symm x)).mp
    simpa only [α.apply_symm_apply] using x.property⟩
  left_inv x := Subtype.ext (α.symm_apply_apply x)
  right_inv x := Subtype.ext (α.apply_symm_apply x)
  map_mul' x y := Subtype.ext (α.map_mul x y)

omit [Finite G] in
private theorem invariantAut_pow (α : MulAut G) (C : Subgroup G)
    (hC : ∀ x, α x ∈ C ↔ x ∈ C) (n : ℕ) (x : C) :
    (((invariantAut α C hC)^n) x : G) = (α^n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ',MulAut.mul_apply]
    change α (((invariantAut α C hC)^n) x : G)=_
    rw [ih]

/-- The quotient action has square one on a nondefining p-subgroup. -/
theorem central_quotient_square (hp : 3<p) (hpq : p≠q)
    (j : G→*GL (Fin 3) F) (hj : Function.Injective j)
    (f : G→*H) (hf : Function.Surjective f) (hk : f.ker≤center G)
    (hkq : (Nat.card f.ker:F)≠0)
    (P : Subgroup H) (hP : IsPGroup p P)
    (α : MulAut G) (β : MulAut H)
    (hcompat : ∀x,f (α x)=β (f x))
    (ha : ∃n:ℕ,α^(2^n)=1)
    (hPβ : ∀x,β x∈P↔x∈P)
    (hform : ∃g:GL (Fin 3) F,
      (∀x,j (α x)=g*j x*g⁻¹) ∨
      (∀x,(j (α x)).val=g.val*(j x).inv.transpose*g.inv)) :
    ∀b∈P,β (β b)=b := by
  let C := P.comap f
  let fC := f.subgroupComap P
  have hfC : Function.Surjective fC := f.subgroupComap_surjective_of_surjective P hf
  have hkC : fC.ker≤center C := by
    intro a ha
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact mem_center_iff.mp (hk (congrArg Subtype.val ha)) b
  let e : fC.ker ≃* f.ker :=
    { toFun := fun x=>⟨x.val.val,congrArg Subtype.val x.property⟩
      invFun := fun x=>⟨⟨x.val,by change f x.val∈P; rw [x.property];exact one_mem _⟩,
        Subtype.ext x.property⟩
      left_inv := fun x=>rfl
      right_inv := fun x=>rfl
      map_mul' := fun x y=>rfl }
  have hkCq : (Nat.card fC.ker:F)≠0 := by
    rwa [Nat.card_congr e.toEquiv]
  let jC := j.comp C.subtype
  have hjC : Function.Injective jC := hj.comp Subtype.val_injective
  let _ := central_preimage_abelian hp hpq jC hjC fC hfC hkC hP
  have horder : (Nat.card C:F)≠0 := central_preimage_order hpq fC hfC hkCq hP
  have hC : ∀x,α x∈C↔x∈C := by
    intro x
    change f (α x)∈P↔f x∈P
    rw [hcompat,hPβ]
  let αC := invariantAut α C hC
  have hαC : ∃n:ℕ,αC^(2^n)=1 := by
    obtain ⟨n,hn⟩ := ha
    refine ⟨n,?_⟩
    ext x
    rw [invariantAut_pow,hn]
    rfl
  have hformC : ∃g:GL (Fin 3) F,
      (∀x,jC (αC x)=g*jC x*g⁻¹) ∨
      (∀x,(jC (αC x)).val=g.val*(jC x).inv.transpose*g.inv) := by
    obtain ⟨g,h|h⟩ := hform
    · exact ⟨g,Or.inl (fun x=>h x)⟩
    · exact ⟨g,Or.inr (fun x=>h x)⟩
  have hs := matrix_square_eq_one_of_field jC hjC horder αC hαC hformC
  intro b hb
  obtain ⟨a,ha⟩ := hfC ⟨b,hb⟩
  have hs' := congrArg (fun z : MulAut C => (z a : G)) hs
  change α (α a.val)=a.val at hs'
  have hh := congrArg f hs'
  rw [hcompat,hcompat] at hh
  have hab : f a.val=b := congrArg Subtype.val ha
  rwa [hab] at hh
end Representation.ThreeWeightSquare
