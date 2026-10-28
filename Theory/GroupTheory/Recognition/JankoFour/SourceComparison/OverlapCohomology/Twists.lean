module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology.Native

/-!
# The quadratic correction on the actual hexad extension

The full symplectic cocycle defines a shear of the native hexad group by
its intrinsic elementary radical. The cocycle law proves multiplicativity
without a chosen complement. Every such shear is involutory in
characteristic two. Principal cocycles give inner automorphisms through
the radical, whereas the quadratic cocycle is outer: any inner conjugator
fixing the radical would itself lie there by faithfulness of the action.

The computed normal form therefore factors every pointwise radical fixer
as one inner automorphism, optionally followed by this constructed twist.
Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
This concerns the hexad quotient used by the overlap calculation, not yet
all automorphisms of I or its lifting back across Q A.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
open Subgroup Representation Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour
open Sporadic.Mathieu.M22ChapterH.Hexad.Action

private noncomputable def vector (v : V) : Outer :=
  (nativeCoordinates.symm (Multiplicative.ofAdd v)).val

private theorem vector_add (v w : V) : vector (v+w) = vector v * vector w :=
  congrArg Subtype.val (nativeCoordinates.symm.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w))

private theorem vector_zero : vector 0 = 1 :=
  congrArg Subtype.val (nativeCoordinates.symm.map_one)

private theorem vector_neg (v : V) : vector (-v) = (vector v)⁻¹ :=
  congrArg Subtype.val (nativeCoordinates.symm.map_inv (Multiplicative.ofAdd v))

private theorem vector_commute (v w : V) : Commute (vector v) (vector w) := by
  change vector v * vector w = vector w * vector v
  rw [←vector_add,←vector_add,add_comm]

private theorem vector_actor (v : V) : nativeActor (vector v) = 1 := by
  apply (show nativeActor.ker = pCore 2 Outer from nativeActor_ker).ge
  exact (nativeCoordinates.symm (Multiplicative.ofAdd v)).property

private theorem vector_action (g : Outer) (v : V) :
    vector (natural (nativeActor g) v) = g * vector v * g⁻¹ :=
  nativeCoordinates_conjugation_symm g v

private theorem cocycle_one (f : cocycles natural) : f.val 1 = 0 := by
  have he := f.property 1 1
  simpa using he.symm

private noncomputable def shear (f : cocycles natural) : Outer →* Outer where
  toFun g := vector (f.val (nativeActor g)) * g
  map_one' := by rw [map_one,cocycle_one,vector_zero,one_mul]
  map_mul' g k := by
    change vector (f.val (nativeActor (g*k))) * (g*k) =
      (vector (f.val (nativeActor g)) * g) * (vector (f.val (nativeActor k)) * k)
    rw [map_mul,f.property,add_comm,vector_add,vector_action]
    group

private theorem shear_actor (f : cocycles natural) (g : Outer) :
    nativeActor (shear f g) = nativeActor g := by
  change nativeActor (vector _ * g) = _
  rw [map_mul,vector_actor,one_mul]

private theorem shear_involutive (f : cocycles natural) : Function.Involutive (shear f) := by
  intro g
  change vector (f.val (nativeActor (shear f g))) * (vector (f.val (nativeActor g)) * g) = g
  have hv (v : V) : v+v=0 := by
    ext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [shear_actor,←mul_assoc,←vector_add,hv,vector_zero,one_mul]

/-- Every full symplectic cocycle gives a genuine automorphism of the native
hexad extension; no complement or splitting is assumed. -/
noncomputable def nativeCocycleAut (f : cocycles natural) : MulAut Outer :=
  { shear f with
    invFun := shear f
    left_inv := shear_involutive f
    right_inv := shear_involutive f }

theorem nativeCocycleAut_apply (f : cocycles natural) (g : Outer) :
    nativeCocycleAut f g = (nativeCoordinates.symm
      (Multiplicative.ofAdd (f.val (nativeActor g))) : Outer) * g := by rfl

theorem nativeCocycleAut_actor (f : cocycles natural) (g : Outer) :
    nativeActor (nativeCocycleAut f g) = nativeActor g := by exact shear_actor f g

theorem nativeCocycleAut_fixes_radical (f : cocycles natural) (n : pCore 2 Outer) :
    nativeCocycleAut f n.val = n.val := by
  have hn : nativeActor n.val = 1 := nativeActor_ker.ge n.property
  change vector (f.val (nativeActor n.val)) * n.val = n.val
  rw [hn,cocycle_one,vector_zero,one_mul]

theorem nativeCocycleAut_add (f c : cocycles natural) :
    nativeCocycleAut (f+c) = nativeCocycleAut f * nativeCocycleAut c := by
  apply MulEquiv.ext
  intro g
  rw [MulAut.mul_apply,nativeCocycleAut_apply (f+c),nativeCocycleAut_apply f,
    nativeCocycleAut_actor,nativeCocycleAut_apply c]
  change vector (f.val (nativeActor g)+c.val (nativeActor g))*g = _
  rw [vector_add,mul_assoc]
  rfl

theorem nativeCocycleAut_principal (v : V) :
    nativeCocycleAut (principal natural v) =
      MulAut.conj ((nativeCoordinates.symm (Multiplicative.ofAdd v) : Outer)⁻¹) := by
  apply MulEquiv.ext
  intro g
  rw [nativeCocycleAut_apply,MulAut.conj_apply]
  change vector (natural (nativeActor g) v-v)*g = (vector v)⁻¹*g*((vector v)⁻¹)⁻¹
  rw [sub_eq_add_neg,vector_add,(vector_commute _ _).eq,vector_neg,vector_action]
  group

/-- Distinct full-group cocycles give distinct automorphisms of the actual extension. -/
theorem nativeCocycleAut_injective : Function.Injective nativeCocycleAut := by
  intro f c he
  apply Subtype.ext
  funext s
  obtain ⟨g,rfl⟩ := nativeActor_surjective s
  apply Multiplicative.ofAdd.injective
  apply nativeCoordinates.symm.injective
  apply Subtype.ext
  have hh := MulEquiv.congr_fun he g
  rw [nativeCocycleAut_apply,nativeCocycleAut_apply] at hh
  exact mul_right_cancel hh

private theorem native_conjugator_mem_radical (x : Outer)
    (hx : ∀ n : pCore 2 Outer, x*n.val*x⁻¹=n.val) : x ∈ pCore 2 Outer := by
  rw [←nativeActor_ker,MonoidHom.mem_ker]
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [show (1 : Sp).val = 1 from rfl,Matrix.one_mulVec]
  change natural (nativeActor x) v = v
  apply Multiplicative.ofAdd.injective
  apply nativeCoordinates.symm.injective
  apply Subtype.ext
  rw [nativeCoordinates_conjugation_symm]
  exact hx _

/-- The one nonprincipal correction on the actual native hexad extension. -/
noncomputable def nativeQuadraticTwist : MulAut Outer := nativeCocycleAut quadraticCocycle

theorem nativeQuadraticTwist_apply (g : Outer) :
    nativeQuadraticTwist g = (nativeCoordinates.symm
      (Multiplicative.ofAdd (quadraticCocycle.val (nativeActor g))) : Outer) * g := by
  exact nativeCocycleAut_apply quadraticCocycle g

theorem nativeQuadraticTwist_fixes_radical (n : pCore 2 Outer) :
    nativeQuadraticTwist n.val = n.val := by
  exact nativeCocycleAut_fixes_radical quadraticCocycle n

theorem nativeQuadraticTwist_sq : nativeQuadraticTwist ^ 2 = 1 := by
  rw [pow_two]
  apply MulEquiv.ext
  intro g
  rw [MulAut.mul_apply]
  change shear quadraticCocycle (shear quadraticCocycle g) = g
  exact shear_involutive quadraticCocycle g

/-- The quadratic correction is genuinely outer on the native hexad group. -/
theorem nativeQuadraticTwist_not_inner :
    ¬ ∃ x : Outer, nativeQuadraticTwist = MulAut.conj x := by
  rintro ⟨x,hx⟩
  have hn : x ∈ pCore 2 Outer := native_conjugator_mem_radical x (by
    intro n
    change MulAut.conj x n.val = n.val
    rw [←hx]
    exact nativeCocycleAut_fixes_radical quadraticCocycle n)
  let v : V := (nativeCoordinates ⟨x,hn⟩).toAdd
  have hv : vector v = x := by
    change ((nativeCoordinates.symm
      (Multiplicative.ofAdd (nativeCoordinates ⟨x,hn⟩).toAdd)) : Outer) = x
    rw [ofAdd_toAdd,nativeCoordinates.symm_apply_apply]
  have hp : nativeCocycleAut (principal natural (-v)) = MulAut.conj x := by
    rw [nativeCocycleAut_principal]
    change MulAut.conj (vector (-v))⁻¹ = MulAut.conj x
    rw [vector_neg,inv_inv,hv]
  apply full_quadratic_not_principal
  exact ⟨-v,nativeCocycleAut_injective (hp.trans hx.symm)⟩

/-- The native radical fixers are inner through that radical, with at most
one additional quadratic twist. The correcting maps are constructed here. -/
theorem native_automorphism_factorization (α : MulAut Outer)
    (hfix : ∀ n ∈ pCore 2 Outer, α n = n) :
    ∃ n : pCore 2 Outer,
      α = MulAut.conj n.val ∨ α = MulAut.conj n.val * nativeQuadraticTwist := by
  obtain ⟨t,v,hv⟩ := native_automorphism_normal_form α hfix
  have he : α = nativeCocycleAut (t • quadraticCocycle + principal natural v) := by
    apply MulEquiv.ext
    intro g
    rw [nativeCocycleAut_apply]
    exact hv g
  refine ⟨(nativeCoordinates.symm (Multiplicative.ofAdd v))⁻¹,?_⟩
  have ht : t=0 ∨ t=1 := by
    have ht : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact ht t
  rcases ht with rfl | rfl
  · left
    rw [he,zero_smul,zero_add,nativeCocycleAut_principal]
    rfl
  · right
    rw [he,one_smul,add_comm,nativeCocycleAut_add,nativeCocycleAut_principal]
    rfl

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
