module
public import Theory.Representation.SLThreeCentralExtension.Normalizer
public import Theory.Representation.SLThreeCentralExtension.Involutions
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.Reduction
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# Sharp offender bounds on the binary-three central cover

The central cover has the same fixed kernel as its invariants. Its full
linear normalizer equals its represented SL₃(2) image, using the rigidity
of the natural quotient and commutator generation. In dimension four every
involution has codimension two, while elementary actors have rank at most
two. Hence neither the cover nor its full normalizer has strong offenders.
The final transport retains the actual operators of any faithful actor.

Source: Aschbacher--Smith, B.4.8(2)--(3), printed p.91, as used by the
omega-center FF argument in 10.2.8, printed p.749.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.OneCohomology.SLThreeCentralExtension
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) BinaryLinearThree.Group V)
  (p : σ.IntertwiningMap W) (hp : IsCover p)

include hp

theorem cover_faithful : Function.Injective σ := by
  intro a b hab
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := hp.1 v
  change W a (p x) = W b (p x)
  rw [←p.isIntertwining, ←p.isIntertwining, hab]

theorem cover_kernel_eq_invariants : p.toLinearMap.ker = σ.invariants := by
  apply le_antisymm hp.2.1
  intro v hv
  have hf : p v ∈ fixed W := by
    intro g
    rw [←p.isIntertwining, hv g]
  have hz : fixed W = ⊥ := SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)
  exact hz.le hf

theorem cover_linearNormalizer_eq : linearNormalizer σ = actionImage σ := by
  apply le_antisymm ?_ (actionImage σ).le_normalizer
  intro u hu
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv u
  have hnormal (g : BinaryLinearThree.Group) : ∃ h, ∀ v, e (σ g v) = σ h (e v) := by
    have hh := (mem_normalizer_iff.mp hu (σ.asGroupHom g)).mp ⟨g,rfl⟩
    obtain ⟨h,hh⟩ := hh
    refine ⟨h,fun v => ?_⟩
    have he := congrArg (fun a : (Module.End (ZMod 2) V)ˣ => a.val (u.val v)) hh
    change σ h (u.val v) = (u.val * σ g * u.inv) (u.val v) at he
    have hi : u.inv (u.val v) = v := by
      have hh := LinearMap.congr_fun u.inv_val v
      exact hh
    change u.val (σ g v) = σ h (u.val v)
    simpa only [Module.End.mul_apply,hi] using he.symm
  have hkernel : ∀ v, p v=0 → p (e v)=0 := by
    intro v hv
    have hf : v ∈ σ.invariants := (cover_kernel_eq_invariants σ p hp).le hv
    have hfix : e v ∈ σ.invariants := by
      intro g
      have hh := (mem_normalizer_iff.mp ((linearNormalizer σ).inv_mem hu)
        (σ.asGroupHom g)).mp ⟨g,rfl⟩
      obtain ⟨h,hh⟩ := hh
      have he := congrArg (fun a : (Module.End (ZMod 2) V)ˣ => a.val v) hh
      change σ h v = (u.inv * σ g * u.val) v at he
      have he' := congrArg u.val he
      have hi (x : V) : u.val (u.inv x)=x := LinearMap.congr_fun u.val_inv x
      change σ g (u.val v) = u.val v
      simpa only [Module.End.mul_apply,hi,hf h] using he'.symm
    exact (cover_kernel_eq_invariants σ p hp).symm.le hfix
  obtain ⟨g,hg⟩ := normalizing_equiv_eq_action p hp e hkernel hnormal
  exact ⟨g,Units.ext (LinearMap.ext (fun v => (hg v).symm))⟩

variable [FiniteDimensional (ZMod 2) V]

theorem cover_not_strong (hdim : Module.finrank (ZMod 2) V=4) :
    ¬ IsStrongFFModule σ := by
  rintro ⟨A,hA⟩
  apply CFSG.Quasithin.ChapterB.NaturalExtensions.FourSpaceOffenders.no_strong
    σ hdim (fun a ha => ?_) A hA
  have hc := NaturalExtension.involution_codim_of_commutator_top σ hdim hp.2.2 a ha
  have hd := fixedCodim_add_finrank σ (zpowers a)
  omega

theorem cover_normalizer_not_strong (hdim : Module.finrank (ZMod 2) V=4) :
    ¬ IsStrongFFModule (normalizerRepresentation σ) := by
  have hi : Function.Injective σ.asGroupHom := fun _ _ h => cover_faithful σ p hp
    (congrArg Units.val h)
  let E : BinaryLinearThree.Group ≃* actionImage σ := MonoidHom.ofInjective hi
  let f : linearNormalizer σ →* BinaryLinearThree.Group := E.symm.toMonoidHom.comp
    (inclusion (cover_linearNormalizer_eq σ p hp).le)
  have hfi : Function.Injective f := E.symm.injective.comp (inclusion_injective _)
  have he (g : linearNormalizer σ) (v : V) : normalizerRepresentation σ g v = σ (f g) v := by
    exact (congrArg (fun x : actionImage σ => x.val.val v)
      (E.apply_symm_apply (inclusion (cover_linearNormalizer_eq σ p hp).le g))).symm
  rintro ⟨A,hA,hlt⟩
  have hoff : IsOffender σ (A.map f) :=
    (show IsOffender (normalizerRepresentation σ) A from ⟨hA,hlt.le⟩).map_equivariant
      _ _ f hfi (LinearEquiv.refl _ _) he
  apply cover_not_strong σ p hp hdim
  refine ⟨A.map f,hoff.1,?_⟩
  rw [←fixedCodim_map_equivariant (normalizerRepresentation σ) σ f
    (LinearEquiv.refl _ _) he,rank_map_injective f hfi]
  exact hlt

/-- Faithful actions whose operators are those of the same central cover inherit
its sharp offender bound. The actor map is constructed from those operators. -/
theorem covered_action_not_strong {H : Type*} [_root_.Group H]
    (τ : Representation (ZMod 2) H V) (hτ : Function.Injective τ)
    (hact : ∀ h, ∃ g, τ h = σ g) (hdim : Module.finrank (ZMod 2) V=4) :
    ¬ IsStrongFFModule τ := by
  have hs := cover_faithful σ p hp
  let f : H →* BinaryLinearThree.Group := {
    toFun := fun h => Classical.choose (hact h)
    map_one' := hs (by rw [←Classical.choose_spec (hact 1),map_one,map_one])
    map_mul' := fun a b => hs (by
      rw [←Classical.choose_spec (hact (a*b)),map_mul,map_mul,
        ←Classical.choose_spec (hact a),←Classical.choose_spec (hact b)]) }
  have he (h : H) : τ h = σ (f h) := Classical.choose_spec (hact h)
  have hf : Function.Injective f := fun a b hab => hτ (by rw [he a,he b,hab])
  rintro ⟨A,hA,hlt⟩
  have hoff : IsOffender σ (A.map f) :=
    (show IsOffender τ A from ⟨hA,hlt.le⟩).map_equivariant
      _ _ f hf (LinearEquiv.refl _ _) (fun h v => LinearMap.congr_fun (he h) v)
  apply cover_not_strong σ p hp hdim
  refine ⟨A.map f,hoff.1,?_⟩
  rw [←fixedCodim_map_equivariant τ σ f (LinearEquiv.refl _ _)
    (fun h v => LinearMap.congr_fun (he h) v),rank_map_injective f hf]
  exact hlt

end Representation.OneCohomology.SLThreeCentralExtension
