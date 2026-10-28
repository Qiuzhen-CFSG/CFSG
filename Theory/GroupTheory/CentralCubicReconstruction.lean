module
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-!
# Reconstructing a central cubic extension from its commutator

Let D have exponent three, let q : D → V have central kernel, and let an
involution fix the kernel and invert V. Every coset has a unique inverted
representative: for a lift x it is x⁻¹ α(x). This gives canonical coordinates
V × ker(q) on the whole group. Their multiplication has correction term the
inverse of the commutator pairing of representatives.

Consequently compatible isomorphisms of V and ker(q), preserving that
pairing, lift to an actual group isomorphism. Automorphisms commuting with
α preserve the section, so equivariance on the two coordinates implies
full equivariance. All maps retain the original quotient and kernel.

This is the elementary exponent-three, class-two central-extension argument
used for the marked cubic cores in Aschbacher–Smith I.4.5, printed p.417.
The proof here is the explicit representative calculation; it assumes no
classification of the group or its actions.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory

/-- A central cubic extension with an involution fixing its kernel and
inverting its quotient. -/
structure CubicInvolutionExtension (D V : Type*) [Group D] [Group V] where
  quotient : D →* V
  surjective : Function.Surjective quotient
  central : quotient.ker ≤ center D
  cube : ∀ x : D, x^3=1
  involution : MulAut D
  involutive : Function.Involutive involution
  fixed : ∀ x∈quotient.ker, involution x=x
  inverted : ∀ x, quotient (involution x)=(quotient x)⁻¹

namespace CubicInvolutionExtension
variable {D V : Type*} [Group D] [Group V] (d : CubicInvolutionExtension D V)

include d in
private theorem inv_mul_inv (x : D) : x⁻¹*x⁻¹=x := by
  have h := d.cube x
  apply (mul_left_cancel (a:=x*x))
  calc
    (x*x)*(x⁻¹*x⁻¹)=1 := by group
    _ = (x*x)*x := by simpa only [pow_succ,pow_zero,one_mul] using h.symm

/-- The explicit inverted representative associated to a lift. -/
def representative (x : D) : D := x⁻¹*d.involution x

theorem representative_inverted (x : D) :
    d.involution (d.representative x)=(d.representative x)⁻¹ := by
  simp only [representative,map_mul,map_inv,mul_inv_rev,inv_inv]
  rw [d.involutive x]

theorem quotient_representative (x : D) :
    d.quotient (d.representative x)=d.quotient x := by
  rw [representative,map_mul,map_inv,d.inverted,←map_inv,←map_mul,d.inv_mul_inv]

theorem representative_eq_of_quotient_eq {x y : D}
    (h : d.quotient x=d.quotient y) : d.representative x=d.representative y := by
  let k := x⁻¹*y
  have hk : k∈d.quotient.ker := by
    change d.quotient (x⁻¹*y)=1
    rw [map_mul,map_inv,h,inv_mul_cancel]
  have hy : y=x*k := by dsimp [k]; group
  rw [hy,representative,representative,map_mul,mul_inv_rev,d.fixed k hk]
  have hz := mem_center_iff.mp (d.central hk) (x⁻¹*d.involution x)
  calc
    x⁻¹*d.involution x = k⁻¹*(x⁻¹*d.involution x)*k := by rw [mul_assoc,hz,inv_mul_cancel_left]
    _ = _ := by group

theorem representative_eq_self {x : D} (h : d.involution x=x⁻¹) :
    d.representative x=x := by rw [representative,h,d.inv_mul_inv]

theorem inverted_lift_unique {x y : D} (hx : d.involution x=x⁻¹)
    (hy : d.involution y=y⁻¹) (h : d.quotient x=d.quotient y) : x=y := by
  rw [←d.representative_eq_self hx,←d.representative_eq_self hy]
  exact d.representative_eq_of_quotient_eq h

/-- The unique inverted lift of a quotient element. -/
noncomputable def invertedSection (v : V) : D :=
  d.representative (d.surjective v).choose

@[simp] theorem quotient_section (v : V) : d.quotient (d.invertedSection v)=v := by
  rw [invertedSection,d.quotient_representative]
  exact (d.surjective v).choose_spec

theorem section_inverted (v : V) : d.involution (d.invertedSection v)=(d.invertedSection v)⁻¹ :=
  d.representative_inverted _

@[simp] theorem section_quotient (x : D) : d.invertedSection (d.quotient x)=d.representative x :=
  d.representative_eq_of_quotient_eq (d.surjective (d.quotient x)).choose_spec

@[simp] theorem section_one : d.invertedSection 1=1 := by
  apply d.inverted_lift_unique (d.section_inverted _) (by simp)
  simp

/-- Central kernel coordinate relative to the canonical inverted lift. -/
noncomputable def centralCoordinate (x : D) : d.quotient.ker :=
  ⟨(d.invertedSection (d.quotient x))⁻¹*x,by
    change d.quotient ((d.invertedSection (d.quotient x))⁻¹*x)=1
    rw [map_mul,map_inv,d.quotient_section,inv_mul_cancel]⟩

theorem reconstruct (x : D) :
    d.invertedSection (d.quotient x)*(d.centralCoordinate x:D)=x := by
  dsimp [centralCoordinate]
  group

/-- Exact coordinates for the whole group, retaining the literal central kernel. -/
noncomputable def coordinates : D ≃ V × d.quotient.ker where
  toFun x := (d.quotient x,d.centralCoordinate x)
  invFun v := d.invertedSection v.1 * v.2
  left_inv := d.reconstruct
  right_inv v := by
    apply Prod.ext
    · change d.quotient (d.invertedSection v.1*(v.2:D))=v.1
      rw [map_mul,d.quotient_section,show d.quotient (v.2:D)=1 from v.2.property,mul_one]
    · apply Subtype.ext
      change (d.invertedSection (d.quotient (d.invertedSection v.1*(v.2:D))))⁻¹*
        (d.invertedSection v.1*(v.2:D))=(v.2:D)
      rw [map_mul,d.quotient_section,show d.quotient (v.2:D)=1 from v.2.property,mul_one]
      group

/-- Every automorphism commuting with the involution preserves the canonical lifts. -/
theorem section_equivariant (a : MulAut D) (b : MulAut V)
    (ha : ∀ x, a (d.involution x)=d.involution (a x))
    (hab : ∀ x, d.quotient (a x)=b (d.quotient x)) (v : V) :
    a (d.invertedSection v)=d.invertedSection (b v) := by
  apply d.inverted_lift_unique
  · rw [←ha,d.section_inverted,map_inv]
  · exact d.section_inverted _
  · rw [hab,d.quotient_section,d.quotient_section]

open scoped IsMulCommutative
variable [IsMulCommutative V]

/-- The central commutator of the canonical lifts, in the literal kernel. -/
noncomputable def commutatorValue (v w : V) : d.quotient.ker :=
  ⟨⁅d.invertedSection v,d.invertedSection w⁆,by
    rw [MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)⟩

/-- The pairing agrees with the commutator of any two lifts. -/
theorem commutatorValue_quotient (x y : D) :
    (d.commutatorValue (d.quotient x) (d.quotient y):D)=⁅x,y⁆ :=
  CentralExtension.commutator_eq_of_image_eq d.quotient d.central
    (d.quotient_section _) (d.quotient_section _)

/-- The section multiplication is fixed by its commutator; there is no
additional choice of central cocycle. -/
theorem section_mul (v w : V) :
    d.invertedSection (v*w)=d.invertedSection v*d.invertedSection w*
      (d.commutatorValue v w:D) := by
  let x := d.invertedSection v
  let y := d.invertedSection w
  let k := d.commutatorValue v w
  have hx : d.involution x=x⁻¹ := d.section_inverted v
  have hy : d.involution y=y⁻¹ := d.section_inverted w
  have hk : (k:D)=⁅x⁻¹,y⁻¹⁆ := by
    calc
      (k:D) = d.involution k := (d.fixed _ k.property).symm
      _ = ⁅d.involution x,d.involution y⁆ := map_commutatorElement _ x y
      _ = ⁅x⁻¹,y⁻¹⁆ := by rw [hx,hy]
  have he : x⁻¹*y⁻¹=(k:D)*(x*y)⁻¹ := by rw [hk,commutatorElement_def]; group
  have hz := mem_center_iff.mp (d.central k.property) ((x*y)⁻¹)
  calc
    d.invertedSection (v*w) = d.representative (x*y) := by
      rw [←d.section_quotient,map_mul,d.quotient_section,d.quotient_section]
    _ = (x*y)⁻¹*((k:D)*(x*y)⁻¹) := by rw [representative,map_mul,hx,hy,he]
    _ = (k:D)*((x*y)⁻¹*(x*y)⁻¹) := by rw [←mul_assoc,hz,mul_assoc]
    _ = (k:D)*(x*y) := by rw [d.inv_mul_inv]
    _ = x*y*(k:D) := (mem_center_iff.mp (d.central k.property) (x*y)).symm

/-- Multiplication in the full group in quotient/central coordinates. -/
theorem coordinate_product (v w : V) (a b : d.quotient.ker) :
    (d.invertedSection v*(a:D))*(d.invertedSection w*(b:D))=
      d.invertedSection (v*w)*((a*b*(d.commutatorValue v w)⁻¹:d.quotient.ker):D) := by
  rw [d.section_mul]
  change _=(d.invertedSection v*d.invertedSection w*(d.commutatorValue v w:D))*
    ((a:D)*(b:D)*(d.commutatorValue v w:D)⁻¹)
  have ha := mem_center_iff.mp (d.central a.property) (d.invertedSection w)
  have hk := mem_center_iff.mp (d.central (d.commutatorValue v w).property) ((a:D)*(b:D))
  calc
    _ = d.invertedSection v*d.invertedSection w*((a:D)*(b:D)) := by
      rw [mul_assoc,←mul_assoc (a:D),←ha]; simp only [mul_assoc]
    _ = _ := by rw [mul_assoc (d.invertedSection v*d.invertedSection w),
      ←mul_assoc (d.commutatorValue v w:D),←hk,mul_inv_cancel_right]

variable {D₂ V₂ : Type*} [Group D₂] [Group V₂] [IsMulCommutative V₂]
    (r : CubicInvolutionExtension D₂ V₂)

/-- A commutator-preserving isomorphism of quotient and kernel reconstructs
an actual isomorphism of the full cubic groups. -/
noncomputable def liftEquiv (e : V ≃* V₂) (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w)) : D ≃* D₂ := by
  let E : D ≃ D₂ := d.coordinates.trans
    ((e.toEquiv.prodCongr f.toEquiv).trans r.coordinates.symm)
  have HE (v : V) (a : d.quotient.ker) :
      E (d.invertedSection v*(a:D))=r.invertedSection (e v)*(f a:D₂) := by
    change r.coordinates.symm ((e.toEquiv.prodCongr f.toEquiv)
      (d.coordinates (d.coordinates.symm (v,a))))=_
    rw [Equiv.apply_symm_apply]
    rfl
  refine { toEquiv := E, map_mul' := ?_ }
  intro x y
  obtain ⟨⟨v,a⟩,rfl⟩ := d.coordinates.symm.surjective x
  obtain ⟨⟨w,b⟩,rfl⟩ := d.coordinates.symm.surjective y
  change E ((d.invertedSection v*(a:D))*(d.invertedSection w*(b:D)))=
    E (d.invertedSection v*(a:D))*E (d.invertedSection w*(b:D))
  rw [d.coordinate_product,HE,HE,HE,map_mul,r.coordinate_product]
  congr 1
  exact congrArg Subtype.val (by rw [map_mul,map_mul,map_inv,hform])

theorem liftEquiv_apply (e : V ≃* V₂) (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w)) (x : D) :
    d.liftEquiv r e f hform x=
      r.invertedSection (e (d.quotient x))*(f (d.centralCoordinate x):D₂) := rfl

@[simp] theorem liftEquiv_quotient (e : V ≃* V₂) (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w)) (x : D) :
    r.quotient (d.liftEquiv r e f hform x)=e (d.quotient x) := by
  rw [liftEquiv_apply,map_mul,r.quotient_section,
    show r.quotient (f (d.centralCoordinate x):D₂)=1 from (f _).property,mul_one]

@[simp] theorem liftEquiv_section (e : V ≃* V₂) (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w)) (v : V) :
    d.liftEquiv r e f hform (d.invertedSection v)=r.invertedSection (e v) := by
  rw [liftEquiv_apply,d.quotient_section]
  have hc : d.centralCoordinate (d.invertedSection v)=1 := by
    apply Subtype.ext
    change (d.invertedSection (d.quotient (d.invertedSection v)))⁻¹*d.invertedSection v=1
    rw [d.quotient_section,inv_mul_cancel]
  rw [hc,map_one,OneMemClass.coe_one,mul_one]

@[simp] theorem liftEquiv_kernel (e : V ≃* V₂) (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w))
    (a : d.quotient.ker) : d.liftEquiv r e f hform (a:D)=(f a:D₂) := by
  rw [liftEquiv_apply,show d.quotient (a:D)=1 from a.property,map_one,r.section_one,one_mul]
  congr 2
  apply Subtype.ext
  change (d.invertedSection (d.quotient (a:D)))⁻¹*(a:D)=(a:D)
  rw [show d.quotient (a:D)=1 from a.property,d.section_one,inv_one,one_mul]

/-- Compatibility on quotient and kernel gives compatibility on the whole
nonabelian group, with the actual automorphisms on each side. -/
theorem liftEquiv_equivariant (e : V ≃* V₂)
    (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w))
    (a : MulAut D) (a₂ : MulAut D₂) (b : MulAut V) (b₂ : MulAut V₂)
    (ha : ∀ x,a (d.involution x)=d.involution (a x))
    (ha₂ : ∀ x,a₂ (r.involution x)=r.involution (a₂ x))
    (hab : ∀ x,d.quotient (a x)=b (d.quotient x))
    (hab₂ : ∀ x,r.quotient (a₂ x)=b₂ (r.quotient x))
    (he : ∀ v,e (b v)=b₂ (e v))
    (hf : ∀ k : d.quotient.ker,
      (f ⟨a k,by rw [MonoidHom.mem_ker,hab,k.property,map_one]⟩:D₂)=a₂ (f k))
    (x : D) :
    d.liftEquiv r e f hform (a x)=a₂ (d.liftEquiv r e f hform x) := by
  obtain ⟨⟨v,k⟩,rfl⟩ := d.coordinates.symm.surjective x
  change d.liftEquiv r e f hform (a (d.invertedSection v*(k:D)))=
    a₂ (d.liftEquiv r e f hform (d.invertedSection v*(k:D)))
  rw [map_mul,d.section_equivariant a b ha hab,map_mul,map_mul,
    d.liftEquiv_section,d.liftEquiv_section,d.liftEquiv_kernel,map_mul,
    r.section_equivariant a₂ b₂ ha₂ hab₂,he]
  congr 1
  exact (d.liftEquiv_kernel r e f hform
    ⟨a k,by rw [MonoidHom.mem_ker,hab,k.property,map_one]⟩).trans (hf k)

omit [IsMulCommutative V] [IsMulCommutative V₂] in
/-- If the kernel is generated by commutators, an involution-compatible
homomorphism is determined by its induced quotient map. -/
theorem hom_ext (hderived : d.quotient.ker ≤ _root_.commutator D)
    (f g : D →* D₂)
    (hf : ∀ x,f (d.involution x)=r.involution (f x))
    (hg : ∀ x,g (d.involution x)=r.involution (g x))
    (hq : ∀ x,r.quotient (f x)=r.quotient (g x)) : f=g := by
  have hk : _root_.commutator D ≤ f.eqLocus g := by
    rw [_root_.commutator_def]
    apply commutator_le.mpr
    intro x _ y _
    change f ⁅x,y⁆=g ⁅x,y⁆
    rw [map_commutatorElement,map_commutatorElement]
    exact CentralExtension.commutator_eq_of_image_eq r.quotient r.central (hq x) (hq y)
  apply MonoidHom.ext
  intro x
  obtain ⟨⟨v,k⟩,rfl⟩ := d.coordinates.symm.surjective x
  change f (d.invertedSection v*(k:D))=g (d.invertedSection v*(k:D))
  rw [map_mul,map_mul]
  congr 1
  · apply r.inverted_lift_unique
    · rw [←hf,d.section_inverted,map_inv]
    · rw [←hg,d.section_inverted,map_inv]
    · exact hq _
  · exact hk (hderived k.property)

/-- The reconstructed equivalence preserves the actual involution. -/
theorem liftEquiv_involution (e : V ≃* V₂) (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w)) (x : D) :
    d.liftEquiv r e f hform (d.involution x)=r.involution (d.liftEquiv r e f hform x) := by
  obtain ⟨⟨v,k⟩,rfl⟩ := d.coordinates.symm.surjective x
  change d.liftEquiv r e f hform (d.involution (d.invertedSection v*(k:D)))=
    r.involution (d.liftEquiv r e f hform (d.invertedSection v*(k:D)))
  rw [map_mul,d.section_inverted,d.fixed _ k.property,map_mul,map_mul,map_inv,
    d.liftEquiv_section,d.liftEquiv_kernel,map_mul,
    r.section_inverted,r.fixed _ (f k).property]

/-- For a derived kernel, equivariance on the quotient alone determines
equivariance of the reconstructed whole-group isomorphism. -/
theorem liftEquiv_equivariant_of_derived
    (hderived : d.quotient.ker ≤ _root_.commutator D)
    (e : V ≃* V₂) (f : d.quotient.ker ≃* r.quotient.ker)
    (hform : ∀ v w, f (d.commutatorValue v w)=r.commutatorValue (e v) (e w))
    (a : MulAut D) (a₂ : MulAut D₂) (b : MulAut V) (b₂ : MulAut V₂)
    (ha : ∀ x,a (d.involution x)=d.involution (a x))
    (ha₂ : ∀ x,a₂ (r.involution x)=r.involution (a₂ x))
    (hab : ∀ x,d.quotient (a x)=b (d.quotient x))
    (hab₂ : ∀ x,r.quotient (a₂ x)=b₂ (r.quotient x))
    (he : ∀ v,e (b v)=b₂ (e v)) (x : D) :
    d.liftEquiv r e f hform (a x)=a₂ (d.liftEquiv r e f hform x) := by
  have hh := d.hom_ext r hderived
    ((d.liftEquiv r e f hform).toMonoidHom.comp a.toMonoidHom)
    (a₂.toMonoidHom.comp (d.liftEquiv r e f hform).toMonoidHom)
    (by
      intro v
      change d.liftEquiv r e f hform (a (d.involution v))=
        r.involution (d.liftEquiv r e f hform (a v))
      rw [ha,d.liftEquiv_involution])
    (by
      intro v
      change a₂ (d.liftEquiv r e f hform (d.involution v))=
        r.involution (a₂ (d.liftEquiv r e f hform v))
      rw [d.liftEquiv_involution,ha₂])
    (by
      intro v
      change r.quotient (d.liftEquiv r e f hform (a v))=
        r.quotient (a₂ (d.liftEquiv r e f hform v))
      rw [d.liftEquiv_quotient,hab,hab₂,d.liftEquiv_quotient,he])
  exact DFunLike.congr_fun hh x

end CubicInvolutionExtension
end Theory.GroupTheory
