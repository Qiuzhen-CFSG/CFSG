module
public import Theory.Representation.SL3.NaturalAbelianTorus
public import Theory.Representation.SL3.DualInvariantLines
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Doubled natural involution layers have no exponent-four lift

An abelian exponent-four group has an exact square map with its involution
subgroup as kernel. Suppose that subgroup is two copies of the natural
SL₃ module and the original covering kernel acts centrally. If the square
image is nonzero, the additive invariant-subgroup classification supplies
a natural graph in that image. Pull back that graph and quotient by its
complementary involution summand. The resulting exact natural self-extension
has doubling as its layer identification, contradicting the nonbinary torus
obstruction. The original quotient marking and covering kernel are retained.

The intrinsic application is the whole-center reconstruction in
Aschbacher–Smith C.1.34, printed pp.136–137. This calculation is independent
of MS-pair hypotheses and does not assume that the square image is the
entire involution layer or that the abelian group is homocyclic.
-/

public noncomputable section
open Representation
open scoped MatrixGroups
namespace Representation.DoubledAbelianTorus
variable {X A F : Type*} [Group X] [AddCommGroup A] [Field F] [CharP F 2]
local notation "W" => (Fin 3 → F)
local notation "V" => (W × W)
variable (π : X →* SL(3,F)) (ρ : Representation ℤ X A)

/-- Exact coordinates for an exponent-four abelian group whose involution
layer is doubled natural. The square image may be any invariant subgroup. -/
structure Data where
  incl : V →+ A
  sq : A →+ V
  incl_injective : Function.Injective incl
  exact : ∀ x, sq x=0 ↔ ∃ v, incl v=x
  double : ∀ x, x+x=incl (sq x)
  incl_equivariant : ∀ g v, ρ g (incl v)=incl
    (specialLinearNatural 3 (π g) v.1,specialLinearNatural 3 (π g) v.2)
  sq_equivariant : ∀ g x, sq (ρ g x)=
    (specialLinearNatural 3 (π g) (sq x).1,specialLinearNatural 3 (π g) (sq x).2)

variable {π ρ} (d : Data π ρ)
omit [CharP F 2] in
private theorem sq_incl (v : V) : d.sq (d.incl v)=0 := (d.exact _).mpr ⟨v,rfl⟩

variable [Finite X] [Finite F]
private theorem no_retract_lift (hπ : Function.Surjective π)
    (hc : ∀ z, π z=1 → ∀ g, Commute (ρ z) (ρ g)) (hF : 2 < Nat.card F)
    (j : W →+ V) (r : V →+ W) (hrj : ∀ v, r (j v)=v)
    (hj : ∀ g v, j (specialLinearNatural 3 (π g) v)=
      (specialLinearNatural 3 (π g) (j v).1,specialLinearNatural 3 (π g) (j v).2))
    (hr : ∀ g v, r (specialLinearNatural 3 (π g) v.1,
      specialLinearNatural 3 (π g) v.2)=specialLinearNatural 3 (π g) (r v))
    (hs : ∀ v, ∃ x, d.sq x=j v) : False := by
  let E : Subrepresentation ρ := {
    toSubmodule := LinearMap.ker ((d.sq.toIntLinearMap) -
      j.toIntLinearMap.comp (r.toIntLinearMap.comp d.sq.toIntLinearMap))
    apply_mem_toSubmodule g x hx := by
      change d.sq (ρ g x)-j (r (d.sq (ρ g x)))=0
      have hx : d.sq x=j (r (d.sq x)) := sub_eq_zero.mp hx
      rw [d.sq_equivariant,hr,hj,←hx,sub_self] }
  have hE (x : A) : x ∈ E.toSubmodule ↔ d.sq x=j (r (d.sq x)) := sub_eq_zero
  let i : V →ₗ[ℤ] E.toSubmodule := d.incl.toIntLinearMap.codRestrict E.toSubmodule
    (fun v => (hE _).mpr (by
      change d.sq (d.incl v)=j (r (d.sq (d.incl v)))
      rw [sq_incl,map_zero,map_zero]))
  let N : Submodule ℤ E.toSubmodule := (LinearMap.ker r.toIntLinearMap).map i
  have hN (g : X) : N ≤ N.comap (E.toRepresentation g) := by
    rintro x ⟨v,hv,rfl⟩
    let w : V := (specialLinearNatural 3 (π g) v.1,specialLinearNatural 3 (π g) v.2)
    refine ⟨w,?_,?_⟩
    · change r w=0
      dsimp [w]
      rw [hr,show r v=0 from hv,map_zero]
    · apply Subtype.ext
      exact (d.incl_equivariant g v).symm
  let σ := E.toRepresentation.quotient N hN
  let q := N.mkQ
  have hq (g : X) (x : E.toSubmodule) : σ g (q x)=q (E.toRepresentation g x) := rfl
  let p : E.toSubmodule →ₗ[ℤ] W := r.toIntLinearMap.comp
    (d.sq.toIntLinearMap.comp E.toSubmodule.subtype)
  have hNp : N ≤ LinearMap.ker p := by
    rintro x ⟨v,_,rfl⟩
    change r (d.sq (d.incl v))=0
    rw [sq_incl,map_zero]
  let proj : (E.toSubmodule ⧸ N) →ₗ[ℤ] W := N.liftQ p hNp
  let incl : W →ₗ[ℤ] (E.toSubmodule ⧸ N) := q.comp (i.comp j.toIntLinearMap)
  have hp (x : E.toSubmodule) : proj (q x)=r (d.sq x.val) := rfl
  have hi (v : W) : incl v=q (i (j v)) := rfl
  have hqzero (x : E.toSubmodule) : q x=0 ↔ x ∈ N := Submodule.Quotient.mk_eq_zero N
  have hinj : Function.Injective incl := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro v hv
    obtain ⟨w,hw,he⟩ := (hqzero _).mp hv
    have he' : w=j v := d.incl_injective (congrArg Subtype.val he)
    have hz : r w=0 := hw
    rw [he',hrj] at hz
    exact hz
  have hsurj : Function.Surjective proj := by
    intro v
    obtain ⟨x,hx⟩ := hs v
    let xx : E.toSubmodule := ⟨x,(hE x).mpr (by rw [hx,hrj])⟩
    exact ⟨q xx,by rw [hp]; change r (d.sq x)=v; rw [hx,hrj]⟩
  have hex (x : E.toSubmodule ⧸ N) : proj x=0 ↔ ∃ v, incl v=x := by
    obtain ⟨x,rfl⟩ := N.mkQ_surjective x
    constructor
    · intro hx
      have hsx : d.sq x.val=0 := by
        rw [(hE _).mp x.property,←hp,hx,map_zero]
      obtain ⟨v,hv⟩ := (d.exact _).mp hsx
      refine ⟨r v,?_⟩
      apply sub_eq_zero.mp
      rw [hi,←map_sub]
      apply (hqzero _).mpr
      refine ⟨j (r v)-v,?_,?_⟩
      · change r (j (r v)-v)=0
        rw [map_sub,hrj,sub_self]
      · apply Subtype.ext
        change d.incl (j (r v)-v)=d.incl (j (r v))-x.val
        rw [map_sub,hv]
    · rintro ⟨v,hv⟩
      rw [←hv,hi,hp]
      change r (d.sq (d.incl (j v)))=0
      rw [sq_incl,map_zero]
  have hinceq (g : X) (v : W) : σ g (incl v)=incl (specialLinearNatural 3 (π g) v) := by
    rw [hi,hq,hi]
    congr 1
    apply Subtype.ext
    change ρ g (d.incl (j v))=d.incl (j (specialLinearNatural 3 (π g) v))
    rw [d.incl_equivariant,hj]
  have hprojeq (g : X) (x : E.toSubmodule ⧸ N) :
      proj (σ g x)=specialLinearNatural 3 (π g) (proj x) := by
    obtain ⟨x,rfl⟩ := N.mkQ_surjective x
    rw [hq,hp,hp]
    change r (d.sq (ρ g x.val))=_
    rw [d.sq_equivariant,hr]
  let dd : NaturalAbelianExtension.Data π σ :=
    ⟨incl.toAddMonoidHom,proj.toAddMonoidHom,hinj,hsurj,hex,hinceq,hprojeq⟩
  apply NaturalAbelianTorus.no_square_extension dd hπ ?_ ?_ hF
  · intro z hz g
    apply LinearMap.ext
    intro x
    obtain ⟨x,rfl⟩ := N.mkQ_surjective x
    change σ z (σ g (q x))=σ g (σ z (q x))
    rw [hq,hq,hq,hq]
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (hc z hz g).eq x.val
  · intro x
    obtain ⟨x,rfl⟩ := N.mkQ_surjective x
    change q x+q x=incl (proj (q x))
    rw [←map_add,hp,hi]
    congr 1
    apply Subtype.ext
    change x.val+x.val=d.incl (j (r (d.sq x.val)))
    rw [d.double,←(hE _).mp x.property]

/-- A central cover of nonbinary SL₃ cannot lift a doubled natural involution
layer to higher exponent. Every element in these square coordinates has square zero. -/
theorem square_eq_zero (hπ : Function.Surjective π)
    (hc : ∀ z, π z=1 → ∀ g, Commute (ρ z) (ρ g)) (hF : 2 < Nat.card F) :
    ∀ x, d.sq x=0 := by
  by_contra hnot
  have hne : d.sq.range ≠ ⊥ := by
    intro he
    apply hnot
    intro x
    exact he.le ⟨x,rfl⟩
  have hinv (g : SL(3,F)) (v : V) (hv : v ∈ d.sq.range) :
      (specialLinearNatural 3 g v.1,specialLinearNatural 3 g v.2) ∈ d.sq.range := by
    obtain ⟨k,rfl⟩ := hπ g
    obtain ⟨x,rfl⟩ := hv
    exact ⟨ρ k x,d.sq_equivariant k x⟩
  have first (a : F) (hs : ∀ v : W, (v,a • v) ∈ d.sq.range) : False := by
    let j : W →+ V := (AddMonoidHom.id W).prod
      { toFun := fun v => a • v
        map_zero' := smul_zero a
        map_add' := fun v w => smul_add a v w }
    apply no_retract_lift d hπ hc hF j (AddMonoidHom.fst W W) (fun _ => rfl)
    · intro g v
      change (specialLinearNatural 3 (π g) v,a • specialLinearNatural 3 (π g) v)=
        (specialLinearNatural 3 (π g) v,specialLinearNatural 3 (π g) (a • v))
      exact Prod.ext rfl (map_smul (specialLinearNatural 3 (π g)) a v).symm
    · intro g v; rfl
    · exact hs
  by_cases ht : d.sq.range=⊤
  · exact first 0 (fun _ => ht.symm ▸ AddSubgroup.mem_top _)
  rcases SL3ParabolicNatural.invariant_double_natural_classification d.sq.range hne ht hinv
    with hz | ⟨a,ha⟩
  · let j : W →+ V := (0 : W →+ W).prod (AddMonoidHom.id W)
    apply no_retract_lift d hπ hc hF j (AddMonoidHom.snd W W) (fun _ => rfl)
    · intro g v
      exact Prod.ext (map_zero _).symm rfl
    · intro g v; rfl
    · intro v
      exact (hz (0,v)).mpr rfl
  · exact first a (fun v => (ha (v,a • v)).mpr rfl)

end Representation.DoubledAbelianTorus
