module

public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.Morphism.Isogeny
public import Theory.AlgebraicGroup.Product

/-!
Closed equalizers and the connected pullback used to lift endomorphisms.

For an isogeny `u : Ku -> K` and an endomorphism `f` of `K`, the subgroup
`E = {(x, y) | f (u x) = u y}` is the equalizer of two morphisms on
`Ku x Ku`, hence is Zariski closed.  Its first projection is surjective when
`u` is, and its kernel embeds through the second projection into `ker u`.
When `Ku` is connected, the first projection remains surjective on the
identity component of `E`: the identity component has finite index, so its
image is a finite-index closed subgroup of the connected target.  The same
kernel embedding makes this restricted projection an isogeny.

This supplies the geometric pullback input for applying `IsUniversalVersion`
to the lifting conclusion of Steinberg [St2, Theorem 9.16], quoted in GLS3
Theorem 2.1.2(e).  The construction is kept in the morphism layer because it
uses only connectedness and isogenies, not semisimplicity or root data.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The equalizer of two algebraic-group morphisms as a closed subgroup. -/
@[expose]
public def Morphism.equalizerClosedSubgroup
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f g : Morphism G H) : ClosedSubgroup G :=
  ClosedSubgroup.ofSubgroup (f.onPoints.eqLocus g.onPoints) (by
    change IsZariskiClosed G {x | f.toVariety.toFun x = g.toVariety.toFun x}
    exact Variety.Morphism.isZariskiClosed_equalizer f.toVariety g.toVariety)

/-- Membership in the closed equalizer is pointwise equality of the maps. -/
public lemma Morphism.mem_equalizerClosedSubgroup_iff
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f g : Morphism G H) (x : Variety.Point G) :
    x ∈ (f.equalizerClosedSubgroup g).toSubgroup ↔
      f.onPoints x = g.onPoints x := Iff.rfl

/-- The pullback subgroup of pairs satisfying `f (u x) = u y`. -/
@[expose]
public noncomputable def Morphism.endomorphismPullbackClosedSubgroup
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    ClosedSubgroup (Variety.prod Ku Ku) :=
  ((f.comp u).comp (Morphism.fst Ku Ku)).equalizerClosedSubgroup
    (u.comp (Morphism.snd Ku Ku))

/-- The pullback carrier has its canonical closed-subgroup algebraic structure. -/
public noncomputable instance Morphism.endomorphismPullbackCarrierAlgebraicGroup
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    AlgebraicGroup (u.endomorphismPullbackClosedSubgroup f).carrierVariety :=
  (u.endomorphismPullbackClosedSubgroup f).carrierAlgebraicGroup

/-- The pointwise equation defining the endomorphism pullback. -/
public lemma Morphism.mem_endomorphismPullbackClosedSubgroup_iff
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (z : Variety.Point (Variety.prod Ku Ku)) :
    z ∈ (u.endomorphismPullbackClosedSubgroup f).toSubgroup ↔
      f.onPoints (u.onPoints (Variety.prodPointEquiv Ku Ku z).1) =
        u.onPoints (Variety.prodPointEquiv Ku Ku z).2 := by
  rfl

/-- First projection from the endomorphism pullback. -/
@[expose]
public noncomputable def Morphism.endomorphismPullbackFirstProjection
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    Morphism (u.endomorphismPullbackClosedSubgroup f).carrierVariety Ku :=
  (Morphism.fst Ku Ku).comp
    (u.endomorphismPullbackClosedSubgroup f).inclusion

/-- Second projection from the endomorphism pullback. -/
@[expose]
public noncomputable def Morphism.endomorphismPullbackSecondProjection
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    Morphism (u.endomorphismPullbackClosedSubgroup f).carrierVariety Ku :=
  (Morphism.snd Ku Ku).comp
    (u.endomorphismPullbackClosedSubgroup f).inclusion

/-- The pullback projections satisfy `u p₂ = f u p₁` on points. -/
public lemma Morphism.endomorphismPullback_factorization
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (z : Variety.Point (u.endomorphismPullbackClosedSubgroup f).carrierVariety) :
    u.onPoints ((u.endomorphismPullbackSecondProjection f).onPoints z) =
      f.onPoints (u.onPoints
        ((u.endomorphismPullbackFirstProjection f).onPoints z)) := by
  have hz := (u.endomorphismPullbackClosedSubgroup f).pointEquiv z |>.property
  exact hz.symm

/-- Surjectivity of `u` makes the first pullback projection surjective. -/
public theorem Morphism.endomorphismPullbackFirstProjection_surjective
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (hu : Function.Surjective u.onPoints) :
    Function.Surjective
      (u.endomorphismPullbackFirstProjection f).onPoints := by
  intro x
  obtain ⟨y, hy⟩ := hu (f.onPoints (u.onPoints x))
  let E := u.endomorphismPullbackClosedSubgroup f
  let z0 : Variety.Point (Variety.prod Ku Ku) :=
    (Variety.prodPointEquiv Ku Ku).symm (x, y)
  have hz0 : z0 ∈ E.toSubgroup := by
    apply (u.mem_endomorphismPullbackClosedSubgroup_iff f z0).2
    change f.onPoints (u.onPoints x) = u.onPoints y
    exact hy.symm
  let z : Variety.Point E.carrierVariety := E.pointEquiv.symm ⟨z0, hz0⟩
  refine ⟨z, ?_⟩
  change (Variety.prodPointEquiv Ku Ku (E.pointEquiv z).val).1 = x
  rw [show E.pointEquiv z = ⟨z0, hz0⟩ by
    dsimp only [z]
    rw [E.pointEquiv.apply_symm_apply]]
  dsimp only [z0]
  rw [Equiv.apply_symm_apply]

/-- The first projection has finite kernel when `u` does. -/
public theorem Morphism.endomorphismPullbackFirstProjection_kernel_finite
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (hu : Finite u.kernel) :
    Finite (u.endomorphismPullbackFirstProjection f).kernel := by
  let E := u.endomorphismPullbackClosedSubgroup f
  let p1 := u.endomorphismPullbackFirstProjection f
  let p2 := u.endomorphismPullbackSecondProjection f
  let embed : p1.kernel → u.kernel := fun z =>
    ⟨p2.onPoints z.1, by
      change u.onPoints (p2.onPoints z.1) = 1
      rw [u.endomorphismPullback_factorization f z.1]
      have hz : p1.onPoints z.1 = 1 := MonoidHom.mem_ker.mp z.2
      rw [hz]
      simp⟩
  let : Finite u.kernel := hu
  exact Finite.of_injective embed (by
    intro z w hzw
    apply Subtype.ext
    apply E.inclusion_injective
    apply (Variety.prodPointEquiv Ku Ku).injective
    apply Prod.ext
    · exact (MonoidHom.mem_ker.mp z.2).trans
        (MonoidHom.mem_ker.mp w.2).symm
    · exact congrArg Subtype.val hzw)

/-- The first projection from the full pullback of an isogeny is an isogeny. -/
public theorem Morphism.endomorphismPullbackFirstProjection_isogeny
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) (hu : IsIsogeny u) :
    IsIsogeny (u.endomorphismPullbackFirstProjection f) :=
  ⟨u.endomorphismPullbackFirstProjection_surjective f hu.1,
    u.endomorphismPullbackFirstProjection_kernel_finite f hu.2⟩

/-- The identity component of the endomorphism pullback. -/
@[expose]
public noncomputable def Morphism.endomorphismPullbackIdentityComponent
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    ClosedSubgroup E.carrierVariety := by
  dsimp only
  exact identityComponentClosedSubgroup _

/-- The identity-component carrier has its canonical algebraic structure. -/
public noncomputable instance
    Morphism.endomorphismPullbackIdentityComponentCarrierAlgebraicGroup
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    AlgebraicGroup
      (u.endomorphismPullbackIdentityComponent f).carrierVariety := by
  dsimp only
  exact (u.endomorphismPullbackIdentityComponent f).carrierAlgebraicGroup

/-- First projection restricted to the identity component of the pullback. -/
@[expose]
public noncomputable def
    Morphism.endomorphismPullbackIdentityComponentFirstProjection
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    let E0 := u.endomorphismPullbackIdentityComponent f
    let _ : AlgebraicGroup E0.carrierVariety := E0.carrierAlgebraicGroup
    Morphism E0.carrierVariety Ku := by
  dsimp only
  exact (u.endomorphismPullbackFirstProjection f).comp
    (u.endomorphismPullbackIdentityComponent f).inclusion

/-- Second projection restricted to the identity component of the pullback. -/
@[expose]
public noncomputable def
    Morphism.endomorphismPullbackIdentityComponentSecondProjection
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    let E0 := u.endomorphismPullbackIdentityComponent f
    let _ : AlgebraicGroup E0.carrierVariety := E0.carrierAlgebraicGroup
    Morphism E0.carrierVariety Ku := by
  dsimp only
  exact (u.endomorphismPullbackSecondProjection f).comp
    (u.endomorphismPullbackIdentityComponent f).inclusion

/-- The identity-component pullback carrier is connected. -/
public lemma Morphism.endomorphismPullbackIdentityComponent_isConnected
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    Variety.IsConnected
      (u.endomorphismPullbackIdentityComponent f).carrierVariety := by
  dsimp only
  exact identityComponentClosedSubgroup_carrier_isConnected _

/-- The identity-component projections still satisfy `u p₂ = f u p₁`. -/
public lemma Morphism.endomorphismPullbackIdentityComponent_factorization
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (z : Variety.Point
      (u.endomorphismPullbackIdentityComponent f).carrierVariety) :
    u.onPoints
        ((u.endomorphismPullbackIdentityComponentSecondProjection f).onPoints z) =
      f.onPoints (u.onPoints
        ((u.endomorphismPullbackIdentityComponentFirstProjection f).onPoints z)) := by
  let E0 := u.endomorphismPullbackIdentityComponent f
  exact u.endomorphismPullback_factorization f (E0.inclusion.onPoints z)

section

variable [IsAlgClosed k]

/-- On a connected source, the identity-component first projection is surjective. -/
public theorem
    Morphism.endomorphismPullbackIdentityComponentFirstProjection_surjective
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (hKu : Variety.IsConnected Ku)
    (hu : Function.Surjective u.onPoints) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    let E0 := u.endomorphismPullbackIdentityComponent f
    let _ : AlgebraicGroup E0.carrierVariety := E0.carrierAlgebraicGroup
    Function.Surjective
      (u.endomorphismPullbackIdentityComponentFirstProjection f).onPoints := by
  dsimp only
  let E := u.endomorphismPullbackClosedSubgroup f
  letI : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
  let E0 := u.endomorphismPullbackIdentityComponent f
  letI : AlgebraicGroup E0.carrierVariety := E0.carrierAlgebraicGroup
  let R : ClosedSubgroup Ku := ClosedSubgroup.top
  let g : Morphism E.carrierVariety R.carrierVariety :=
    (u.endomorphismPullbackFirstProjection f).codRestrictClosedSubgroup R
      (fun _ => R.toSubgroup.one_mem)
  have hg : Function.Surjective g.onPoints := by
    intro y
    obtain ⟨x, hx⟩ := u.endomorphismPullbackFirstProjection_surjective f hu
      ((R.pointEquiv y).val)
    refine ⟨x, ?_⟩
    apply R.inclusion_injective
    change (u.endomorphismPullbackFirstProjection f).onPoints x =
      (R.pointEquiv y).val
    exact hx
  have hR : _root_.IsConnected (R : Set (Variety.Point Ku)) := by
    change _root_.IsConnected (Set.univ : Set (Variety.Point Ku))
    exact hKu
  let : E0.toSubgroup.FiniteIndex := by
    change (AlgebraicGroup.identityComponentSubgroup E.carrierVariety).FiniteIndex
    infer_instance
  have hs := finiteIndex_subgroup_surjective_of_connected_target
    E E0 R g hg hR
  intro y
  let yR : Variety.Point R.carrierVariety :=
    R.pointEquiv.symm ⟨y, R.toSubgroup.one_mem⟩
  obtain ⟨x, hx⟩ := hs yR
  refine ⟨x, ?_⟩
  have hx' := congrArg R.inclusion.onPoints hx
  change (u.endomorphismPullbackFirstProjection f).onPoints
      (E0.inclusion.onPoints x) = y at hx'
  exact hx'

omit [IsAlgClosed k] in
/-- The identity-component first projection has finite kernel when `u` does. -/
public theorem
    Morphism.endomorphismPullbackIdentityComponentFirstProjection_kernel_finite
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (hu : Finite u.kernel) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    let E0 := u.endomorphismPullbackIdentityComponent f
    let _ : AlgebraicGroup E0.carrierVariety := E0.carrierAlgebraicGroup
    Finite
      (u.endomorphismPullbackIdentityComponentFirstProjection f).kernel := by
  dsimp only
  let E := u.endomorphismPullbackClosedSubgroup f
  letI : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
  let E0 := u.endomorphismPullbackIdentityComponent f
  letI : AlgebraicGroup E0.carrierVariety := E0.carrierAlgebraicGroup
  let p10 := u.endomorphismPullbackIdentityComponentFirstProjection f
  let p20 := u.endomorphismPullbackIdentityComponentSecondProjection f
  let embed : p10.kernel → u.kernel := fun z =>
    ⟨p20.onPoints z.1, by
      change u.onPoints (p20.onPoints z.1) = 1
      rw [u.endomorphismPullbackIdentityComponent_factorization f z.1]
      have hz : p10.onPoints z.1 = 1 := MonoidHom.mem_ker.mp z.2
      rw [hz]
      simp⟩
  let : Finite u.kernel := hu
  exact Finite.of_injective embed (by
    intro z w hzw
    apply Subtype.ext
    apply E0.inclusion_injective
    apply E.inclusion_injective
    apply (Variety.prodPointEquiv Ku Ku).injective
    apply Prod.ext
    · exact (MonoidHom.mem_ker.mp z.2).trans
        (MonoidHom.mem_ker.mp w.2).symm
    · exact congrArg Subtype.val hzw)

/-- The connected pullback projection is an isogeny onto `Ku`. -/
public theorem
    Morphism.endomorphismPullbackIdentityComponentFirstProjection_isogeny
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    (u : Morphism Ku K) (f : Morphism K K)
    (hKu : Variety.IsConnected Ku) (hu : IsIsogeny u) :
    let E := u.endomorphismPullbackClosedSubgroup f
    let _ : AlgebraicGroup E.carrierVariety := E.carrierAlgebraicGroup
    let E0 := u.endomorphismPullbackIdentityComponent f
    let _ : AlgebraicGroup E0.carrierVariety := E0.carrierAlgebraicGroup
    IsIsogeny
      (u.endomorphismPullbackIdentityComponentFirstProjection f) := by
  dsimp only
  exact
    ⟨u.endomorphismPullbackIdentityComponentFirstProjection_surjective
        f hKu hu.1,
      u.endomorphismPullbackIdentityComponentFirstProjection_kernel_finite
        f hu.2⟩

end

end Theory.AlgebraicGroup
