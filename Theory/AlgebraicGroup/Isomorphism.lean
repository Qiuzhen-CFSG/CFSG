module

public import Theory.AlgebraicGroup.Morphism.Reconstruction
public import Theory.AlgebraicGroup.Product
public import Theory.AlgebraicGroup.Variety.AffineDuality

universe u

/-! Isomorphisms of algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- An isomorphism of algebraic groups. -/
public structure Iso (G H : Variety k)
    [AlgebraicGroup G] [AlgebraicGroup H] where
  hom : Theory.AlgebraicGroup.Morphism G H
  inv : Theory.AlgebraicGroup.Morphism H G
  hom_inv_id : ∀ x, inv.onPoints (hom.onPoints x) = x
  inv_hom_id : ∀ y, hom.onPoints (inv.onPoints y) = y

@[expose]
public def Iso.id (G : Variety k) [AlgebraicGroup G] :
    Theory.AlgebraicGroup.Iso G G where
  hom := Theory.AlgebraicGroup.Morphism.id G
  inv := Theory.AlgebraicGroup.Morphism.id G
  hom_inv_id := by intro x; rfl
  inv_hom_id := by intro x; rfl

/-- Reverse an algebraic-group isomorphism. -/
@[expose]
public def Iso.symm
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : Theory.AlgebraicGroup.Iso G H) :
    Theory.AlgebraicGroup.Iso H G where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

@[expose]
public def Iso.comp
    {G H I : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] [AlgebraicGroup I]
    (e : Theory.AlgebraicGroup.Iso H I) (d : Theory.AlgebraicGroup.Iso G H) :
    Theory.AlgebraicGroup.Iso G I where
  hom := e.hom.comp d.hom
  inv := d.inv.comp e.inv
  hom_inv_id := by
    intro x
    change d.inv.onPoints
      (e.inv.onPoints (e.hom.onPoints (d.hom.onPoints x))) = x
    rw [e.hom_inv_id, d.hom_inv_id]
  inv_hom_id := by
    intro y
    change e.hom.onPoints
      (d.hom.onPoints (d.inv.onPoints (e.inv.onPoints y))) = y
    rw [d.inv_hom_id, e.inv_hom_id]

/-- Mutually inverse algebraic-group morphisms determine an algebraic-group
isomorphism. -/
public def Iso.ofInverseMorphisms
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Theory.AlgebraicGroup.Morphism G H)
    (g : Theory.AlgebraicGroup.Morphism H G)
    (hgf : ∀ x, g.onPoints (f.onPoints x) = x)
    (hfg : ∀ y, f.onPoints (g.onPoints y) = y) :
    Theory.AlgebraicGroup.Iso G H where
  hom := f
  inv := g
  hom_inv_id := hgf
  inv_hom_id := hfg

@[expose]
public def Iso.toMulEquiv
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : Theory.AlgebraicGroup.Iso G H) :
    Variety.Point G ≃* Variety.Point H where
  toFun := e.hom.onPoints
  invFun := e.inv.onPoints
  left_inv := e.hom_inv_id
  right_inv := e.inv_hom_id
  map_mul' := e.hom.onPoints.map_mul

/-- The direct product of two algebraic-group isomorphisms. -/
@[expose]
public noncomputable def Iso.prod
    {G H I J : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H]
    [AlgebraicGroup I] [AlgebraicGroup J]
    (e : AlgebraicGroup.Iso G H) (f : AlgebraicGroup.Iso I J) :
    AlgebraicGroup.Iso (Variety.prod G I) (Variety.prod H J) where
  hom := AlgebraicGroup.Morphism.prod
    (e.hom.comp (AlgebraicGroup.Morphism.fst G I))
    (f.hom.comp (AlgebraicGroup.Morphism.snd G I))
  inv := AlgebraicGroup.Morphism.prod
    (e.inv.comp (AlgebraicGroup.Morphism.fst H J))
    (f.inv.comp (AlgebraicGroup.Morphism.snd H J))
  hom_inv_id := by
    intro x
    apply (Variety.prodPointEquiv G I).injective
    apply Prod.ext
    · exact e.hom_inv_id (Variety.prodPointEquiv G I x).1
    · exact f.hom_inv_id (Variety.prodPointEquiv G I x).2
  inv_hom_id := by
    intro x
    apply (Variety.prodPointEquiv H J).injective
    apply Prod.ext
    · exact e.inv_hom_id (Variety.prodPointEquiv H J x).1
    · exact f.inv_hom_id (Variety.prodPointEquiv H J x).2

/-- Upgrade an algebraic-group morphism to an isomorphism when its pullback on
polynomial functions is a specified algebra equivalence. -/
@[expose]
public noncomputable def Iso.ofPullbackAlgEquiv
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (e : Variety.PolynomialFunction H ≃ₐ[k]
      Variety.PolynomialFunction G)
    (hpull : f.toVariety.pullbackAlgHom = e.toAlgHom) :
    AlgebraicGroup.Iso G H := by
  let g : Variety.Morphism H G :=
    Variety.Morphism.ofPolynomialFunctionAlgHom e.symm.toAlgHom
  have hg : g.pullbackAlgHom = e.symm.toAlgHom :=
    Variety.Morphism.pullbackAlgHom_ofPolynomialFunctionAlgHom _
  have hgf : ∀ x : Variety.Point G, g.toFun (f.onPoints x) = x := by
    intro x
    apply Variety.Point.ext
    funext i
    let q := Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X i)
    have hq : q (g.toFun (f.onPoints x)) = q x := by
      calc
        q (g.toFun (f.onPoints x)) =
            g.pullbackAlgHom q (f.onPoints x) := rfl
        _ = f.toVariety.pullbackAlgHom (g.pullbackAlgHom q) x := rfl
        _ = e (e.symm q) x := by rw [hg, hpull]; rfl
        _ = q x := by rw [e.apply_symm_apply]
    simpa [q, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial] using hq
  have hfg : ∀ y : Variety.Point H, f.onPoints (g.toFun y) = y := by
    intro y
    apply Variety.Point.ext
    funext i
    let q := Variety.PolynomialFunction.ofPolynomial H (MvPolynomial.X i)
    have hq : q (f.onPoints (g.toFun y)) = q y := by
      calc
        q (f.onPoints (g.toFun y)) =
            f.toVariety.pullbackAlgHom q (g.toFun y) := rfl
        _ = g.pullbackAlgHom (f.toVariety.pullbackAlgHom q) y := rfl
        _ = e.symm (e q) y := by rw [hg, hpull]; rfl
        _ = q y := by rw [e.symm_apply_apply]
    simpa [q, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun, evalPolynomial] using hq
  have hf_injective : Function.Injective f.onPoints :=
    Function.LeftInverse.injective hgf
  let inv : AlgebraicGroup.Morphism H G :=
    { toVariety := g
      map_one := by
        apply hf_injective
        rw [hfg]
        exact f.map_one.symm
      map_mul := by
        intro x y
        apply hf_injective
        rw [hfg]
        exact (congrArg₂ (· * ·) (hfg x) (hfg y)).symm.trans
          (f.map_mul (g.toFun x) (g.toFun y)).symm }
  exact Iso.ofInverseMorphisms f inv hgf hfg

/-- The homomorphism of an algebraic-group isomorphism has surjective
pullback on polynomial functions. -/
public lemma algebraicGroupIso_hom_pullbackRingHom_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : AlgebraicGroup.Iso G H) :
    Function.Surjective e.hom.toVariety.pullbackRingHom := by
  intro q
  refine ⟨e.inv.toVariety.pullbackRingHom q, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change q (e.inv.onPoints (e.hom.onPoints x)) = q x
  rw [e.hom_inv_id]

/-- A pointwise bijective algebraic-group morphism is an algebraic-group
isomorphism once its pullback on polynomial functions is surjective. -/
public theorem algebraicGroupIso_of_bijective_morphism_of_pullback_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (π : AlgebraicGroup.Morphism G H)
    (hbij : Function.Bijective π.onPoints)
    (hpull : Function.Surjective π.toVariety.pullbackRingHom) :
    ∃ e : AlgebraicGroup.Iso G H, e.hom = π := by
  let epoints : Variety.Point H ≃* Variety.Point G :=
    (MulEquiv.ofBijective π.onPoints hbij).symm
  let ψ : Variety.Point H →* Variety.Point G := epoints.toMonoidHom
  have hcomp : ψ.comp π.onPoints =
      (AlgebraicGroup.Morphism.id G).onPoints := by
    apply MonoidHom.ext
    intro x
    change (MulEquiv.ofBijective π.onPoints hbij).symm (π.onPoints x) = x
    exact (MulEquiv.ofBijective π.onPoints hbij).symm_apply_apply x
  obtain ⟨g, hg⟩ := π.exists_of_pointHom_of_pullback_surjective hbij.2 hpull
    (AlgebraicGroup.Morphism.id G) ψ hcomp
  have hleft : ∀ x, g.onPoints (π.onPoints x) = x := by
    intro x
    calc
      g.onPoints (π.onPoints x) = ψ (π.onPoints x) := by rw [hg]
      _ = (AlgebraicGroup.Morphism.id G).onPoints x :=
        congrArg (fun m : Variety.Point G →* Variety.Point G ↦ m x) hcomp
      _ = x := by rfl
  have hright : ∀ y, π.onPoints (g.onPoints y) = y := by
    intro y
    obtain ⟨x, hx⟩ := hbij.2 y
    rw [← hx, hleft]
  let e : AlgebraicGroup.Iso G H :=
    { hom := π
      inv := g
      hom_inv_id := hleft
      inv_hom_id := hright }
  exact ⟨e, rfl⟩

end Theory.AlgebraicGroup
