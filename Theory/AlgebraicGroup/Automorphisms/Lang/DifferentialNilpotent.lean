module

public import Theory.AlgebraicGroup.Automorphisms.Lang.DifferentialSurjectivity

/-!
# The Lang differential from a nilpotent endomorphism differential

This module supplies the linear bridge in Steinberg [St2, 10.5] between the
identity differential of an algebraic-group endomorphism `sigma` and that of
its Lang morphism `x |-> x * sigma(x)⁻¹`.  On identity-point derivations the
Lang differential is `1 - d sigma`: multiplication differentiates to addition
and inversion differentiates to negation.  If `d sigma` is nilpotent, the
finite geometric series is a right inverse to `1 - d sigma`, so the Lang
differential is surjective.

For a semisimple group with finite fixed locus, Steinberg's preceding geometric
argument supplies exactly the nilpotence hypothesis used here.  That
fixed-locus-to-nilpotence theorem is deliberately separate: finite fixed
points do not imply this differential conclusion for arbitrary connected
algebraic groups.
-/

universe u

set_option linter.unusedSectionVars false

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem identityPointDerivation_prod_decomposition
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (D : IdentityPointDerivation (Variety.prod G H)) :
    D =
      identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G H)
          (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H) D) +
        identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
          (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.snd G H) D) := by
  apply coordinateTangentMap_injective (Variety.prod G H)
  funext i
  cases i with
  | inl i =>
      let a := Variety.PolynomialFunction.ofPolynomial (Variety.prod G H)
        (MvPolynomial.X (Sum.inl i))
      have hleft :
          (AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a) = a := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inl, AlgebraicGroup.Morphism.fst,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      have hright :
          (AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a) =
            algebraMap k (Variety.PolynomialFunction (Variety.prod G H))
              ((1 : Variety.Point G).val i) := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inr, AlgebraicGroup.Morphism.snd,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
        exact (polynomialFunction_algebraMap_apply (Variety.prod G H)
          ((1 : Variety.Point G).val i) x).symm
      change D a = D ((AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a)) +
        D ((AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a))
      rw [hleft, hright, D.map_algebraMap, add_zero]
  | inr i =>
      let a := Variety.PolynomialFunction.ofPolynomial (Variety.prod G H)
        (MvPolynomial.X (Sum.inr i))
      have hleft :
          (AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a) =
            algebraMap k (Variety.PolynomialFunction (Variety.prod G H))
              ((1 : Variety.Point H).val i) := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inl, AlgebraicGroup.Morphism.fst,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
        exact (polynomialFunction_algebraMap_apply (Variety.prod G H)
          ((1 : Variety.Point H).val i) x).symm
      have hright :
          (AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
              ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a) = a := by
        apply Variety.PolynomialFunction.ext
        intro x
        simp [a, Variety.Morphism.pullbackAlgHom,
          Variety.Morphism.pullbackRingHom, Variety.PolynomialFunction.pullback,
          AlgebraicGroup.Morphism.inr, AlgebraicGroup.Morphism.snd,
          Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun, Variety.prodPointEquiv,
          evalPolynomial]
      change D a = D ((AlgebraicGroup.Morphism.fst G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inl G H).toVariety.pullbackAlgHom a)) +
        D ((AlgebraicGroup.Morphism.snd G H).toVariety.pullbackAlgHom
          ((AlgebraicGroup.Morphism.inr G H).toVariety.pullbackAlgHom a))
      rw [hleft, hright, D.map_algebraMap, zero_add]

private theorem identityPointDerivationMorphismLinearMap_congr
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    {f g : Variety.Morphism G H}
    (hf : f.toFun 1 = 1) (hg : g.toFun 1 = 1) (hfg : f = g) :
    identityPointDerivationMorphismLinearMap f hf =
      identityPointDerivationMorphismLinearMap g hg := by
  subst g
  rfl

private theorem identityPointDerivationMorphismLinearMap_groupMorphism
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) :
    identityPointDerivationMorphismLinearMap f.toVariety f.map_one =
      identityTangentMorphismLinearMap f := by
  rfl

private theorem pair_identity
    {U G H : Variety k} [AlgebraicGroup U] [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Variety.Morphism U G) (g : Variety.Morphism U H)
    (hf : f.toFun 1 = 1) (hg : g.toFun 1 = 1) :
    letI : AlgebraicGroup (Variety.prod G H) := AlgebraicGroup.prod G H
    (f.pair g).toFun 1 = 1 := by
  let _ : AlgebraicGroup (Variety.prod G H) := AlgebraicGroup.prod G H
  apply (Variety.prodPointEquiv G H).injective
  change (f.toFun 1, g.toFun 1) = (1, 1)
  rw [hf, hg]

private theorem identityPointDerivationMorphismLinearMap_fst_pair
    {U G H : Variety k} [AlgebraicGroup U] [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Variety.Morphism U G) (g : Variety.Morphism U H)
    (hf : f.toFun 1 = 1) (hg : g.toFun 1 = 1) :
    letI : AlgebraicGroup (Variety.prod G H) := AlgebraicGroup.prod G H
    (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)).comp
        (identityPointDerivationMorphismLinearMap (f.pair g)
          (pair_identity f g hf hg)) =
      identityPointDerivationMorphismLinearMap f hf := by
  let _ : AlgebraicGroup (Variety.prod G H) := AlgebraicGroup.prod G H
  let hpair : (f.pair g).toFun 1 = 1 := pair_identity f g hf hg
  have hcomp := identityPointDerivationMorphismLinearMap_comp
    (f.pair g) (AlgebraicGroup.Morphism.fst G H).toVariety hpair
      (AlgebraicGroup.Morphism.fst G H).map_one
  rw [identityPointDerivationMorphismLinearMap_groupMorphism] at hcomp
  rw [← hcomp]
  apply identityPointDerivationMorphismLinearMap_congr
  apply Variety.Morphism.ext
  rfl

private theorem identityPointDerivationMorphismLinearMap_snd_pair
    {U G H : Variety k} [AlgebraicGroup U] [AlgebraicGroup G] [AlgebraicGroup H]
    (f : Variety.Morphism U G) (g : Variety.Morphism U H)
    (hf : f.toFun 1 = 1) (hg : g.toFun 1 = 1) :
    letI : AlgebraicGroup (Variety.prod G H) := AlgebraicGroup.prod G H
    (identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.snd G H)).comp
        (identityPointDerivationMorphismLinearMap (f.pair g)
          (pair_identity f g hf hg)) =
      identityPointDerivationMorphismLinearMap g hg := by
  let _ : AlgebraicGroup (Variety.prod G H) := AlgebraicGroup.prod G H
  let hpair : (f.pair g).toFun 1 = 1 := pair_identity f g hf hg
  have hcomp := identityPointDerivationMorphismLinearMap_comp
    (f.pair g) (AlgebraicGroup.Morphism.snd G H).toVariety hpair
      (AlgebraicGroup.Morphism.snd G H).map_one
  rw [identityPointDerivationMorphismLinearMap_groupMorphism] at hcomp
  rw [← hcomp]
  apply identityPointDerivationMorphismLinearMap_congr
  apply Variety.Morphism.ext
  rfl

private theorem mulMorphism_identity
    (G : Variety k) [AlgebraicGroup G] :
    (AlgebraicGroup.mulMorphism G).toFun 1 = 1 := by
  change (1 : Variety.Point G) * 1 = 1
  simp

private theorem identityPointDerivationMorphismLinearMap_mul_apply
    {G : Variety k} [AlgebraicGroup G]
    (D : IdentityPointDerivation (Variety.prod G G)) :
    letI : AlgebraicGroup (Variety.prod G G) := AlgebraicGroup.prod G G
    identityPointDerivationMorphismLinearMap
        (AlgebraicGroup.mulMorphism G) (mulMorphism_identity G) D =
      identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G G) D +
        identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.snd G G) D := by
  let _ : AlgebraicGroup (Variety.prod G G) := AlgebraicGroup.prod G G
  let dmul := identityPointDerivationMorphismLinearMap
    (AlgebraicGroup.mulMorphism G) (mulMorphism_identity G)
  let dinl := identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G G)
  let dinr := identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G G)
  let dfst := identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G G)
  let dsnd := identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.snd G G)
  have hsplit : D = dinl (dfst D) + dinr (dsnd D) :=
    identityPointDerivation_prod_decomposition D
  have hleft : ∀ E : IdentityPointDerivation G, dmul (dinl E) = E := by
    intro E
    have hcomp := identityPointDerivationMorphismLinearMap_comp
      (AlgebraicGroup.Morphism.inl G G).toVariety
      (AlgebraicGroup.mulMorphism G)
      (AlgebraicGroup.Morphism.inl G G).map_one (mulMorphism_identity G)
    have hmorph : (AlgebraicGroup.mulMorphism G).comp
        (AlgebraicGroup.Morphism.inl G G).toVariety =
          (AlgebraicGroup.Morphism.id G).toVariety := by
      apply Variety.Morphism.ext
      funext x
      change x * 1 = x
      simp
    calc
      dmul (dinl E) = identityPointDerivationMorphismLinearMap
          ((AlgebraicGroup.mulMorphism G).comp
            (AlgebraicGroup.Morphism.inl G G).toVariety) _ E :=
        (LinearMap.congr_fun hcomp E).symm
      _ = identityPointDerivationMorphismLinearMap
          (AlgebraicGroup.Morphism.id G).toVariety
            (AlgebraicGroup.Morphism.id G).map_one E := by
        exact LinearMap.congr_fun
          (identityPointDerivationMorphismLinearMap_congr _ _ hmorph) E
      _ = E := by rfl
  have hright : ∀ E : IdentityPointDerivation G, dmul (dinr E) = E := by
    intro E
    have hcomp := identityPointDerivationMorphismLinearMap_comp
      (AlgebraicGroup.Morphism.inr G G).toVariety
      (AlgebraicGroup.mulMorphism G)
      (AlgebraicGroup.Morphism.inr G G).map_one (mulMorphism_identity G)
    have hmorph : (AlgebraicGroup.mulMorphism G).comp
        (AlgebraicGroup.Morphism.inr G G).toVariety =
          (AlgebraicGroup.Morphism.id G).toVariety := by
      apply Variety.Morphism.ext
      funext x
      change 1 * x = x
      simp
    calc
      dmul (dinr E) = identityPointDerivationMorphismLinearMap
          ((AlgebraicGroup.mulMorphism G).comp
            (AlgebraicGroup.Morphism.inr G G).toVariety) _ E :=
        (LinearMap.congr_fun hcomp E).symm
      _ = identityPointDerivationMorphismLinearMap
          (AlgebraicGroup.Morphism.id G).toVariety
            (AlgebraicGroup.Morphism.id G).map_one E := by
        exact LinearMap.congr_fun
          (identityPointDerivationMorphismLinearMap_congr _ _ hmorph) E
      _ = E := by rfl
  change dmul D = dfst D + dsnd D
  calc
    dmul D = dmul (dinl (dfst D) + dinr (dsnd D)) := congrArg dmul hsplit
    _ = dmul (dinl (dfst D)) + dmul (dinr (dsnd D)) := map_add dmul _ _
    _ = dfst D + dsnd D := by rw [hleft, hright]

private theorem identityPointDerivationMorphismLinearMap_mul_pair
    {U G : Variety k} [AlgebraicGroup U] [AlgebraicGroup G]
    (f g : Variety.Morphism U G) (hf : f.toFun 1 = 1) (hg : g.toFun 1 = 1) :
    letI : AlgebraicGroup (Variety.prod G G) := AlgebraicGroup.prod G G
    identityPointDerivationMorphismLinearMap
        ((AlgebraicGroup.mulMorphism G).comp (f.pair g))
        (by
          change (AlgebraicGroup.mulMorphism G).toFun ((f.pair g).toFun 1) = 1
          rw [show (f.pair g).toFun 1 = 1 from pair_identity f g hf hg]
          exact mulMorphism_identity G) =
      identityPointDerivationMorphismLinearMap f hf +
        identityPointDerivationMorphismLinearMap g hg := by
  let _ : AlgebraicGroup (Variety.prod G G) := AlgebraicGroup.prod G G
  let hpair : (f.pair g).toFun 1 = 1 := pair_identity f g hf hg
  let hmul := mulMorphism_identity G
  have hcomp := identityPointDerivationMorphismLinearMap_comp
    (f.pair g) (AlgebraicGroup.mulMorphism G) hpair hmul
  rw [hcomp]
  apply LinearMap.ext
  intro D
  rw [LinearMap.comp_apply, identityPointDerivationMorphismLinearMap_mul_apply]
  have hfst := LinearMap.congr_fun
    (identityPointDerivationMorphismLinearMap_fst_pair f g hf hg) D
  have hsnd := LinearMap.congr_fun
    (identityPointDerivationMorphismLinearMap_snd_pair f g hf hg) D
  simpa only [LinearMap.comp_apply, LinearMap.add_apply] using congrArg₂ (· + ·) hfst hsnd

private theorem identityPointDerivationMorphismLinearMap_const_one
    {U G : Variety k} [AlgebraicGroup U] [AlgebraicGroup G] :
    identityPointDerivationMorphismLinearMap
        (Variety.Morphism.const U G 1) rfl = 0 := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro a
  change D ((Variety.Morphism.const U G 1).pullbackAlgHom a) = 0
  have hpull : (Variety.Morphism.const U G 1).pullbackAlgHom a =
      algebraMap k (Variety.PolynomialFunction U) (a 1) := by
    apply Variety.PolynomialFunction.ext
    intro x
    change a 1 = (algebraMap k (Variety.PolynomialFunction U) (a 1)) x
    exact (polynomialFunction_algebraMap_apply U (a 1) x).symm
  rw [hpull, D.map_algebraMap]

private theorem invMorphism_identity
    (G : Variety k) [AlgebraicGroup G] :
    (AlgebraicGroup.invMorphism G).toFun 1 = 1 := by
  change (1 : Variety.Point G)⁻¹ = 1
  simp

private theorem identityPointDerivationMorphismLinearMap_inv
    {G : Variety k} [AlgebraicGroup G] :
    identityPointDerivationMorphismLinearMap
        (AlgebraicGroup.invMorphism G) (invMorphism_identity G) =
      -LinearMap.id := by
  let id := (AlgebraicGroup.Morphism.id G).toVariety
  let inv := AlgebraicGroup.invMorphism G
  let hid : id.toFun 1 = 1 := (AlgebraicGroup.Morphism.id G).map_one
  let hinv : inv.toFun 1 = 1 := invMorphism_identity G
  let pair := id.pair inv
  let hpair : pair.toFun 1 = 1 := pair_identity id inv hid hinv
  let mulInv := (AlgebraicGroup.mulMorphism G).comp pair
  let hmulInv : mulInv.toFun 1 = 1 := by
    change (AlgebraicGroup.mulMorphism G).toFun (pair.toFun 1) = 1
    rw [hpair]
    exact mulMorphism_identity G
  have hmulPair := identityPointDerivationMorphismLinearMap_mul_pair
    id inv hid hinv
  have hmorph : mulInv = Variety.Morphism.const G G 1 := by
    apply Variety.Morphism.ext
    funext x
    change x * x⁻¹ = 1
    simp
  have hconst := identityPointDerivationMorphismLinearMap_const_one
    (U := G) (G := G)
  have hsum :
      LinearMap.id + identityPointDerivationMorphismLinearMap inv hinv = 0 := by
    calc
      LinearMap.id + identityPointDerivationMorphismLinearMap inv hinv =
          identityPointDerivationMorphismLinearMap id hid +
            identityPointDerivationMorphismLinearMap inv hinv := by rfl
      _ = identityPointDerivationMorphismLinearMap mulInv hmulInv := hmulPair.symm
      _ = identityPointDerivationMorphismLinearMap
          (Variety.Morphism.const G G 1) rfl :=
        identityPointDerivationMorphismLinearMap_congr _ _ hmorph
      _ = 0 := hconst
  apply LinearMap.ext
  intro D
  have hsumD := LinearMap.congr_fun hsum D
  change D + identityPointDerivationMorphismLinearMap inv hinv D = 0 at hsumD
  change identityPointDerivationMorphismLinearMap inv hinv D = -D
  exact eq_neg_of_add_eq_zero_right hsumD

/-- At the identity, the Lang morphism `x |-> x * sigma(x)⁻¹` has differential
`1 - d sigma`. -/
public theorem identityPointDerivationMorphismLinearMap_langMorphism
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G) :
    identityPointDerivationMorphismLinearMap
        (langMorphism sigma) (langMorphism_identity sigma) =
      LinearMap.id - identityTangentMorphismLinearMap sigma := by
  let id := (AlgebraicGroup.Morphism.id G).toVariety
  let inv := AlgebraicGroup.invMorphism G
  let sigmaInv := sigma.toVariety.comp inv
  let hid : id.toFun 1 = 1 := (AlgebraicGroup.Morphism.id G).map_one
  let hinv : inv.toFun 1 = 1 := invMorphism_identity G
  let hsigmaInv : sigmaInv.toFun 1 = 1 := by
    change sigma.toVariety.toFun (inv.toFun 1) = 1
    rw [hinv]
    exact sigma.map_one
  have hmulPair := identityPointDerivationMorphismLinearMap_mul_pair
    id sigmaInv hid hsigmaInv
  have hcomp := identityPointDerivationMorphismLinearMap_comp
    inv sigma.toVariety hinv sigma.map_one
  rw [identityPointDerivationMorphismLinearMap_groupMorphism] at hcomp
  have hinvMap := identityPointDerivationMorphismLinearMap_inv (G := G)
  calc
    identityPointDerivationMorphismLinearMap
        (langMorphism sigma) (langMorphism_identity sigma) =
      identityPointDerivationMorphismLinearMap id hid +
        identityPointDerivationMorphismLinearMap sigmaInv hsigmaInv := by
          exact hmulPair
    _ = LinearMap.id +
        (identityTangentMorphismLinearMap sigma).comp
          (identityPointDerivationMorphismLinearMap inv hinv) := by
      rw [← hcomp]
      rfl
    _ = LinearMap.id +
        (identityTangentMorphismLinearMap sigma).comp (-LinearMap.id) := by
      rw [hinvMap]
    _ = LinearMap.id - identityTangentMorphismLinearMap sigma := by
      apply LinearMap.ext
      intro D
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply,
        map_neg, sub_eq_add_neg]

/-- A nilpotent identity differential makes the differential of the Lang
morphism surjective.  Steinberg [St2, 10.5] supplies this hypothesis from a
finite fixed locus when the ambient group is semisimple. -/
public theorem langMorphism_identity_differential_surjective_of_nilpotent
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hNilpotent : IsNilpotent (identityTangentMorphismLinearMap sigma)) :
    Function.Surjective
      (identityPointDerivationMorphismLinearMap
        (langMorphism sigma) (langMorphism_identity sigma)) := by
  rw [identityPointDerivationMorphismLinearMap_langMorphism]
  let d := identityTangentMorphismLinearMap sigma
  obtain ⟨n, hn⟩ := hNilpotent
  let inverse : Module.End k (IdentityPointDerivation G) :=
    ∑ i ∈ Finset.range n, d ^ i
  intro D
  refine ⟨inverse D, ?_⟩
  have hgeom := mul_neg_geom_sum d n
  rw [hn] at hgeom
  have hpoint := LinearMap.congr_fun hgeom D
  simpa only [Module.End.one_eq_id, Module.End.mul_apply, inverse,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.zero_apply, sub_zero]
    using hpoint

end Theory.AlgebraicGroup.Bor1
