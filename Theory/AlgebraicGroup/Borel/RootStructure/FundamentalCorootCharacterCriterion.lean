module

public import Theory.AlgebraicGroup.Borel.RootStructure.FundamentalCorootData
public import Theory.AlgebraicGroup.Semisimple.Versions
public import Theory.AlgebraicGroup.Tori.IsoOfCharacterPullbackSurjective

/-!
This module supplies the torus-theoretic part of the fundamental-coroot
criterion in GLS3, Theorem 1.12.5(b).  Given algebraic root cocharacters, it
constructs their product morphism from a product of multiplicative groups and
proves the required Chevalley point formula.  Once point-surjectivity is known,
the morphism is an isomorphism exactly when pullback is surjective on torus
characters.

The construction takes coordinate projections, composes them with the chosen
cocharacters, and multiplies the resulting morphisms in the commutative target
torus.  The final equivalence uses character functoriality for an isomorphism
in one direction and the torus character-pullback isomorphism criterion in the
other.  The remaining comparison with semantic universality is whole-group
root-datum mathematics, not part of this lower torus layer.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private def oneMorphism
    (G H : Variety k) [AlgebraicGroup G] [AlgebraicGroup H] :
    AlgebraicGroup.Morphism G H where
  toVariety := Variety.Morphism.const G H 1
  map_one := rfl
  map_mul := by
    intro _ _
    exact (one_mul 1).symm

private def mulMorphismOfCommutativeTarget
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hH : IsMulCommutative (Variety.Point H))
    (f g : AlgebraicGroup.Morphism G H) : AlgebraicGroup.Morphism G H where
  toVariety := (AlgebraicGroup.mulMorphism H).comp
    (f.toVariety.pair g.toVariety)
  map_one := by
    change f.onPoints 1 * g.onPoints 1 = 1
    rw [(f.onPoints).map_one, (g.onPoints).map_one, one_mul]
  map_mul := by
    intro x y
    change f.onPoints (x * y) * g.onPoints (x * y) =
      (f.onPoints x * g.onPoints x) * (f.onPoints y * g.onPoints y)
    rw [(f.onPoints).map_mul, (g.onPoints).map_mul]
    have hcomm : g.onPoints x * f.onPoints y =
        f.onPoints y * g.onPoints x :=
      (isMulCommutative_iff.mp hH) _ _
    calc
      (f.onPoints x * f.onPoints y) * (g.onPoints x * g.onPoints y) =
          f.onPoints x * (f.onPoints y * g.onPoints x) * g.onPoints y := by
            simp only [mul_assoc]
      _ = f.onPoints x * (g.onPoints x * f.onPoints y) * g.onPoints y := by
            rw [hcomm]
      _ = (f.onPoints x * g.onPoints x) *
          (f.onPoints y * g.onPoints y) := by simp only [mul_assoc]

private def morphismListProduct
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hH : IsMulCommutative (Variety.Point H)) :
    List (AlgebraicGroup.Morphism G H) → AlgebraicGroup.Morphism G H
  | [] => oneMorphism G H
  | f :: fs => mulMorphismOfCommutativeTarget hH f
      (morphismListProduct hH fs)

omit [IsAlgClosed k] in
private lemma morphismListProduct_apply
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hH : IsMulCommutative (Variety.Point H))
    (fs : List (AlgebraicGroup.Morphism G H)) (x : Variety.Point G) :
    (morphismListProduct hH fs).onPoints x =
      (fs.map fun f => f.onPoints x).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      change f.onPoints x * (morphismListProduct hH fs).onPoints x = _
      rw [ih]
      rfl

omit [IsAlgClosed k] in
private lemma dCoordinateCharacter_onPoints
    (n : Nat) (i : Fin n) (x : Variety.Point (dVariety k n)) :
    (dCoordinateCharacter n i).onPoints x =
      (dPointEquiv 1).symm (fun _ => dPointEquiv n x i) := by
  apply (dPointEquiv 1).injective
  funext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  rw [dCoordinateCharacter_apply]
  simp

private noncomputable def cocharacterProductMorphism
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    {n : Nat} (h : Fin n → AlgebraicGroup.Morphism (KMult k) T) :
    AlgebraicGroup.Morphism (dVariety k n) T :=
  morphismListProduct hT.isMulCommutative
    (List.ofFn fun i => (h i).comp (dCoordinateCharacter n i))

omit [IsAlgClosed k] in
private lemma cocharacterProductMorphism_apply
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    {n : Nat} (h : Fin n → AlgebraicGroup.Morphism (KMult k) T)
    (x : Variety.Point (dVariety k n)) :
    (cocharacterProductMorphism hT h).onPoints x =
      (List.ofFn fun i => (h i).onPoints
        ((dPointEquiv 1).symm (fun _ => dPointEquiv n x i))).prod := by
  rw [cocharacterProductMorphism, morphismListProduct_apply]
  apply congrArg List.prod
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext i
  change (h i).onPoints ((dCoordinateCharacter n i).onPoints x) = _
  rw [dCoordinateCharacter_onPoints]

/-- The product morphism of the algebraic coroots indexed by `order`. -/
public noncomputable def fundamentalCorootProductMorphism
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {iota R M N : Type*} [Finite iota] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing iota R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ iota)
    (base : P.Base) (hCoroot : IsAlgebraicFundamentalCorootData C P e base)
    (hT : IsSubtorus T) (order : List D.Root) :
    FundamentalCorootMorphism C order where
  map := cocharacterProductMorphism
    (by simpa only [IsSubtorus] using hT)
    (fun i => hCoroot.rootCocharacter (order.get i))
  point_formula := by
    intro x
    have hTorus : IsTorus T.carrierVariety := by
      simpa only [IsSubtorus] using hT
    rw [cocharacterProductMorphism_apply hTorus]
    change T.inclusion.onPoints
        ((List.ofFn fun i =>
          (hCoroot.rootCocharacter (order.get i)).onPoints
            ((dPointEquiv 1).symm
              (fun _ => dPointEquiv order.length x i))).prod) = _
    rw [map_list_prod, fundamentalCorootCoordinateWord_eq]
    apply congrArg List.prod
    rw [List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext i
    change T.includePoint
        ((hCoroot.rootCocharacter (order.get i)).onPoints
          ((dPointEquiv 1).symm
            (fun _ => dPointEquiv order.length x i))) = _
    exact hCoroot.h_spec (order.get i) (dPointEquiv order.length x i)

/-- For a point-surjective product of coroots, being an algebraic-group
isomorphism is equivalent to surjectivity of pullback on torus characters. -/
public theorem fundamentalCorootProductMorphism_iso_iff_characterPullback_surjective
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {iota R M N : Type*} [Finite iota] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing iota R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ iota)
    (base : P.Base) (hCoroot : IsAlgebraicFundamentalCorootData C P e base)
    (hT : IsSubtorus T) (order : List D.Root)
    (hsurjective : Function.Surjective
      (fundamentalCorootProductMorphism C P e base hCoroot hT order).map.onPoints) :
    (∃ iso : AlgebraicGroup.Iso (dVariety k order.length) T.carrierVariety,
      iso.hom =
        (fundamentalCorootProductMorphism C P e base hCoroot hT order).map) ↔
      Function.Surjective (TorusCharacter.pullback
        (fundamentalCorootProductMorphism C P e base hCoroot hT order).map) := by
  let phi :=
    (fundamentalCorootProductMorphism C P e base hCoroot hT order).map
  constructor
  · rintro ⟨iso, hiso⟩
    subst phi
    rw [← hiso]
    intro character
    refine ⟨TorusCharacter.pullback iso.inv character, ?_⟩
    apply AlgebraicGroup.Morphism.ext
    funext x
    change character.onPoints
        (iso.inv.onPoints (iso.hom.onPoints x)) = character.onPoints x
    rw [iso.hom_inv_id]
  · intro hpullback
    exact torusIso_of_surjective_of_character_pullback_surjective
      (dVariety_isTorus order.length) hT phi hsurjective hpullback

/-- Logical assembly of the torus criterion with a whole-group theorem
identifying semantic universality with surjectivity on characters. -/
public theorem fundamentalCorootProductMorphism_universal_iff_iso_of_characterPullback
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (C : ChevalleyData K D)
    {iota R M N : Type*} [Finite iota] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing iota R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (e : D.Root ≃ iota)
    (base : P.Base) (hCoroot : IsAlgebraicFundamentalCorootData C P e base)
    (hT : IsSubtorus T) (order : List D.Root)
    (hsurjective : Function.Surjective
      (fundamentalCorootProductMorphism C P e base hCoroot hT order).map.onPoints)
    (huniversal : IsUniversalVersion K ↔
      Function.Surjective (TorusCharacter.pullback
        (fundamentalCorootProductMorphism C P e base hCoroot hT order).map)) :
    IsUniversalVersion K ↔
      ∃ iso : AlgebraicGroup.Iso (dVariety k order.length) T.carrierVariety,
        iso.hom =
          (fundamentalCorootProductMorphism C P e base hCoroot hT order).map :=
  huniversal.trans
    (fundamentalCorootProductMorphism_iso_iff_characterPullback_surjective
      C P e base hCoroot hT order hsurjective).symm

end Theory.AlgebraicGroup
