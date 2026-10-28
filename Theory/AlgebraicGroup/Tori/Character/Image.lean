module

public import Theory.AlgebraicGroup.Tori.Character.Classification
public import Theory.AlgebraicGroup.Tori.Character.SmithNormalForm

universe u

set_option linter.style.haveILetI false

/-! Closed images of morphisms from algebraic tori. -/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The closed image of a morphism from a standard diagonal torus is a
torus. -/
private lemma dMorphism_imageClosedSubgroup_isTorus
    {H : Variety k} [AlgebraicGroup H]
    (n : ℕ) (f : AlgebraicGroup.Morphism (dVariety k n) H) :
    let I := f.imageClosedSubgroup
    @IsTorus k _ I.carrierVariety I.carrierAlgebraicGroup := by
  let p : H.Coordinates → MvPolynomial (dVariety k n).Coordinates k :=
    fun i => Classical.choose (f.toVariety.regular i)
  have hp (i : H.Coordinates) (x : Variety.Point (dVariety k n)) :
      (f.onPoints x).val i = evalPolynomial x.val (p i) :=
    Classical.choose_spec (f.toVariety.regular i) x
  let S := Σ i : H.Coordinates,
    {z // z ∈ (dLaurentCoefficients n (p i)).support}
  let m := Fintype.card S
  let e : Fin m ≃ S := (Fintype.equivFin S).symm
  let zTuple : Fin m → Fin n → ℤ := fun j => (e j).2.1
  let χ := dCharacterTupleMorphism (k := k) m n zTuple
  have hχf {x y : Variety.Point (dVariety k n)}
      (hxy : χ.onPoints x = χ.onPoints y) :
      f.onPoints x = f.onPoints y := by
    apply Variety.Point.ext
    funext i
    rw [hp i x, hp i y,
      evalPolynomial_eq_dLaurentPointCharacters_sum,
      evalPolynomial_eq_dLaurentPointCharacters_sum]
    apply Finsupp.sum_congr
    intro z hz
    congr 1
    let s : S := ⟨i, ⟨z, hz⟩⟩
    let j : Fin m := e.symm s
    have hj := congrArg (fun q => dPointEquiv m q j) hxy
    rw [dCharacterTupleMorphism_apply,
      dCharacterTupleMorphism_apply] at hj
    have hjval := congrArg Units.val hj
    have hes : (e (e.symm s)).2.1 = z := by
      have heq := congrArg (fun q : S => q.2.1) (e.apply_symm_apply s)
      simpa [s] using heq
    change (↑(∏ q, (dPointEquiv n x q) ^
        (e (e.symm s)).2.1 q) : k) =
      (↑(∏ q, (dPointEquiv n y q) ^
        (e (e.symm s)).2.1 q) : k) at hjval
    rw [hes] at hjval
    exact hjval
  have hrecover (j : Fin m) :
      ∃ q : MvPolynomial H.Coordinates k,
        ∀ x : Variety.Point (dVariety k n),
          evalPolynomial (f.onPoints x).val q =
            dLaurentPointCharacter n (zTuple j) x := by
    let s : S := e j
    exact exists_target_polynomial_eq_dLaurentPointCharacter_of_mem_support
      n f s.1 (p s.1) (hp s.1) s.2.2
  let qPos : Fin m → MvPolynomial H.Coordinates k :=
    fun j => Classical.choose (hrecover j)
  have hqPos (j : Fin m) (x : Variety.Point (dVariety k n)) :
      evalPolynomial (f.onPoints x).val (qPos j) =
        dLaurentPointCharacter n (zTuple j) x :=
    Classical.choose_spec (hrecover j) x
  have hfχ {x y : Variety.Point (dVariety k n)}
      (hxy : f.onPoints x = f.onPoints y) :
      χ.onPoints x = χ.onPoints y := by
    apply (dPointEquiv m).injective
    funext j
    rw [dCharacterTupleMorphism_apply,
      dCharacterTupleMorphism_apply]
    apply Units.ext
    change dLaurentPointCharacter n (zTuple j) x =
      dLaurentPointCharacter n (zTuple j) y
    calc
      dLaurentPointCharacter n (zTuple j) x =
          evalPolynomial (f.onPoints x).val (qPos j) := (hqPos j x).symm
      _ = evalPolynomial (f.onPoints y).val (qPos j) := by rw [hxy]
      _ = dLaurentPointCharacter n (zTuple j) y := hqPos j y
  let Iχ := χ.imageClosedSubgroup
  let If := f.imageClosedSubgroup
  letI : AlgebraicGroup Iχ.carrierVariety := Iχ.carrierAlgebraicGroup
  letI : AlgebraicGroup If.carrierVariety := If.carrierAlgebraicGroup
  have hIχset :
      (Iχ : Set (Variety.Point (dVariety k m))) = Set.range χ.onPoints :=
    χ.imageClosedSubgroup_carrier.trans χ.image_carrier
  have hIfset : (If : Set (Variety.Point H)) = Set.range f.onPoints :=
    f.imageClosedSubgroup_carrier.trans f.image_carrier
  have hIχpre (y : Variety.Point Iχ.carrierVariety) :
      ∃ x : Variety.Point (dVariety k n),
        χ.onPoints x = Iχ.inclusion.onPoints y := by
    have hy : Iχ.inclusion.onPoints y ∈
        (Iχ : Set (Variety.Point (dVariety k m))) :=
      (Iχ.pointEquiv y).property
    rw [hIχset] at hy
    rcases hy with ⟨x, hx⟩
    exact ⟨x, hx⟩
  let preχ (y : Variety.Point Iχ.carrierVariety) :
      Variety.Point (dVariety k n) := Classical.choose (hIχpre y)
  have hpreχ (y : Variety.Point Iχ.carrierVariety) :
      χ.onPoints (preχ y) = Iχ.inclusion.onPoints y :=
    Classical.choose_spec (hIχpre y)
  have hIfpre (y : Variety.Point If.carrierVariety) :
      ∃ x : Variety.Point (dVariety k n),
        f.onPoints x = If.inclusion.onPoints y := by
    have hy : If.inclusion.onPoints y ∈
        (If : Set (Variety.Point H)) :=
      (If.pointEquiv y).property
    rw [hIfset] at hy
    rcases hy with ⟨x, hx⟩
    exact ⟨x, hx⟩
  let preF (y : Variety.Point If.carrierVariety) :
      Variety.Point (dVariety k n) := Classical.choose (hIfpre y)
  have hpreF (y : Variety.Point If.carrierVariety) :
      f.onPoints (preF y) = If.inclusion.onPoints y :=
    Classical.choose_spec (hIfpre y)
  let aPoly (i : H.Coordinates) :
      MvPolynomial Iχ.carrierVariety.Coordinates k :=
    ∑ s : (dLaurentCoefficients n (p i)).support,
      MvPolynomial.C (dLaurentCoefficients n (p i) s.1) *
        MvPolynomial.X (Sum.inl (ULift.up (e.symm ⟨i, s⟩)))
  have hχcoordinate (x : Variety.Point (dVariety k n)) (j : Fin m) :
      (χ.onPoints x).val (Sum.inl (ULift.up j)) =
        dLaurentPointCharacter n (zTuple j) x := by
    change ((dPointEquiv m (χ.onPoints x) j : k)) = _
    rw [dCharacterTupleMorphism_apply]
    rfl
  have haRegular (i : H.Coordinates) :
      ∃ q : MvPolynomial Iχ.carrierVariety.Coordinates k,
        ∀ y : Variety.Point Iχ.carrierVariety,
          (f.onPoints (preχ y)).val i = evalPolynomial y.val q := by
    refine ⟨aPoly i, ?_⟩
    intro y
    rw [hp i (preχ y), evalPolynomial_eq_dLaurentPointCharacters_sum]
    rw [Finsupp.sum]
    conv_lhs => rw [← Finset.sum_attach]
    simp only [aPoly, evalPolynomial_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [evalPolynomial_mul]
    simp [evalPolynomial]
    have hcoord := congrArg
      (fun q => q.val (Sum.inl (ULift.up (e.symm ⟨i, s⟩))))
      (hpreχ y)
    have hincval : (Iχ.inclusion.onPoints y).val = y.val :=
      Iχ.pointEquiv_val y
    rw [hincval] at hcoord
    have hzTuple : zTuple (e.symm ⟨i, s⟩) = s.1 := by
      change (e (e.symm ⟨i, s⟩)).2.1 = s.1
      rw [e.apply_symm_apply]
    have hsource := hχcoordinate (preχ y) (e.symm ⟨i, s⟩)
    rw [hzTuple] at hsource
    have hval : dLaurentPointCharacter n s.1 (preχ y) =
        y.val (Sum.inl (ULift.up (e.symm ⟨i, s⟩))) :=
      hsource.symm.trans hcoord
    exact Or.inl hval
  let aAmb : AlgebraicGroup.Morphism Iχ.carrierVariety H :=
    { toVariety :=
        { toFun := fun y => f.onPoints (preχ y)
          regular := haRegular }
      map_one := by
        have hχone : χ.onPoints (preχ 1) = χ.onPoints 1 := by
          calc
            χ.onPoints (preχ 1) = Iχ.inclusion.onPoints 1 := hpreχ 1
            _ = 1 := Iχ.inclusion.map_one
            _ = χ.onPoints 1 := χ.map_one.symm
        calc
          f.onPoints (preχ 1) = f.onPoints 1 := hχf hχone
          _ = 1 := f.map_one
      map_mul := by
        intro x y
        have hχmul : χ.onPoints (preχ (x * y)) =
            χ.onPoints (preχ x * preχ y) := by
          calc
            χ.onPoints (preχ (x * y)) =
                Iχ.inclusion.onPoints (x * y) := hpreχ _
            _ = Iχ.inclusion.onPoints x * Iχ.inclusion.onPoints y :=
              Iχ.inclusion.map_mul x y
            _ = χ.onPoints (preχ x) * χ.onPoints (preχ y) := by
              rw [hpreχ x, hpreχ y]
            _ = χ.onPoints (preχ x * preχ y) := (χ.map_mul _ _).symm
        calc
          f.onPoints (preχ (x * y)) =
              f.onPoints (preχ x * preχ y) := hχf hχmul
          _ = f.onPoints (preχ x) * f.onPoints (preχ y) := f.map_mul _ _ }
  have haIf (y : Variety.Point Iχ.carrierVariety) :
      aAmb.onPoints y ∈ (If : Set (Variety.Point H)) := by
    rw [hIfset]
    exact ⟨preχ y, rfl⟩
  let aI : AlgebraicGroup.Morphism Iχ.carrierVariety If.carrierVariety :=
    aAmb.codRestrictClosedSubgroup If haIf
  let invPoly : H.Coordinates → MvPolynomial H.Coordinates k :=
    fun i => (inferInstance : AlgebraicGroup H).invPolynomial i
  let qNeg (j : Fin m) : MvPolynomial H.Coordinates k :=
    MvPolynomial.bind₁ invPoly (qPos j)
  have hqNeg (j : Fin m) (y : Variety.Point H) :
      evalPolynomial y.val (qNeg j) =
        evalPolynomial y⁻¹.val (qPos j) := by
    change evalPolynomial y.val (MvPolynomial.bind₁ invPoly (qPos j)) = _
    rw [evalPolynomial_bind₁]
    congr 1
    funext i
    exact ((inferInstance : AlgebraicGroup H).inv_regular i y).symm
  have hχnegative (x : Variety.Point (dVariety k n)) (j : Fin m) :
      (χ.onPoints x).val (Sum.inr (ULift.up j)) =
        (χ.onPoints x⁻¹).val (Sum.inl (ULift.up j)) := by
    have hinv := χ.map_inv x
    have hcoord := congrArg
      (fun q => q.val (Sum.inl (ULift.up j))) hinv
    exact hcoord.symm
  have hbRegular (c : Iχ.carrierVariety.Coordinates) :
      ∃ q : MvPolynomial If.carrierVariety.Coordinates k,
        ∀ y : Variety.Point If.carrierVariety,
          (χ.onPoints (preF y)).val c = evalPolynomial y.val q := by
    cases c with
    | inl u =>
        cases u with
        | up j =>
            refine ⟨qPos j, ?_⟩
            intro y
            calc
              (χ.onPoints (preF y)).val (Sum.inl (ULift.up j)) =
                  dLaurentPointCharacter n (zTuple j) (preF y) :=
                hχcoordinate (preF y) j
              _ = evalPolynomial (f.onPoints (preF y)).val (qPos j) :=
                (hqPos j (preF y)).symm
              _ = evalPolynomial y.val (qPos j) := by
                rw [hpreF]
                rw [show (If.inclusion.onPoints y).val = y.val from
                  If.pointEquiv_val y]
    | inr u =>
        cases u with
        | up j =>
            refine ⟨qNeg j, ?_⟩
            intro y
            calc
              (χ.onPoints (preF y)).val (Sum.inr (ULift.up j)) =
                  (χ.onPoints (preF y)⁻¹).val
                    (Sum.inl (ULift.up j)) := hχnegative (preF y) j
              _ = dLaurentPointCharacter n (zTuple j) (preF y)⁻¹ :=
                hχcoordinate (preF y)⁻¹ j
              _ = evalPolynomial (f.onPoints (preF y)⁻¹).val (qPos j) :=
                (hqPos j (preF y)⁻¹).symm
              _ = evalPolynomial (f.onPoints (preF y))⁻¹.val (qPos j) := by
                rw [f.map_inv]
              _ = evalPolynomial (f.onPoints (preF y)).val (qNeg j) :=
                (hqNeg j (f.onPoints (preF y))).symm
              _ = evalPolynomial y.val (qNeg j) := by
                rw [hpreF]
                rw [show (If.inclusion.onPoints y).val = y.val from
                  If.pointEquiv_val y]
  let bAmb : AlgebraicGroup.Morphism If.carrierVariety (dVariety k m) :=
    { toVariety :=
        { toFun := fun y => χ.onPoints (preF y)
          regular := hbRegular }
      map_one := by
        have hfone : f.onPoints (preF 1) = f.onPoints 1 := by
          calc
            f.onPoints (preF 1) = If.inclusion.onPoints 1 := hpreF 1
            _ = 1 := If.inclusion.map_one
            _ = f.onPoints 1 := f.map_one.symm
        calc
          χ.onPoints (preF 1) = χ.onPoints 1 := hfχ hfone
          _ = 1 := χ.map_one
      map_mul := by
        intro x y
        have hfmul : f.onPoints (preF (x * y)) =
            f.onPoints (preF x * preF y) := by
          calc
            f.onPoints (preF (x * y)) =
                If.inclusion.onPoints (x * y) := hpreF _
            _ = If.inclusion.onPoints x * If.inclusion.onPoints y :=
              If.inclusion.map_mul x y
            _ = f.onPoints (preF x) * f.onPoints (preF y) := by
              rw [hpreF x, hpreF y]
            _ = f.onPoints (preF x * preF y) := (f.map_mul _ _).symm
        calc
          χ.onPoints (preF (x * y)) =
              χ.onPoints (preF x * preF y) := hfχ hfmul
          _ = χ.onPoints (preF x) * χ.onPoints (preF y) := χ.map_mul _ _ }
  have hbIχ (y : Variety.Point If.carrierVariety) :
      bAmb.onPoints y ∈ (Iχ : Set (Variety.Point (dVariety k m))) := by
    rw [hIχset]
    exact ⟨preF y, rfl⟩
  let bI : AlgebraicGroup.Morphism If.carrierVariety Iχ.carrierVariety :=
    bAmb.codRestrictClosedSubgroup Iχ hbIχ
  let imageIso : AlgebraicGroup.Iso Iχ.carrierVariety If.carrierVariety :=
    { hom := aI
      inv := bI
      hom_inv_id := by
        intro y
        apply Iχ.inclusion_injective
        rw [bAmb.codRestrictClosedSubgroup_inclusion_apply Iχ hbIχ]
        change χ.onPoints (preF (aI.onPoints y)) = Iχ.inclusion.onPoints y
        have hfa : f.onPoints (preF (aI.onPoints y)) =
            f.onPoints (preχ y) := by
          calc
            f.onPoints (preF (aI.onPoints y)) =
                If.inclusion.onPoints (aI.onPoints y) := hpreF _
            _ = aAmb.onPoints y :=
              aAmb.codRestrictClosedSubgroup_inclusion_apply If haIf y
            _ = f.onPoints (preχ y) := rfl
        calc
          χ.onPoints (preF (aI.onPoints y)) =
              χ.onPoints (preχ y) := hfχ hfa
          _ = Iχ.inclusion.onPoints y := hpreχ y
      inv_hom_id := by
        intro y
        apply If.inclusion_injective
        rw [aAmb.codRestrictClosedSubgroup_inclusion_apply If haIf]
        change f.onPoints (preχ (bI.onPoints y)) = If.inclusion.onPoints y
        have hχb : χ.onPoints (preχ (bI.onPoints y)) =
            χ.onPoints (preF y) := by
          calc
            χ.onPoints (preχ (bI.onPoints y)) =
                Iχ.inclusion.onPoints (bI.onPoints y) := hpreχ _
            _ = bAmb.onPoints y :=
              bAmb.codRestrictClosedSubgroup_inclusion_apply Iχ hbIχ y
            _ = χ.onPoints (preF y) := rfl
        calc
          f.onPoints (preχ (bI.onPoints y)) =
              f.onPoints (preF y) := hχf hχb
          _ = If.inclusion.onPoints y := hpreF y }
  have hχT : @IsTorus k _ Iχ.carrierVariety Iχ.carrierAlgebraicGroup :=
    dCharacterTupleMorphism_image_isTorus m n zTuple
  obtain ⟨r, ⟨torusIso⟩⟩ := hχT
  exact ⟨r, ⟨imageIso.comp torusIso⟩⟩

/-- The image of a torus under an algebraic-group morphism is a torus.

This is GLS3, Proposition 1.4.2(d). -/
public theorem morphism_image_isTorus
    {T H : Variety k} [AlgebraicGroup T] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism T H) (hT : IsTorus T) :
    let I := f.imageClosedSubgroup
    @IsTorus k _ I.carrierVariety I.carrierAlgebraicGroup := by
  obtain ⟨n, ⟨e⟩⟩ := hT
  let g := f.comp e.hom
  have hRange : Set.range g.onPoints = Set.range f.onPoints := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.hom.onPoints x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨e.inv.onPoints x, ?_⟩
      change f.onPoints (e.hom.onPoints (e.inv.onPoints x)) = f.onPoints x
      rw [e.inv_hom_id]
  have hImage : g.imageClosedSubgroup = f.imageClosedSubgroup := by
    apply SetLike.coe_injective
    calc
      (g.imageClosedSubgroup : Set (Variety.Point H)) = Set.range g.onPoints :=
        g.imageClosedSubgroup_carrier.trans g.image_carrier
      _ = Set.range f.onPoints := hRange
      _ = (f.imageClosedSubgroup : Set (Variety.Point H)) :=
        (f.imageClosedSubgroup_carrier.trans f.image_carrier).symm
  have hgT := dMorphism_imageClosedSubgroup_isTorus n g
  rw [hImage] at hgT
  exact hgT

end Theory.AlgebraicGroup
