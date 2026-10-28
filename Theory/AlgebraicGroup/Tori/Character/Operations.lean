module

public import Theory.AlgebraicGroup.Tori.Character.Classification
public import Theory.AlgebraicGroup.Tori.Power

universe u

/-! Pullback and isomorphism operations on algebraic-group characters. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Pullback of algebraic characters along an algebraic-group morphism. -/
@[expose]
public noncomputable def TorusCharacter.pullback
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) :
    TorusCharacter H →* TorusCharacter G where
  toFun := fun χ => χ.comp f
  map_one' := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    rfl
  map_mul' := by
    intro χ ψ
    apply AlgebraicGroup.Morphism.ext
    funext x
    rfl

/-- Pullback commutes with the scalar polynomial function attached to a
character. -/
public lemma TorusCharacter.pullback_scalarPolynomialFunction
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (χ : TorusCharacter H) :
    f.toVariety.pullbackAlgHom χ.scalarPolynomialFunction =
      (TorusCharacter.pullback f χ).scalarPolynomialFunction := by
  apply Variety.PolynomialFunction.ext
  intro x
  change χ.scalarPolynomialFunction (f.onPoints x) =
    (TorusCharacter.pullback f χ).scalarPolynomialFunction x
  rw [TorusCharacter.scalarPolynomialFunction_apply,
    TorusCharacter.scalarPolynomialFunction_apply]
  rfl

/-- An isomorphism of algebraic groups induces an equivalence of character
groups by pullback. -/
public noncomputable def torusCharacter_iso_equiv
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (e : AlgebraicGroup.Iso G H) : TorusCharacter G ≃* TorusCharacter H where
  toFun := TorusCharacter.pullback e.inv
  invFun := TorusCharacter.pullback e.hom
  left_inv χ := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    change χ.onPoints (e.inv.onPoints (e.hom.onPoints x)) = χ.onPoints x
    rw [e.hom_inv_id]
  right_inv ψ := by
    apply AlgebraicGroup.Morphism.ext
    funext y
    change ψ.onPoints (e.hom.onPoints (e.inv.onPoints y)) = ψ.onPoints y
    rw [e.inv_hom_id]
  map_mul' := (TorusCharacter.pullback e.inv).map_mul

/-- Character pullback is contravariant. -/
public lemma torusCharacter_pullback_comp
    {G H I : Variety k}
    [AlgebraicGroup G] [AlgebraicGroup H] [AlgebraicGroup I]
    (f : AlgebraicGroup.Morphism G H) (g : AlgebraicGroup.Morphism H I) :
    TorusCharacter.pullback (g.comp f) =
      TorusCharacter.pullback f ∘ TorusCharacter.pullback g := by
  ext χ
  apply AlgebraicGroup.Morphism.ext
  funext x
  rfl

/-- Pullback along the identity morphism is the identity on characters. -/
public lemma torusCharacter_pullback_id
    (G : Variety k) [AlgebraicGroup G] :
    TorusCharacter.pullback (AlgebraicGroup.Morphism.id G) = MonoidHom.id _ := by
  ext χ
  apply AlgebraicGroup.Morphism.ext
  funext x
  rfl

/-- A nontrivial character of a torus takes every nonzero scalar value. -/
public theorem TorusCharacter.exists_pointCharacter_eq_of_ne_one
    [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) (χ : TorusCharacter T) (hχ : χ ≠ 1) :
    ∀ c : k, c ≠ 0 → ∃ t, χ.pointCharacter t = c := by
  classical
  intro c hc
  obtain ⟨n, ⟨e⟩⟩ := hT
  let χd : TorusCharacter (dVariety k n) := TorusCharacter.pullback e.hom χ
  have hχd : χd ≠ 1 := by
    intro h
    apply hχ
    apply AlgebraicGroup.Morphism.ext
    funext t
    have ht := congrArg (fun f : TorusCharacter (dVariety k n) =>
      f.onPoints (e.inv.onPoints t)) h
    change χ.onPoints (e.hom.onPoints (e.inv.onPoints t)) =
      (1 : TorusCharacter (dVariety k n)).onPoints (e.inv.onPoints t) at ht
    rw [e.inv_hom_id] at ht
    change χ.toVariety.toFun t = (1 : TorusCharacter T).toVariety.toFun t
    calc
      χ.toVariety.toFun t = χ.onPoints t := rfl
      _ = (1 : TorusCharacter (dVariety k n)).onPoints
          (e.inv.onPoints t) := ht
      _ = 1 := rfl
      _ = (1 : TorusCharacter T).toVariety.toFun t := rfl
  obtain ⟨z, hzχ⟩ := dLaurentCharacter_surjective (k := k) n χd
  have hz : z ≠ 0 := by
    intro hz
    apply hχd
    rw [← hzχ, hz]
    simp [dLaurentCharacter]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨a, ha⟩ :=
    units_zpow_surjective_of_isAlgClosed (k := k) (z i) hi (Units.mk0 c hc)
  let u : Fin n → kˣ := Function.update (fun _ => 1) i a
  let x : Variety.Point (dVariety k n) := (dPointEquiv n).symm u
  refine ⟨e.hom.onPoints x, ?_⟩
  have hprod : (∏ j, u j ^ z j) = a ^ z i := by
    rw [Finset.prod_eq_single i]
    · simp [u]
    · intro j hj hji
      simp [u, hji]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  have hvalue : dLaurentPointCharacter (k := k) n z x = c := by
    change ((↑(∏ j, (dPointEquiv n x j) ^ z j) : k)) = c
    rw [show dPointEquiv n x = u by simp [x]]
    rw [hprod]
    simpa using congrArg Units.val ha
  change χd.pointCharacter x = c
  rw [← hzχ, TorusCharacter.pointCharacter_dLaurentCharacter]
  exact hvalue

end Theory.AlgebraicGroup
