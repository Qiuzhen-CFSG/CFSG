module

public import Theory.AlgebraicGroup.Tori.Character.Operations

universe u

/-! Character-lattice and point duality for algebraic tori.

The standard diagonal torus has character lattice `ℤ^n`; its points are recovered
by evaluating all Laurent characters.  For an arbitrary torus, the canonical
evaluation homomorphism sends a point `t` to `χ ↦ χ(t)`.  Choosing an isomorphism
with a diagonal torus transports the proved coordinate evaluation bijection and
shows that this canonical map is bijective.  Thus the resulting duality does not
depend on the chosen diagonal coordinates.
-/

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The character group of `D_n`, written additively, is the integral lattice
`ℤ^n`. -/
@[expose]
public noncomputable def dLaurentCharacterAddEquiv [IsAlgClosed k] (n : ℕ) :
    (Fin n → ℤ) ≃+ Additive (TorusCharacter (dVariety k n)) :=
  AddEquiv.ofBijective (dLaurentCharacterHom (k := k) n)
    ⟨dLaurentCharacter_injective n, dLaurentCharacter_surjective n⟩

/-- The standard coordinate characters form a basis of the character lattice
of `D_n`. -/
public theorem dVariety_character_basis [IsAlgClosed k] (n : ℕ) :
    Nonempty
      (Module.Basis (Fin n) ℤ
        (Additive (TorusCharacter (dVariety k n)))) := by
  let e : (Fin n → ℤ) ≃ₗ[ℤ]
      Additive (TorusCharacter (dVariety k n)) :=
    (dLaurentCharacterAddEquiv (k := k) n).toIntLinearEquiv
  exact ⟨(Pi.basisFun ℤ (Fin n)).map e⟩

/-- An isomorphism `D_n ≃ T` transports the standard character-lattice basis
to `T`. -/
public theorem torus_character_basis_of_iso [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (n : ℕ) (e : AlgebraicGroup.Iso (dVariety k n) T) :
    Nonempty (Module.Basis (Fin n) ℤ (Additive (TorusCharacter T))) := by
  obtain ⟨b⟩ := dVariety_character_basis (k := k) n
  have eC : TorusCharacter (dVariety k n) ≃* TorusCharacter T :=
    torusCharacter_iso_equiv e
  let : CommGroup (TorusCharacter (dVariety k n)) :=
    torusCharacterCommGroup (dVariety k n)
  let : CommGroup (TorusCharacter T) := torusCharacterCommGroup T
  have eL : Additive (TorusCharacter (dVariety k n)) ≃ₗ[ℤ]
      Additive (TorusCharacter T) :=
    eC.toAdditive.toIntLinearEquiv
  exact ⟨b.map eL⟩

/-- The character lattice of `D_n` is finitely generated. -/
public theorem dVariety_character_fg [IsAlgClosed k] (n : ℕ) :
    Module.Finite ℤ (Additive (TorusCharacter (dVariety k n))) := by
  obtain ⟨b⟩ := dVariety_character_basis (k := k) n
  exact Module.Finite.of_basis b

/-- The character lattice of `D_n` has rank `n`. -/
public theorem dVariety_character_finrank [IsAlgClosed k] (n : ℕ) :
    Module.finrank ℤ (Additive (TorusCharacter (dVariety k n))) = n := by
  obtain ⟨b⟩ := dVariety_character_basis (k := k) n
  simpa using Module.finrank_eq_card_basis b

/-- The character lattice of `D_n` is free. -/
public theorem dVariety_character_free [IsAlgClosed k] (n : ℕ) :
    Module.Free ℤ (Additive (TorusCharacter (dVariety k n))) := by
  obtain ⟨b⟩ := dVariety_character_basis (k := k) n
  exact Module.Free.of_basis b

/-- If `T ≃ D_n`, its character lattice is finitely generated. -/
public theorem torus_character_fg_of_iso [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (n : ℕ) (e : AlgebraicGroup.Iso (dVariety k n) T) :
    Module.Finite ℤ (Additive (TorusCharacter T)) := by
  obtain ⟨b⟩ := torus_character_basis_of_iso (k := k) n e
  exact Module.Finite.of_basis b

/-- If `T ≃ D_n`, its character lattice has rank `n`. -/
public theorem torus_character_finrank_of_iso [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (n : ℕ) (e : AlgebraicGroup.Iso (dVariety k n) T) :
    Module.finrank ℤ (Additive (TorusCharacter T)) = n := by
  obtain ⟨b⟩ := torus_character_basis_of_iso (k := k) n e
  simpa using Module.finrank_eq_card_basis b

/-- If `T ≃ D_n`, its character lattice is free. -/
public theorem torus_character_free_of_iso [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (n : ℕ) (e : AlgebraicGroup.Iso (dVariety k n) T) :
    Module.Free ℤ (Additive (TorusCharacter T)) := by
  obtain ⟨b⟩ := torus_character_basis_of_iso (k := k) n e
  exact Module.Free.of_basis b

/-- Canonical evaluation of every algebraic character at a point. -/
@[expose]
public noncomputable def torusPointEval
    (T : Variety k) [AlgebraicGroup T] :
    Variety.Point T →* (TorusCharacter T →* kˣ) where
  toFun := fun x =>
    { toFun := fun χ => dPointEquiv 1 (χ.onPoints x) 0
      map_one' := by
        change dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 = 1
        rw [dPointEquiv_one]
        rfl
      map_mul' := by
        intro χ ψ
        change dPointEquiv 1 (χ.onPoints x * ψ.onPoints x) 0 =
          dPointEquiv 1 (χ.onPoints x) 0 * dPointEquiv 1 (ψ.onPoints x) 0
        exact congrFun
          (dPointEquiv_mul 1 (χ.onPoints x) (ψ.onPoints x)) 0 }
  map_one' := by
    ext χ
    simp [dPointEquiv_one]
  map_mul' := by
    intro x y
    ext χ
    simp [dPointEquiv_mul]

/-- Canonical point evaluation has the expected value on each character. -/
public lemma torusPointEval_apply
    {T : Variety k} [AlgebraicGroup T]
    (x : Variety.Point T) (χ : TorusCharacter T) :
    torusPointEval T x χ = dPointEquiv 1 (χ.onPoints x) 0 :=
  rfl

private lemma dVarietyPointEval_apply (n : ℕ)
    (x : Variety.Point (dVariety k n))
    (f : TorusCharacter (dVariety k n)) :
    (dVarietyPointEval (k := k) n x) f =
      dPointEquiv 1 (f.onPoints x) 0 :=
  rfl

private lemma dVarietyPointEval_bijective [IsAlgClosed k] (n : ℕ) :
    Function.Bijective (dVarietyPointEval (k := k) n) := by
  constructor
  · intro x y hxy
    apply (dPointEquiv n).injective
    funext i
    have hx := congrArg
      (fun f : TorusCharacter (dVariety k n) →* kˣ =>
        f (dLaurentCharacter (k := k) n (Pi.single i 1))) hxy
    rw [dVarietyPointEval_apply n x, dVarietyPointEval_apply n y] at hx
    rw [dLaurentCharacter_single] at hx
    rw [dCoordinateCharacter_apply n i x,
      dCoordinateCharacter_apply n i y] at hx
    exact hx
  · intro φ
    let invFun :
        (TorusCharacter (dVariety k n) →* kˣ) →
          Variety.Point (dVariety k n) :=
      fun ψ => (dPointEquiv n).symm
        (fun i => ψ (dLaurentCharacter (k := k) n (Pi.single i 1)))
    refine ⟨invFun φ, ?_⟩
    ext χ
    obtain ⟨z, hz⟩ := dLaurentCharacter_surjective (k := k) n χ
    rw [← hz]
    rw [dVarietyPointEval_apply n (invFun φ)
      (dLaurentCharacter (k := k) n z)]
    rw [dLaurentCharacter_apply (k := k) n z (invFun φ)]
    simp [invFun]
    rw [dLaurentCharacter_expand (k := k) n z]
    simp [map_prod, map_zpow]

/-- For a torus over an algebraically closed field, points are determined by,
and realize, all multiplicative character evaluations. -/
public theorem torusPointEval_bijective [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) :
    Function.Bijective (torusPointEval T) := by
  obtain ⟨n, ⟨e⟩⟩ := hT
  have hd := dVarietyPointEval_bijective (k := k) n
  constructor
  · intro x y hxy
    have he : dVarietyPointEval n (e.inv.onPoints x) =
        dVarietyPointEval n (e.inv.onPoints y) := by
      ext χ
      have h := DFunLike.congr_fun hxy (TorusCharacter.pullback e.inv χ)
      change dPointEquiv 1 (χ.onPoints (e.inv.onPoints x)) 0 =
        dPointEquiv 1 (χ.onPoints (e.inv.onPoints y)) 0 at h
      exact congrArg Units.val h
    have hinv := hd.injective he
    calc
      x = e.hom.onPoints (e.inv.onPoints x) := (e.inv_hom_id x).symm
      _ = e.hom.onPoints (e.inv.onPoints y) := congrArg e.hom.onPoints hinv
      _ = y := e.inv_hom_id y
  · intro φ
    let φd : TorusCharacter (dVariety k n) →* kˣ :=
      φ.comp (TorusCharacter.pullback e.inv)
    obtain ⟨x, hx⟩ := hd.surjective φd
    refine ⟨e.hom.onPoints x, ?_⟩
    ext χ
    have h := DFunLike.congr_fun hx (TorusCharacter.pullback e.hom χ)
    rw [torusPointEval_apply]
    apply congrArg Units.val
    calc
      dPointEquiv 1 (χ.onPoints (e.hom.onPoints x)) 0 =
          dVarietyPointEval n x (TorusCharacter.pullback e.hom χ) := rfl
      _ = φ (TorusCharacter.pullback e.inv
            (TorusCharacter.pullback e.hom χ)) := h
      _ = φ χ := by
        congr 1
        apply AlgebraicGroup.Morphism.ext
        funext t
        change χ.onPoints (e.hom.onPoints (e.inv.onPoints t)) = χ.onPoints t
        rw [e.inv_hom_id]

/-- Points of `D_n` correspond exactly to multiplicative characters of its
character group, via evaluation. -/
public theorem dVariety_character_duality [IsAlgClosed k] (n : ℕ) :
    Nonempty
      (Variety.Point (dVariety k n) ≃*
        (TorusCharacter (dVariety k n) →* kˣ)) :=
  ⟨MulEquiv.ofBijective (dVarietyPointEval (k := k) n)
    (dVarietyPointEval_bijective (k := k) n)⟩

/-- A torus is the multiplicative dual of its character lattice. -/
public theorem torus_character_duality [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (hT : IsTorus T) :
    Nonempty (Variety.Point T ≃* (TorusCharacter T →* kˣ)) :=
  ⟨MulEquiv.ofBijective (torusPointEval T)
    (torusPointEval_bijective hT)⟩

end Theory.AlgebraicGroup
