module

public import Theory.AlgebraicGroup.Tori.Basic

universe u

/-! Splitting a standard diagonal torus into one fewer coordinates and one
copy of the multiplicative group. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private def splitDVarietyPoint (n : ℕ)
    (x : Variety.Point (dVariety k (n + 1))) :
    Variety.Point (Variety.prod (dVariety k n) (KMult k)) :=
  (Variety.prodPointEquiv (dVariety k n) (KMult k)).symm
    (⟨Sum.elim
        (fun p : ULift (Fin n) ↦ x.val (Sum.inl (ULift.up p.down.castSucc)))
        (fun p : ULift (Fin n) ↦ x.val (Sum.inr (ULift.up p.down.castSucc))), by
      intro p hp
      rcases hp with ⟨i, rfl⟩
      simpa [evalPolynomial] using x.isZero
        (MvPolynomial.X (Sum.inl (ULift.up i.castSucc)) *
          MvPolynomial.X (Sum.inr (ULift.up i.castSucc)) - 1)
        (Set.mem_ofPred.mpr ⟨i.castSucc, rfl⟩)⟩,
    ⟨Sum.elim
        (fun _ : ULift (Fin 1) ↦ x.val (Sum.inl (ULift.up (Fin.last n))))
        (fun _ : ULift (Fin 1) ↦ x.val (Sum.inr (ULift.up (Fin.last n)))), by
      intro p hp
      rcases hp with ⟨i, rfl⟩
      simpa [evalPolynomial] using x.isZero
        (MvPolynomial.X (Sum.inl (ULift.up (Fin.last n))) *
          MvPolynomial.X (Sum.inr (ULift.up (Fin.last n))) - 1)
        (Set.mem_ofPred.mpr ⟨Fin.last n, rfl⟩)⟩)

private def mergeDVarietyPoint (n : ℕ)
    (z : Variety.Point (Variety.prod (dVariety k n) (KMult k))) :
    Variety.Point (dVariety k (n + 1)) := by
  let xy := Variety.prodPointEquiv (dVariety k n) (KMult k) z
  exact ⟨Sum.elim
      (fun p : ULift (Fin (n + 1)) ↦
        Fin.lastCases
          (xy.2.val (Sum.inl (ULift.up (0 : Fin 1))))
          (fun i ↦ xy.1.val (Sum.inl (ULift.up i))) p.down)
      (fun p : ULift (Fin (n + 1)) ↦
        Fin.lastCases
          (xy.2.val (Sum.inr (ULift.up (0 : Fin 1))))
          (fun i ↦ xy.1.val (Sum.inr (ULift.up i))) p.down), by
    intro p hp
    rcases hp with ⟨i, rfl⟩
    cases i using Fin.lastCases with
    | last =>
        simpa [evalPolynomial, xy] using xy.2.isZero
          (MvPolynomial.X (Sum.inl (ULift.up (0 : Fin 1))) *
            MvPolynomial.X (Sum.inr (ULift.up (0 : Fin 1))) - 1)
          (Set.mem_ofPred.mpr ⟨0, rfl⟩)
    | cast i =>
        simpa [evalPolynomial, xy] using xy.1.isZero
          (MvPolynomial.X (Sum.inl (ULift.up i)) *
            MvPolynomial.X (Sum.inr (ULift.up i)) - 1)
          (Set.mem_ofPred.mpr ⟨i, rfl⟩)⟩

private def splitDVarietyMorphism (n : ℕ) :
    Variety.Morphism (dVariety k (n + 1))
      (Variety.prod (dVariety k n) (KMult k)) where
  toFun := splitDVarietyPoint n
  regular := by
    intro c
    cases c with
    | inl c =>
        cases c with
        | inl p =>
            exact ⟨MvPolynomial.X (Sum.inl (ULift.up p.down.castSucc)), by
              intro x
              simp [splitDVarietyPoint, Variety.prodPointEquiv,
                evalPolynomial]⟩
        | inr p =>
            exact ⟨MvPolynomial.X (Sum.inr (ULift.up p.down.castSucc)), by
              intro x
              simp [splitDVarietyPoint, Variety.prodPointEquiv,
                evalPolynomial]⟩
    | inr c =>
        cases c with
        | inl p =>
            exact ⟨MvPolynomial.X (Sum.inl (ULift.up (Fin.last n))), by
              intro x
              simp [splitDVarietyPoint, Variety.prodPointEquiv,
                evalPolynomial]⟩
        | inr p =>
            exact ⟨MvPolynomial.X (Sum.inr (ULift.up (Fin.last n))), by
              intro x
              simp [splitDVarietyPoint, Variety.prodPointEquiv,
                evalPolynomial]⟩

private def mergeDVarietyMorphism (n : ℕ) :
    Variety.Morphism (Variety.prod (dVariety k n) (KMult k))
      (dVariety k (n + 1)) where
  toFun := mergeDVarietyPoint n
  regular := by
    intro c
    cases c with
    | inl p =>
        cases p with
        | up i =>
            cases i using Fin.lastCases with
            | last =>
                exact ⟨MvPolynomial.X
                    (Sum.inr (Sum.inl (ULift.up (0 : Fin 1)))), by
                  intro z
                  simp [mergeDVarietyPoint, Variety.prodPointEquiv,
                    evalPolynomial]⟩
            | cast i =>
                exact ⟨MvPolynomial.X
                    (Sum.inl (Sum.inl (ULift.up i))), by
                  intro z
                  simp [mergeDVarietyPoint, Variety.prodPointEquiv,
                    evalPolynomial]⟩
    | inr p =>
        cases p with
        | up i =>
            cases i using Fin.lastCases with
            | last =>
                exact ⟨MvPolynomial.X
                    (Sum.inr (Sum.inr (ULift.up (0 : Fin 1)))), by
                  intro z
                  simp [mergeDVarietyPoint, Variety.prodPointEquiv,
                    evalPolynomial]⟩
            | cast i =>
                exact ⟨MvPolynomial.X
                    (Sum.inl (Sum.inr (ULift.up i))), by
                  intro z
                  simp [mergeDVarietyPoint, Variety.prodPointEquiv,
                    evalPolynomial]⟩

private lemma split_merge (n : ℕ)
    (z : Variety.Point (Variety.prod (dVariety k n) (KMult k))) :
    splitDVarietyPoint n (mergeDVarietyPoint n z) = z := by
  apply (Variety.prodPointEquiv (dVariety k n) (KMult k)).injective
  apply Prod.ext
  · apply Variety.Point.ext
    funext c
    cases c <;>
      simp [mergeDVarietyPoint, splitDVarietyPoint,
        Variety.prodPointEquiv]
  · apply Variety.Point.ext
    funext c
    cases c with
    | inl p =>
        cases p with
        | up i =>
            have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
            subst i
            simp [mergeDVarietyPoint, splitDVarietyPoint,
              Variety.prodPointEquiv]
    | inr p =>
        cases p with
        | up i =>
            have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
            subst i
            simp [mergeDVarietyPoint, splitDVarietyPoint,
              Variety.prodPointEquiv]

private lemma merge_split (n : ℕ)
    (x : Variety.Point (dVariety k (n + 1))) :
    mergeDVarietyPoint n (splitDVarietyPoint n x) = x := by
  apply Variety.Point.ext
  funext c
  cases c with
  | inl p =>
      cases p with
      | up i =>
          cases i using Fin.lastCases <;>
            simp [mergeDVarietyPoint, splitDVarietyPoint,
              Variety.prodPointEquiv]
  | inr p =>
      cases p with
      | up i =>
          cases i using Fin.lastCases <;>
            simp [mergeDVarietyPoint, splitDVarietyPoint,
              Variety.prodPointEquiv]

private noncomputable def splitDAlgebraicMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (dVariety k (n + 1))
      (Variety.prod (dVariety k n) (KMult k)) := by
  let F := splitDVarietyMorphism (k := k) n
  have hmul : ∀ x y, F.toFun (x * y) = F.toFun x * F.toFun y := by
    intro x y
    apply (Variety.prodPointEquiv (dVariety k n) (KMult k)).injective
    rw [Variety.prodPointEquiv_mul]
    apply Prod.ext
    · apply (dPointEquiv n).injective
      funext i
      change dPointEquiv (n + 1) (x * y) i.castSucc =
        dPointEquiv (n + 1) x i.castSucc *
          dPointEquiv (n + 1) y i.castSucc
      exact congrFun (dPointEquiv_mul (n + 1) x y) i.castSucc
    · apply (dPointEquiv 1).injective
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      change dPointEquiv (n + 1) (x * y) (Fin.last n) =
        dPointEquiv (n + 1) x (Fin.last n) *
          dPointEquiv (n + 1) y (Fin.last n)
      exact congrFun (dPointEquiv_mul (n + 1) x y) (Fin.last n)
  have hone : F.toFun 1 = 1 := by
    have h := hmul 1 1
    have h' : F.toFun 1 * 1 = F.toFun 1 * F.toFun 1 := by
      simpa using h
    exact (mul_left_cancel h').symm
  exact
    { toVariety := F
      map_one := hone
      map_mul := hmul }

private noncomputable def mergeDAlgebraicMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (Variety.prod (dVariety k n) (KMult k))
      (dVariety k (n + 1)) := by
  let F := splitDAlgebraicMorphism (k := k) n
  let G := mergeDVarietyMorphism (k := k) n
  have hFinj : Function.Injective F.onPoints := by
    intro x y h
    change splitDVarietyPoint n x = splitDVarietyPoint n y at h
    rw [← merge_split (k := k) n x, ← merge_split (k := k) n y, h]
  have hmul : ∀ x y, G.toFun (x * y) = G.toFun x * G.toFun y := by
    intro x y
    apply hFinj
    change splitDVarietyPoint n (mergeDVarietyPoint n (x * y)) =
      splitDVarietyPoint n
        (mergeDVarietyPoint n x * mergeDVarietyPoint n y)
    rw [split_merge]
    change x * y = F.toVariety.toFun
      (mergeDVarietyPoint n x * mergeDVarietyPoint n y)
    rw [F.map_mul]
    change x * y = splitDVarietyPoint n (mergeDVarietyPoint n x) *
      splitDVarietyPoint n (mergeDVarietyPoint n y)
    rw [split_merge, split_merge]
  have hone : G.toFun 1 = 1 := by
    have h := hmul 1 1
    have h' : G.toFun 1 * 1 = G.toFun 1 * G.toFun 1 := by
      simpa using h
    exact (mul_left_cancel h').symm
  exact
    { toVariety := G
      map_one := hone
      map_mul := hmul }

private lemma dVarietySuccProdIso_nonempty (n : ℕ) :
    Nonempty
      (AlgebraicGroup.Iso (dVariety k (n + 1))
        (Variety.prod (dVariety k n) (KMult k))) :=
  ⟨Iso.ofInverseMorphisms
    (splitDAlgebraicMorphism n)
    (mergeDAlgebraicMorphism n)
    (merge_split n)
    (split_merge n)⟩

/-- Coordinate splitting identifies `D_(n+1)` with `D_n × KMult`. -/
public noncomputable def dVarietySuccProdIso (n : ℕ) :
    AlgebraicGroup.Iso (dVariety k (n + 1))
      (Variety.prod (dVariety k n) (KMult k)) :=
  Classical.choice (dVarietySuccProdIso_nonempty n)

end Theory.AlgebraicGroup
