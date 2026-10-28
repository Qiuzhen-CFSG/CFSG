module

public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.Dimension.Isomorphism
public import Theory.AlgebraicGroup.Tori.Power
public import Theory.AlgebraicGroup.Tori.Product

universe u

/-! Dimension of standard diagonal tori. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma kMult_dimension_eq_one :
    Variety.dimension (KMult k) = 1 := by
  let : IsDomain (coordinateRing (KMult k)) :=
    irreducibleVariety_coordinateRing_domain (KMult k)
      (connectedAlgebraicGroup_irreducible
        (KMult k) (dVariety_isConnected (k := k) 1))
  have hirr := connectedAlgebraicGroup_irreducible
    (KMult k) (dVariety_isConnected (k := k) 1)
  rw [dimension_eq_fractionRing_of_isIrreducible (KMult k) hirr]
  rw [trdeg_fractionRing_eq]
  let I := vanishingIdeal (Set.univ : Set (Variety.Point (KMult k)))
  have hI : I ≠ ⊥ := by
    let i : Fin 1 := ⟨0, by omega⟩
    let p : MvPolynomial (KMult k).Coordinates k :=
      MvPolynomial.X (Sum.inl (ULift.up i)) *
        MvPolynomial.X (Sum.inr (ULift.up i)) - 1
    have hpI : p ∈ I := by
      intro x hx
      exact x.isZero p (Set.mem_ofPred.mpr ⟨i, rfl⟩)
    have hpne : p ≠ 0 := by
      intro hp
      have heval := congrArg
        (MvPolynomial.eval (fun _ : (KMult k).Coordinates ↦ (0 : k))) hp
      simp [p] at heval
    intro hbot
    rw [hbot] at hpI
    exact hpne (Ideal.mem_bot.mp hpI)
  have hlt : Algebra.trdeg k
      (MvPolynomial (KMult k).Coordinates k ⧸ I) < 2 := by
    have h := trdeg_quotient_lt_coordinates_of_ne_bot
      (k := k) (KMult k).Coordinates I hI
    simpa using h
  have hle : Algebra.trdeg k
      (MvPolynomial (KMult k).Coordinates k ⧸ I) ≤ 1 := by
    rw [show (2 : Cardinal) = 1 + 1 by norm_num] at hlt
    exact Cardinal.lt_natCast_add_one_iff.mp hlt
  have hnonzero : ({0} : Set k)ᶜ.Infinite :=
    (Set.finite_singleton 0).infinite_compl
  let NonzeroK := {a : k // a ∈ ({0} : Set k)ᶜ}
  let : Infinite NonzeroK := Set.infinite_coe_iff.mpr hnonzero
  have : Infinite kˣ :=
    Infinite.of_injective
      (fun a : NonzeroK ↦ Units.mk0 a.1 (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using a.2))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg Units.val h)
  have : Infinite (Fin 1 → kˣ) :=
    Infinite.of_injective (fun a : kˣ ↦ fun _ ↦ a) (by
      intro a b h
      exact congrFun h ⟨0, by omega⟩)
  have : Infinite (Variety.Point (KMult k)) :=
    Infinite.of_injective (dPointEquiv (k := k) 1).symm
      (dPointEquiv (k := k) 1).symm.injective
  have hdimne : Variety.dimension (KMult k) ≠ 0 := by
    intro hzero
    have hfin : Finite (Variety.Point (KMult k)) :=
      (dimension_zero_iff_finite_points (KMult k)).mp hzero
    exact @not_finite (Variety.Point (KMult k)) inferInstance hfin
  have htrne : Algebra.trdeg k
      (MvPolynomial (KMult k).Coordinates k ⧸ I) ≠ 0 := by
    intro hzero
    apply hdimne
    rw [dimension_eq_fractionRing_of_isIrreducible (KMult k) hirr]
    rw [trdeg_fractionRing_eq]
    simpa [I] using hzero
  exact le_antisymm hle (Cardinal.one_le_iff_ne_zero.mpr htrne)

/-- The standard diagonal torus `D_n` has dimension `n`. -/
public theorem dVariety_dimension_eq (n : ℕ) :
    Variety.dimension (dVariety k n) = n := by
  induction n with
  | zero =>
      apply (dimension_zero_iff_finite_points (dVariety k 0)).2
      let : Subsingleton (Variety.Point (dVariety k 0)) :=
        ⟨fun x y => (dPointEquiv 0).injective <| funext fun i => Fin.elim0 i⟩
      exact Finite.of_subsingleton
  | succ n ih =>
      rw [algebraicGroupIso_dimension_eq (dVarietySuccProdIso n)]
      rw [dimension_product_additive, ih, kMult_dimension_eq_one]
      simp

end Theory.AlgebraicGroup
