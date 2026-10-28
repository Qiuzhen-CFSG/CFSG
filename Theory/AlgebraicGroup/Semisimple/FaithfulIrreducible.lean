module

public import Theory.AlgebraicGroup.Representations.NormalSolvableScalar
public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Semisimple.Defs

/-!
# A faithful irreducible special-linear criterion for semisimplicity

A connected algebraic group with a faithful finite-dimensional irreducible
rational action of determinant one is semisimple. Lie--Kolchin and normality
make each radical act by scalars. The determinant bounds these scalars by the
roots of `X ^ dim V - 1`; faithfulness then makes the radical finite, and
connectedness forces it to be trivial.

This is a direct criterion for the radical convention in GLS3, Definition
1.7.1 (`refs/KGroup/GLS3/Chapter1.tex`), using the proved scalar-action theorem
rather than the numbered structure theorems.
-/

namespace Theory.AlgebraicGroup
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Variety k} [AlgebraicGroup G]
  {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

public theorem radical_eq_bot_of_faithful_irreducible_det_one
    (ρ : RationalRepresentation G V)
    (hfaithful : Function.Injective ρ.action)
    (hirr : IsIrreducibleRepresentation ρ)
    (hG : Variety.IsConnected G)
    (hdet : ∀ g, LinearMap.det (ρ.action g : Module.End k V) = 1)
    (R : ClosedSubgroup G) (hR : IsRadicalSubgroup R) :
    R.toSubgroup = ⊥ := by
  have hRvar : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point G // x ∈ (R : Set (Variety.Point G))} :=
      Subtype.connectedSpace hR.connected
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨χ, hχ⟩ := ρ.acts_by_scalars_of_isIrreducible hirr
    hG R hR.normal hR.solvable hRvar
  have hpow (r : R.toSubgroup) : χ r ^ Module.finrank k V = 1 := by
    have h := hdet r
    rw [hχ r, LinearMap.det_smul] at h
    simpa using h
  have hroots : ({a : k | a ^ Module.finrank k V = 1} : Set k).Finite := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using
      Polynomial.finite_setOfPred_isRoot
        (Polynomial.X_pow_sub_C_ne_zero (Module.finrank_pos (R := k) (M := V)) (1 : k))
  let roots := {a : k // a ^ Module.finrank k V = 1}
  let : Finite roots := Set.finite_coe_iff.mpr hroots
  let embed : R.toSubgroup → roots := fun r => ⟨χ r, hpow r⟩
  have hembed : Function.Injective embed := by
    intro x y hxy
    apply Subtype.ext
    apply hfaithful
    apply Units.ext
    have he : χ x = χ y := congrArg Subtype.val hxy
    rw [hχ x, hχ y, he]
  let : Finite R.toSubgroup := Finite.of_injective embed hembed
  have hfinite : Finite (Variety.Point R.carrierVariety) :=
    (Equiv.finite_iff R.pointEquiv).mpr inferInstance
  have hdim : Variety.dimension R.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points R.carrierVariety).mpr hfinite
  by_contra hne
  have hpos := connected_closedSubgroup_dimension_pos_of_ne_bot R hR.connected hne
  rw [hdim] at hpos
  exact lt_irrefl 0 hpos

/-- A faithful irreducible rational action of determinant one detects
semisimplicity of a connected algebraic group. -/
public theorem isSemisimple_of_faithful_irreducible_det_one
    (ρ : RationalRepresentation G V)
    (hfaithful : Function.Injective ρ.action)
    (hirr : IsIrreducibleRepresentation ρ)
    (hG : Variety.IsConnected G)
    (hdet : ∀ g, LinearMap.det (ρ.action g : Module.End k V) = 1) :
    IsSemisimpleAlgebraicGroup G :=
  ⟨hG, radical_eq_bot_of_faithful_irreducible_det_one ρ hfaithful hirr hG hdet⟩

end Theory.AlgebraicGroup
