module

public import Theory.AlgebraicGroup.Borel.IsogenyImage
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.Representations.NormalSolvableScalar
public import Theory.AlgebraicGroup.RootSystems.SymplecticAlgebraicQuotient
public import Theory.AlgebraicGroup.RootSystems.SymplecticElementaryGeneration
public import Theory.AlgebraicGroup.RootSystems.SymplecticNaturalIrreducibility

/-!
# Semisimplicity of the standard symplectic carriers

The explicit standard symplectic carrier is connected by elementary root
generation.  In positive rank its natural representation is irreducible and
faithful; the scalar-action theorem for connected solvable normal subgroups
therefore puts every radical subgroup in the finite scalar center.  A
finite-point/dimension argument then makes the connected radical trivial.
Rank zero is handled directly from the subsingleton point group.  Finally,
the all-rank finite-center quotient is semisimple by the direct isogeny-image
API.  This uses only the concrete root curves, matrix representation, center,
and quotient APIs, with no classification or general Chevalley construction.
-/

universe u v

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma symplecticNaturalRepresentation_action_injective (m : ℕ) :
    Function.Injective
      (symplecticNaturalRepresentation (k := k) m).action := by
  intro x y hxy
  apply symplecticClosedPointMatrix_injective m
  ext i j
  have hxy' :
      ((symplecticNaturalRepresentation (k := k) m).action x :
        Module.End k (symplecticStandardSpace (k := k) m)) (Pi.single j 1) =
      ((symplecticNaturalRepresentation (k := k) m).action y :
        Module.End k (symplecticStandardSpace (k := k) m)) (Pi.single j 1) :=
    congrArg (fun f : LinearMap.GeneralLinearGroup k
        (symplecticStandardSpace (k := k) m) =>
      (f : Module.End k (symplecticStandardSpace (k := k) m)) (Pi.single j 1)) hxy
  have hmatx := symplecticNaturalRepresentation_action_matrix m x (Pi.single j 1)
  have hmaty := symplecticNaturalRepresentation_action_matrix m y (Pi.single j 1)
  rw [hmatx, hmaty] at hxy'
  simpa [Matrix.mulVec_single_one] using congrArg (fun z => z i) hxy'

/-- A positive-rank radical subgroup is contained in the scalar center. -/
public theorem standardSymplectic_radical_le_center (m : ℕ) (hm : 0 < m)
    (R : ClosedSubgroup
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (hR : IsRadicalSubgroup R) :
    R.toSubgroup ≤ Subgroup.center
      (Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) := by
  let i : Fin m := ⟨0, hm⟩
  letI : Inhabited (Fin m) := ⟨i⟩
  letI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl i⟩
  letI : Nontrivial (symplecticStandardSpace (k := k) m) := Pi.nontrivial
  let S := standardSymplecticClosedSubgroup (k := k) m
  let ρ := symplecticNaturalRepresentation (k := k) m
  have hirr : IsIrreducibleRepresentation ρ :=
    ⟨symplecticNaturalRepresentation_isRational m,
      symplecticNaturalRepresentation_isAlgebraicallyIrreducible m hm⟩
  have hRvar : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace
        {x : Variety.Point S.carrierVariety // x ∈
          (R : Set (Variety.Point S.carrierVariety))} :=
      Subtype.connectedSpace hR.connected
    let : ConnectedSpace (Variety.Point R.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨χ, hχ⟩ := ρ.acts_by_scalars_of_isIrreducible hirr
    (standardSymplecticClosedSubgroup_isConnected m) R hR.normal hR.solvable hRvar
  intro r hr
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply symplecticNaturalRepresentation_action_injective m
  apply Units.ext
  change (ρ.action (g * r) : Module.End k (symplecticStandardSpace (k := k) m)) =
    (ρ.action (r * g) : Module.End k (symplecticStandardSpace (k := k) m))
  rw [ρ.action.map_mul, ρ.action.map_mul]
  change (ρ.action g : Module.End k (symplecticStandardSpace (k := k) m)) *
      (ρ.action r : Module.End k (symplecticStandardSpace (k := k) m)) =
    (ρ.action r : Module.End k (symplecticStandardSpace (k := k) m)) *
      (ρ.action g : Module.End k (symplecticStandardSpace (k := k) m))
  rw [hχ ⟨r, hr⟩]
  ext v
  simp

/-- A positive-rank radical subgroup is trivial. -/
public theorem standardSymplectic_radical_eq_bot_of_pos (m : ℕ) (hm : 0 < m)
    (R : ClosedSubgroup
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (hR : IsRadicalSubgroup R) : R.toSubgroup = ⊥ := by
  have hRcenter := standardSymplectic_radical_le_center (k := k) m hm R hR
  let e : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety ≃*
      bilinearIsometrySubgroup (standardSymplecticBilinForm (k := k) m) :=
    standardSymplecticClosedSubgroupPoints (k := k) m
  letI : Finite (Subgroup.center
      (Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)) :=
    finite_center_of_mulEquiv_standardSymplectic_all m e
  let embed : R.toSubgroup → Subgroup.center
      (Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :=
    fun x => ⟨x.1, hRcenter x.2⟩
  letI : Finite R.toSubgroup := Finite.of_injective embed (by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.center
      (Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) =>
      (z : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)) hxy)
  have hRpointsFinite : Finite (Variety.Point R.carrierVariety) :=
    (Equiv.finite_iff R.pointEquiv).mpr inferInstance
  have hRdim : Variety.dimension R.carrierVariety = 0 :=
    (dimension_zero_iff_finite_points R.carrierVariety).mpr hRpointsFinite
  by_contra hRne
  have hRpos := connected_closedSubgroup_dimension_pos_of_ne_bot
    R hR.connected hRne
  rw [hRdim] at hRpos
  exact (lt_irrefl 0 hRpos)

/-- The standard symplectic carrier is semisimple in every rank. -/
public theorem standardSymplecticClosedSubgroup_isSemisimple (m : ℕ) :
    IsSemisimpleAlgebraicGroup
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety := by
  by_cases hm : 0 < m
  · let i : Fin m := ⟨0, hm⟩
    letI : Inhabited (Fin m) := ⟨i⟩
    letI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl i⟩
    letI : Nontrivial (symplecticStandardSpace (k := k) m) := Pi.nontrivial
    refine ⟨standardSymplecticClosedSubgroup_isConnected m, ?_⟩
    intro R hR
    exact standardSymplectic_radical_eq_bot_of_pos m hm R hR
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    refine ⟨standardSymplecticClosedSubgroup_isConnected 0, ?_⟩
    intro R hR
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      apply symplecticClosedPointMatrix_injective 0
      apply Subsingleton.elim
    · exact bot_le

/-- Every isogeny target of the standard symplectic carrier is semisimple. -/
public theorem standardSymplectic_isogenyTarget_isSemisimple (m : ℕ)
    {Q : Variety k} [AlgebraicGroup Q]
    (q : AlgebraicGroup.Morphism
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety Q)
    (hq : IsIsogeny q) : IsSemisimpleAlgebraicGroup Q := by
  have hQconn : Variety.IsConnected Q :=
    connected_of_surjective_morphism q
      (standardSymplecticClosedSubgroup_isConnected m) hq.1
  exact isogeny_radical_image q hq
    (standardSymplecticClosedSubgroup_isConnected m) hQconn
    (standardSymplecticClosedSubgroup_isSemisimple m)

/-- The standard finite-center projective quotient exists and is semisimple. -/
public theorem standardSymplecticQuotient_exists_isSemisimple (m : ℕ) :
    ∃ (Q : Variety k) (_ : AlgebraicGroup Q)
      (q : AlgebraicGroup.Morphism
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety Q),
      IsIsogeny q ∧
      q.kernel = Subgroup.center
        (Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) ∧
      IsSemisimpleAlgebraicGroup Q := by
  obtain ⟨Q, hQ, q, hq, hker, _hfac, _heq⟩ :=
    standardSymplecticQuotient_exists (k := k) m
  letI : AlgebraicGroup Q := hQ
  exact ⟨Q, hQ, q, hq, hker,
    standardSymplectic_isogenyTarget_isSemisimple m q hq⟩

end Theory.AlgebraicGroup
