module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicSetup
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Quotient

universe u

set_option linter.style.haveILetI false

/-!
Adjacent quotients of a standard-parabolic relative-root filtration.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Successive standard-parabolic relative-root layers form a descending
filtration. -/
public lemma standardParabolicRelativeRootLayer_succ_le
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    S.layer (i + 1) ≤ S.layer i := by
  letI := Fintype.ofFinite S.ι
  exact relativeRootSeries_antitone S.D S.rootEquiv S.rationalBase.support
    S.coeff S.J (Nat.le_succ i)

/-- The next relative-root layer is normal in every positive layer. -/
public lemma standardParabolicRelativeRootLayer_next_normal
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    ((S.layer (i + 1)).subgroupOf (S.layer i)).Normal := by
  letI := Fintype.ofFinite S.ι
  exact relativeRootSeries_next_layer_normal S.D S.C S.rationalPairing
    S.rootEquiv S.rationalBase S.coeff S.rationalSimpleRootExpansion
    S.chevalleySystem S.J i hi

/-- Every adjacent positive relative-root quotient is commutative. -/
public lemma standardParabolicRelativeRootLayer_quotient_commutative
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    IsMulCommutative
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  dsimp only
  letI := Fintype.ofFinite S.ι
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hcomm : ⁅S.layer i, S.layer i⁆ ≤ S.layer (i + 1) :=
    relativeRootSeries_commutator_same_layer_le_next_layer S.D S.C
      S.rationalPairing S.rootEquiv S.rationalBase S.coeff
      S.rationalSimpleRootExpansion S.chevalleySystem S.J i hi
  have hmap : (_root_.commutator ↥(S.layer i)).map (S.layer i).subtype ≤
      S.layer (i + 1) := by
    rw [Subgroup.map_subtype_commutator]
    exact hcomm
  simpa [Subgroup.comap_subtype] using
    (Subgroup.map_le_iff_le_comap.mp hmap)

end Theory.AlgebraicGroup
