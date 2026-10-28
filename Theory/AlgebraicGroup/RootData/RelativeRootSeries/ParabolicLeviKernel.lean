module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicBounds
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicLeviAction

universe u

set_option linter.style.haveILetI false

/-!
The direct conjugation action of the standard Levi point subgroup on
relative-root layers and its exact group-theoretic kernel.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Restrict the normalizer conjugation homomorphism to the standard Levi
point subgroup. -/
public noncomputable def standardLeviSubgroup_relativeRootLayer_conjugationHom
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    standardLeviSubgroup S.D S.sigmaJ →* MulAut (S.layer i) :=
  (S.layer i).normalizerMonoidHom.comp
    (Subgroup.inclusion
      (standardLeviSubgroup_le_relativeRootLayer_normalizer S i))

/-- The direct layer action is ambient conjugation. -/
public lemma standardLeviSubgroup_relativeRootLayer_conjugationHom_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ)
    (l : standardLeviSubgroup S.D S.sigmaJ) (x : S.layer i) :
    ((standardLeviSubgroup_relativeRootLayer_conjugationHom S i l) x :
        Variety.Point K) =
      l.1 * x.1 * l.1⁻¹ := by
  rfl

/-- The kernel of the direct standard-Levi action on a relative-root layer is
the pullback of that layer's ambient centralizer. -/
public lemma standardLeviSubgroup_relativeRootLayer_conjugationHom_ker
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :
    (standardLeviSubgroup_relativeRootLayer_conjugationHom S i).ker =
      (Subgroup.centralizer (S.layer i : Set (Variety.Point K))).comap
        (standardLeviSubgroup S.D S.sigmaJ).subtype := by
  ext l
  change ((Subgroup.inclusion
    (standardLeviSubgroup_le_relativeRootLayer_normalizer S i)) l) ∈
      (S.layer i).normalizerMonoidHom.ker ↔ _
  rw [Subgroup.normalizerMonoidHom_ker]
  rfl

/-- On the first layer, the direct standard-Levi action kernel is the pullback
of the ambient centralizer of the standard unipotent radical. -/
public lemma standardLeviSubgroup_unipotentRadical_conjugationHom_ker
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) :
    (standardLeviSubgroup_relativeRootLayer_conjugationHom S 1).ker =
      (Subgroup.centralizer (S.U.toSubgroup : Set (Variety.Point K))).comap
        (standardLeviSubgroup S.D S.sigmaJ).subtype := by
  rw [standardLeviSubgroup_relativeRootLayer_conjugationHom_ker,
    ← standardParabolicUnipotentRadical_eq_firstRelativeRootLayer S]

/-- The standard Levi action on a positive adjacent quotient, expressed as a
homomorphism to its multiplicative automorphism group. -/
public noncomputable def
    standardLeviSubgroup_relativeRootLayer_quotientConjugationHom
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    standardLeviSubgroup S.D S.sigmaJ →*
      MulAut (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  letI := standardLeviSubgroup_relativeRootLayer_quotientAction S i hi
  exact MulDistribMulAction.toMulAut
    (standardLeviSubgroup S.D S.sigmaJ)
    (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i))

/-- A standard Levi element acts trivially on an adjacent quotient exactly
when every conjugation displacement lies in the next relative-root layer. -/
public lemma
    mem_standardLeviSubgroup_relativeRootLayer_quotientConjugationHom_ker_iff
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (l : standardLeviSubgroup S.D S.sigmaJ) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    l ∈
        (standardLeviSubgroup_relativeRootLayer_quotientConjugationHom S i hi).ker ↔
      ∀ x : S.layer i, l.1 * x.1 * l.1⁻¹ * x.1⁻¹ ∈ S.layer (i + 1) := by
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  letI := standardLeviSubgroup_relativeRootLayer_quotientAction S i hi
  let N := (S.layer (i + 1)).subgroupOf (S.layer i)
  constructor
  · intro hl x
    let y : S.layer i :=
      ⟨l.1 * x.1 * l.1⁻¹, by
        have hnorm :=
          standardLeviSubgroup_le_relativeRootLayer_normalizer S i l.2
        rw [Subgroup.mem_normalizer_iff] at hnorm
        exact (hnorm x.1).mp x.2⟩
    have hl' :
        standardLeviSubgroup_relativeRootLayer_quotientConjugationHom S i hi l = 1 :=
      hl
    have hvalue := congrArg
      (fun f : MulAut (S.layer i ⧸ N) => f (QuotientGroup.mk' N x)) hl'
    have haction :
        (standardLeviSubgroup_relativeRootLayer_quotientAction S i hi).smul l
          (QuotientGroup.mk' N x) = QuotientGroup.mk' N y := by
      simpa [y] using
        standardLeviSubgroup_relativeRootLayer_quotientAction_mk S i hi l x
    change (standardLeviSubgroup_relativeRootLayer_quotientAction S i hi).smul l
      (QuotientGroup.mk' N x) = QuotientGroup.mk' N x at hvalue
    rw [haction] at hvalue
    have hmem := QuotientGroup.eq_iff_div_mem.mp hvalue
    change (((y / x : S.layer i) : Variety.Point K) ∈ S.layer (i + 1)) at hmem
    simpa [y, div_eq_mul_inv, mul_assoc] using hmem
  · intro hl
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    let y : S.layer i :=
      ⟨l.1 * x.1 * l.1⁻¹, by
        have hnorm :=
          standardLeviSubgroup_le_relativeRootLayer_normalizer S i l.2
        rw [Subgroup.mem_normalizer_iff] at hnorm
        exact (hnorm x.1).mp x.2⟩
    have haction :
        (standardLeviSubgroup_relativeRootLayer_quotientAction S i hi).smul l
          (QuotientGroup.mk' N x) = QuotientGroup.mk' N y := by
      simpa [y] using
        standardLeviSubgroup_relativeRootLayer_quotientAction_mk S i hi l x
    change (standardLeviSubgroup_relativeRootLayer_quotientAction S i hi).smul l
      (QuotientGroup.mk' N x) = QuotientGroup.mk' N x
    rw [haction]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (((y / x : S.layer i) : Variety.Point K) ∈ S.layer (i + 1))
    simpa [y, div_eq_mul_inv, mul_assoc] using hl x

end Theory.AlgebraicGroup
