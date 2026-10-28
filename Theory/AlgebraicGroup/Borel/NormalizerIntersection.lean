module

public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.RootData.Standard
public import Theory.AlgebraicGroup.RootSystems.Weyl
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Tori.UnipotentIntersection

/-!
The standard Borel intersects the normalizer of its maximal torus in exactly
that torus.  This is the intersection assertion used in GLS3, Theorem 1.11.3.

The normalizer/Weyl package is kept explicit: it identifies the normalizer
quotient, transports positive root groups under that action, and supplies the
standard reflection consequence that every nonidentity Weyl element has an
inversion root.  The proof first excludes a negative root group from the Borel.
Indeed, the opposite-root intersection bound would put such a root group in
the torus, contradicting the trivial intersection of a torus with a nontrivial
unipotent root group.  An element of the Borel-normalizer intersection therefore
preserves every positive root.  The inversion-root property makes its Weyl
class trivial, so the quotient kernel puts the element in the torus.
-/

set_option linter.style.haveILetI false

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The part of the maximal-torus normalizer/Weyl package needed to identify
its intersection with a standard Borel. -/
public structure StandardNormalizerRootAction
    {K : Variety k} [AlgebraicGroup K]
    (T B : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root)
    {ι X Y : Type u} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (base : P.Base) (e : D.Root ≃ ι) where
  weylEquiv :
    (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) ⧸
      T.toSubgroup.subgroupOf
        (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))) ≃*
      P.weylGroup
  mapRootGroupIntoB : ∀
    (n : Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))
    (α : D.Root),
    α ∈ positiveRoots → (n : Variety.Point K) ∈ B.toSubgroup →
    (D.rootSubgroup
      (e.symm (P.weylGroupToPerm
        (weylEquiv (QuotientGroup.mk'
          (T.toSubgroup.subgroupOf
            (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))) n))
          (e α)))).toSubgroup ≤ B.toSubgroup
  nontrivialHasInversion : ∀ w : P.weylGroup, w ≠ 1 →
    ∃ i, base.IsPos i ∧ ¬base.IsPos (P.weylGroupToPerm w i)

/-- GLS3, Theorem 1.11.3: the standard Borel/torus-normalizer intersection is
the maximal torus. -/
public theorem standardBorel_inf_torusNormalizer_eq_torus
    {K : Variety k} [AlgebraicGroup K]
    (_hK : IsReductiveAlgebraicGroup K)
    (T B : ClosedSubgroup K) (D : RootGroupData K T)
    (positiveRoots : Set D.Root)
    (hSetup : IsStandardBorelSetup T B D positiveRoots)
    (_hBroot : B.toSubgroup =
      RootSubgroupGenerated D positiveRoots ⊔ T.toSubgroup)
    {ι X Y : Type u} [Finite ι]
    [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hActual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (action : StandardNormalizerRootAction T B D positiveRoots P base e)
    (hOppositeInf : ∀ α, α ∈ positiveRoots →
      (D.rootSubgroup (D.neg α)).toSubgroup ⊓ B.toSubgroup ≤ T.toSubgroup) :
    B.toSubgroup ⊓ Subgroup.normalizer
        (T.toSubgroup : Set (Variety.Point K)) = T.toSubgroup := by
  classical
  let N := Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))
  let TN := T.toSubgroup.subgroupOf N
  let hTNNormal : TN.Normal := T.toSubgroup.normal_in_normalizer
  letI := hTNNormal
  have hnegneg (α : D.Root) : D.neg (D.neg α) = α := by
    exact hSetup.2.1.neg_neg α
  have hroot_not_le_B (α : D.Root) (hα : α ∈ positiveRoots) :
      ¬(D.rootSubgroup (D.neg α)).toSubgroup ≤ B.toSubgroup := by
    intro hle
    have hleT : (D.rootSubgroup (D.neg α)).toSubgroup ≤ T.toSubgroup := by
      intro x hx
      exact hOppositeInf α hα ⟨hx, hle hx⟩
    have hroot := (hSetup.2.1.2.2.1 (D.neg α)).1
    have hbot := hroot.inf_torus_eq_bot hSetup.1.1
    have heqbot : (D.rootSubgroup (D.neg α)).toSubgroup = ⊥ := by
      apply le_antisymm
      · intro x hx
        have hxbot : x ∈ (⊥ : Subgroup (Variety.Point K)) := by
          rw [← hbot]
          exact ⟨hx, hleT hx⟩
        exact hxbot
      · exact bot_le
    exact hroot.invariant_unipotent_ne_bot.2.2 heqbot
  have hroot_le_B_pos (α : D.Root)
      (hle : (D.rootSubgroup α).toSubgroup ≤ B.toSubgroup) :
      α ∈ positiveRoots := by
    have hall : α ∈ positiveRoots ∪ D.neg ⁻¹' positiveRoots := by
      rw [hSetup.2.2.1.2.1]
      exact Set.mem_univ α
    rcases hall with hα | hnegα
    · exact hα
    · exfalso
      apply hroot_not_le_B (D.neg α) hnegα
      simpa [hnegneg] using hle
  apply le_antisymm
  · intro g hg
    let n : N := ⟨g, hg.2⟩
    let q : N ⧸ TN := QuotientGroup.mk' TN n
    let w : P.weylGroup := action.weylEquiv q
    have hwpos : ∀ α, α ∈ positiveRoots →
        e.symm (P.weylGroupToPerm w (e α)) ∈ positiveRoots := by
      intro α hα
      apply hroot_le_B_pos
      exact action.mapRootGroupIntoB n α hα hg.1
    have hwBasePos : ∀ i, base.IsPos i →
        base.IsPos (P.weylGroupToPerm w i) := by
      intro i hi
      let α := e.symm i
      have hα : α ∈ positiveRoots := (hActual.2.2 α).mpr (by simpa [α])
      have h := hwpos α hα
      simpa [w, α] using (hActual.2.2 _).mp h
    have hw : w = 1 := by
      by_contra hw
      obtain ⟨i, hi, hwi⟩ := action.nontrivialHasInversion w hw
      exact hwi (hwBasePos i hi)
    have hq : q = 1 := action.weylEquiv.injective (by simpa [w] using hw)
    have hnTN : n ∈ TN := by
      apply (QuotientGroup.eq_one_iff n).mp
      exact hq
    exact hnTN
  · intro g hg
    exact ⟨hSetup.2.2.2.2.1 hg, T.toSubgroup.le_normalizer hg⟩

end Theory.AlgebraicGroup
