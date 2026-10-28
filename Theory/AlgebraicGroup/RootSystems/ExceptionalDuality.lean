module

import all Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.Core
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.B2ModelAdapter
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.F4ModelAdapter
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDualityG2
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.LengthPartition

/-!
# Exceptional root duality rigidity

This module classifies the positive root dualities of the non-simply-laced
self-dual exceptional Cartan matrices `B₂`, `F₄`, and `G₂`.  Such a duality
preserves a chosen base and positive system, exchanges the two asymmetric
integral-pairing length classes, and preserves every Coxeter product.

Existence reverses the numbered base, identifies its Cartan matrix with that
of the flipped root pairing, and applies
`RootPairing.Base.equivOfCartanMatrixEq`.  Positivity is transported through
the additive closure characterization
`RootPairing.Base.isPos_iff_root_mem_closure`.  Uniqueness is supplied by the
three finite standard-model adapters, whose positive-root fingerprints and
simple-root permutations are kernel checked.

The result is purely about finite reduced crystallographic real root systems;
in particular, it has no field-characteristic hypothesis.  It is the root
system input for the exceptional graph-field automorphism construction.  The
assembly also exports the corresponding theorem that every exceptional root is
in one of the two directed root-length classes.
-/

namespace Theory.AlgebraicGroup

open Set

private theorem flip_isPos_iff
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (α : ι) : base.flip.IsPos α ↔ base.IsPos α := by
  apply base.induction_reflect α (p := fun i => base.flip.IsPos i ↔ base.IsPos i)
  · intro i hi
    have hf : base.flip.IsPos (P.flip.reflectionPerm i i) ↔ ¬base.flip.IsPos i := by
      let _ := P.flip.indexNeg
      exact RootPairing.Base.IsPos.neg_iff_not base.flip i
    change base.flip.IsPos (P.reflectionPerm i i) ↔ ¬base.flip.IsPos i at hf
    have hb : base.IsPos (P.reflectionPerm i i) ↔ ¬base.IsPos i := by
      let _ := P.indexNeg
      exact RootPairing.Base.IsPos.neg_iff_not base i
    rw [hf, hb, hi]
  · intro i hi
    exact ⟨fun _ => base.isPos_of_mem_support hi,
      fun _ => base.flip.isPos_of_mem_support hi⟩
  · intro i j hi hj
    by_cases hij : i = j
    · subst i
      have hf : base.flip.IsPos (P.flip.reflectionPerm j j) ↔ ¬base.flip.IsPos j := by
        let _ := P.flip.indexNeg
        exact RootPairing.Base.IsPos.neg_iff_not base.flip j
      change base.flip.IsPos (P.reflectionPerm j j) ↔ ¬base.flip.IsPos j at hf
      have hb : base.IsPos (P.reflectionPerm j j) ↔ ¬base.IsPos j := by
        let _ := P.indexNeg
        exact RootPairing.Base.IsPos.neg_iff_not base j
      rw [hf, hb, hi]
    · by_cases hrj : P.reflectionPerm j i = j
      · rw [hrj]
        exact ⟨fun _ => base.isPos_of_mem_support hj,
          fun _ => base.flip.isPos_of_mem_support hj⟩
      · constructor
        · intro h
          have h' : base.flip.IsPos i := by
            simpa using h.reflectionPerm hj hrj
          exact (hi.mp h').reflectionPerm hj hij
        · intro h
          have h' : base.IsPos i := by
            simpa using h.reflectionPerm hj hrj
          exact (hi.mpr h').reflectionPerm hj hij

private theorem exists_positiveRootDuality_of_flip_cartan
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) {eBase : base.support ≃ (base.flip).support}
    (hcart : ∀ i j, base.flip.cartanMatrix (eBase i) (eBase j) =
      base.cartanMatrix i j) :
    ∃ ρ : Equiv.Perm ι, P.IsPositiveRootDuality base ρ := by
  let e : P.Equiv P.flip := base.equivOfCartanMatrixEq base.flip eBase hcart
  let ρ : Equiv.Perm ι := e.toHom.indexEquiv
  have heBase (i : base.support) : ρ i = eBase i := by
    apply P.flip.root.injective
    rw [← RootPairing.Hom.root_weightMap_apply P P.flip i e.toHom]
    change (base.toWeightBasis.equiv base.flip.toWeightBasis eBase) (P.root i) =
      P.flip.root (eBase i)
    simp [Module.Basis.equiv]
  have hsupport (α : ι) : α ∈ base.support ↔ ρ α ∈ base.support := by
    constructor
    · intro hα
      have := heBase ⟨α, hα⟩
      rw [this]
      exact (eBase ⟨α, hα⟩).property
    · intro hα
      let i : base.support :=
        ⟨(eBase.symm ⟨ρ α, by simpa [RootPairing.Base.flip_support] using hα⟩ :
          base.support), (eBase.symm ⟨ρ α, by
            simpa [RootPairing.Base.flip_support] using hα⟩ :
          base.support).property⟩
      have hi : (i : ι) = α := by
        apply ρ.injective
        rw [heBase]
        simp [i]
      simpa [hi] using i.property
  have hpos (α : ι) : base.IsPos α ↔ base.IsPos (ρ α) := by
    constructor
    · intro h
      have hmap (x : M)
          (hx : x ∈ AddSubmonoid.closure (P.root '' (base.support : Set ι))) :
          e.weightEquiv P P.flip x ∈ AddSubmonoid.closure
            (P.flip.root '' (base.flip.support : Set ι)) := by
        induction hx using AddSubmonoid.closure_induction with
        | mem x hx =>
            rcases hx with ⟨j, hj, rfl⟩
            refine AddSubmonoid.subset_closure ⟨ρ j, ?_, ?_⟩
            · simpa [hsupport j, RootPairing.Base.flip_support] using hj
            · exact (RootPairing.Hom.root_weightMap_apply P P.flip j e.toHom).symm
        | zero => simp
        | add x y hx hy hx' hy' => simpa using AddSubmonoid.add_mem _ hx' hy'
      exact (flip_isPos_iff base (ρ α)).mp <|
        (base.flip.isPos_iff_root_mem_closure _).mpr <| by
          simpa [ρ, RootPairing.Hom.root_weightMap_apply] using
            hmap _ ((base.isPos_iff_root_mem_closure _).mp h)
    · intro h
      have hmap (x : N)
          (hx : x ∈ AddSubmonoid.closure
            (P.flip.root '' (base.flip.support : Set ι))) :
          (e.weightEquiv P P.flip).symm x ∈ AddSubmonoid.closure
            (P.root '' (base.support : Set ι)) := by
        induction hx using AddSubmonoid.closure_induction with
        | mem x hx =>
            rcases hx with ⟨j, hj, rfl⟩
            obtain ⟨i, hi⟩ := e.toHom.indexEquiv.surjective j
            refine AddSubmonoid.subset_closure ⟨i, ?_, ?_⟩
            · apply (hsupport i).mpr
              rw [hi]
              simpa [RootPairing.Base.flip_support] using hj
            · rw [← hi]
              rw [← RootPairing.Hom.root_weightMap_apply P P.flip i e.toHom]
              simp
        | zero => simp
        | add x y hx hy hx' hy' => simpa using AddSubmonoid.add_mem _ hx' hy'
      apply (base.isPos_iff_root_mem_closure _).mpr
      have h' := (base.flip.isPos_iff_root_mem_closure _).mp <|
        (flip_isPos_iff base (ρ α)).mpr h
      have hout := hmap _ h'
      have hinv : (e.weightEquiv P P.flip).symm (P.flip.root (ρ α)) = P.root α := by
        rw [← RootPairing.Hom.root_weightMap_apply P P.flip α e.toHom]
        simp
      rw [hinv] at hout
      exact hout
  have hswap (α β : ι) :
      P.pairingIn ℤ (ρ α) (ρ β) = P.pairingIn ℤ β α := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ))
    change algebraMap ℤ ℝ (P.pairingIn ℤ (ρ α) (ρ β)) =
      algebraMap ℤ ℝ (P.pairingIn ℤ β α)
    rw [P.algebraMap_pairingIn, P.algebraMap_pairingIn]
    exact RootPairing.Equiv.pairing_eq e β α
  refine ⟨ρ, hsupport, hpos, ?_, ?_, ?_⟩
  · intro α
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨ρ β, by rw [hswap, hswap]; exact hβ⟩
    · rintro ⟨β, hβ⟩
      obtain ⟨γ, rfl⟩ := ρ.surjective β
      exact ⟨γ, by simpa [hswap] using hβ⟩
  · intro α
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨ρ β, by rw [hswap, hswap]; exact hβ⟩
    · rintro ⟨β, hβ⟩
      obtain ⟨γ, rfl⟩ := ρ.surjective β
      exact ⟨γ, by simpa [hswap] using hβ⟩
  · intro α β
    rw [hswap, hswap, mul_comm]

public theorem exists_exceptionalRootDuality
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (classification : RootClassification)
    (numbering : base.support ≃ Fin classification.rank)
    (hbase : ∀ i j, base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry classification (numbering i) (numbering j))
    (hExceptional : IsExceptionalDualityClassification classification) :
    ∃ ρ : Equiv.Perm ι, P.IsPositiveRootDuality base ρ := by
  let revBase : base.support ≃ base.support :=
    numbering.trans ((Fin.revPerm (n := classification.rank)).trans numbering.symm)
  let eBase : base.support ≃ base.flip.support :=
    revBase.trans (Equiv.setCongr (by simp))
  have hrev (i : base.support) :
      ((eBase i : base.flip.support) : ι) =
        numbering.symm (Fin.revPerm (numbering i)) := by
    rfl
  have hcart : ∀ i j, base.flip.cartanMatrix (eBase i) (eBase j) =
      base.cartanMatrix i j := by
    intro i j
    have hbase' (x y : base.support) :
        P.pairingIn ℤ x y =
          dynkinCartanEntry classification (numbering x) (numbering y) := by
      simpa [RootPairing.Base.cartanMatrixIn_def] using hbase x y
    change P.flip.pairingIn ℤ (eBase i) (eBase j) = P.pairingIn ℤ i j
    change P.pairingIn ℤ (eBase j) (eBase i) = P.pairingIn ℤ i j
    let x : base.support := ⟨eBase j, (eBase j).property⟩
    let y : base.support := ⟨eBase i, (eBase i).property⟩
    rw [show P.pairingIn ℤ (eBase j) (eBase i) = P.pairingIn ℤ x y by rfl,
      hbase', hbase']
    change dynkinCartanEntry classification (numbering x) (numbering y) =
      dynkinCartanEntry classification (numbering i) (numbering j)
    have hx : numbering x = Fin.revPerm (numbering j) := by
      have : x = numbering.symm (Fin.revPerm (numbering j)) := Subtype.ext (hrev j)
      rw [this]
      simp
    have hy : numbering y = Fin.revPerm (numbering i) := by
      have : y = numbering.symm (Fin.revPerm (numbering i)) := Subtype.ext (hrev i)
      rw [this]
      simp
    rw [hx, hy]
    rcases hExceptional with hB | hF | hG
    · rcases hB with ⟨hk, hr⟩
      rcases classification with ⟨kind, rank⟩
      simp only at hk hr
      subst kind
      subst rank
      generalize numbering i = ii
      generalize numbering j = jj
      fin_cases ii <;> fin_cases jj <;>
        simp [dynkinCartanEntry]
    · rcases hF with ⟨hk, hr⟩
      rcases classification with ⟨kind, rank⟩
      simp only at hk hr
      subst kind
      subst rank
      generalize numbering i = ii
      generalize numbering j = jj
      fin_cases ii <;> fin_cases jj <;>
        simp [dynkinCartanEntry]
    · rcases hG with ⟨hk, hr⟩
      rcases classification with ⟨kind, rank⟩
      simp only at hk hr
      subst kind
      subst rank
      generalize numbering i = ii
      generalize numbering j = jj
      fin_cases ii <;> fin_cases jj <;>
        simp [dynkinCartanEntry]
  exact exists_positiveRootDuality_of_flip_cartan base hcart

/-- Exceptional `B₂`, `F₄`, and `G₂` root dualities exist uniquely. -/
public theorem existsUnique_exceptionalRootDuality
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (classification : RootClassification)
    (numbering : base.support ≃ Fin classification.rank)
    (hbase : ∀ i j, base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry classification (numbering i) (numbering j))
    (hExceptional : IsExceptionalDualityClassification classification) :
    ExistsUnique (P.IsPositiveRootDuality base) := by
  rcases exists_exceptionalRootDuality base classification numbering hbase
    hExceptional with ⟨ρ, hρ⟩
  refine ⟨ρ, hρ, ?_⟩
  intro σ hσ
  rcases hExceptional with hB | hF | hG
  · exact exceptional_b2_positiveRootDuality_unique base classification numbering
      hbase hB hσ hρ
  · exact exceptional_f4_positiveRootDuality_unique base classification numbering
      hbase hF hσ hρ
  · rcases classification with ⟨kind, rank⟩
    rcases hG with ⟨rfl, rfl⟩
    apply exceptional_g2_root_duality_unique base numbering
    · intro i j
      have h := hbase (numbering.symm i) (numbering.symm j)
      rw [RootPairing.Base.cartanMatrixIn_def (S := ℤ)] at h
      fin_cases i <;> fin_cases j <;>
        simp [dynkinCartanEntry, StandardRootSystem.typeG2CartanMatrix] at h ⊢
      all_goals assumption
    · exact hσ
    · exact hρ

end Theory.AlgebraicGroup
