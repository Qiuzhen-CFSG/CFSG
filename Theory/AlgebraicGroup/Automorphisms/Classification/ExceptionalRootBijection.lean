module

public import Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_2
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality
import all Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_2
import all Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.Core

/-!
# Exceptional root bijection

This module transports the exceptional root-pairing duality to a Steinberg
Chevalley root-group datum.  The realization identifies integral pairings,
simple roots, heights, and the chosen positive system.  Conjugating the unique
root-pairing duality by `setup.rootEquiv` therefore gives the unique
angle-preserving length-changing root bijection required in GLS3 Theorem
1.15.4(b).  The field characteristic enters only through the exceptional
Steinberg-type hypothesis, while the root-system rigidity itself is
characteristic-free.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem rootPairingInt_eq
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) {C : ChevalleyData K D}
    (setup : SteinbergChevalleyRootSystem D C)
    (α β : D.Root) :
    D.pairing α β = setup.pairing.pairingIn ℤ (setup.rootEquiv α) (setup.rootEquiv β) := by
  rcases setup.realizesRoots with ⟨hpair, _, _, _, _⟩
  exact_mod_cast (show (D.pairing α β : ℝ) =
      (setup.pairing.pairingIn ℤ (setup.rootEquiv α) (setup.rootEquiv β) : ℝ) by
    change (D.pairing α β : ℝ) =
      algebraMap ℤ ℝ (setup.pairing.pairingIn ℤ
        (setup.rootEquiv α) (setup.rootEquiv β))
    rw [setup.pairing.algebraMap_pairingIn]
    exact hpair α β)

omit [IsAlgClosed k] in
private theorem transport_duality
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (setup : SteinbergChevalleyRootSystem D C)
    (ρ : Equiv.Perm setup.ι) :
    setup.pairing.IsPositiveRootDuality setup.base ρ ↔
      IsAnglePreservingLengthChangingRootBijection D
        (setup.rootEquiv.trans (ρ.trans setup.rootEquiv.symm)) := by
  rcases setup.realizesRoots with ⟨hpair, _, _, hsimple, hheight⟩
  have hD := setup.realizesRootGroups
  simp only [RootGroupData.IsRealization] at hD
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, hpositive, _⟩
  have hpos (α : D.Root) :
      α ∈ D.positive ↔ setup.base.IsPos (setup.rootEquiv α) := by
    rw [hpositive]
    change 0 < D.height α ↔ 0 < setup.base.height (setup.rootEquiv α)
    rw [hheight]
  have hlong (α : D.Root) :
      IsLongRoot D α ↔ setup.pairing.IsLongIndex (setup.rootEquiv α) := by
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨setup.rootEquiv β, by
        simpa only [← rootPairingInt_eq D setup] using hβ⟩
    · rintro ⟨j, hj⟩
      obtain ⟨β, rfl⟩ := setup.rootEquiv.surjective j
      exact ⟨β, by simpa only [rootPairingInt_eq D setup] using hj⟩
  have hshort (α : D.Root) :
      IsShortRoot D α ↔ setup.pairing.IsShortIndex (setup.rootEquiv α) := by
    constructor
    · rintro ⟨β, hβ⟩
      exact ⟨setup.rootEquiv β, by
        simpa only [← rootPairingInt_eq D setup] using hβ⟩
    · rintro ⟨j, hj⟩
      obtain ⟨β, rfl⟩ := setup.rootEquiv.surjective j
      exact ⟨β, by simpa only [rootPairingInt_eq D setup] using hj⟩
  let lift (τ : Equiv.Perm setup.ι) : Equiv.Perm D.Root :=
    setup.rootEquiv.trans (τ.trans setup.rootEquiv.symm)
  constructor
  · rintro ⟨hsupport, hbasePos, hlongShort, hshortLong, hangle⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro α
      rw [hsimple α, hsimple (lift ρ α)]
      simpa only [lift, Equiv.trans_apply, Equiv.apply_symm_apply] using
        hsupport (setup.rootEquiv α)
    · intro α
      rw [hpos α, hpos (lift ρ α)]
      simpa only [lift, Equiv.trans_apply, Equiv.apply_symm_apply] using
        hbasePos (setup.rootEquiv α)
    · intro α
      rw [hlong α, hshort (lift ρ α)]
      simpa only [lift, Equiv.trans_apply, Equiv.apply_symm_apply] using
        hlongShort (setup.rootEquiv α)
    · intro α
      rw [hshort α, hlong (lift ρ α)]
      simpa only [lift, Equiv.trans_apply, Equiv.apply_symm_apply] using
        hshortLong (setup.rootEquiv α)
    · intro α β
      rw [rootPairingInt_eq D setup, rootPairingInt_eq D setup,
        rootPairingInt_eq D setup, rootPairingInt_eq D setup]
      simpa only [lift, Equiv.trans_apply, Equiv.apply_symm_apply] using
        hangle (setup.rootEquiv α) (setup.rootEquiv β)
  · intro hρ
    rcases hρ with ⟨hsupport, hbasePos, hlongShort, hshortLong, hangle⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [hsimple, lift, Equiv.trans_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        hsupport (setup.rootEquiv.symm i)
    · intro i
      simpa only [hpos, lift, Equiv.trans_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        hbasePos (setup.rootEquiv.symm i)
    · intro i
      simpa only [hlong, hshort, lift, Equiv.trans_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        hlongShort (setup.rootEquiv.symm i)
    · intro i
      simpa only [hshort, hlong, lift, Equiv.trans_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        hshortLong (setup.rootEquiv.symm i)
    · intro i j
      simpa only [rootPairingInt_eq D setup, lift, Equiv.trans_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        hangle (setup.rootEquiv.symm i) (setup.rootEquiv.symm j)

omit [IsAlgClosed k] in
public theorem existsUnique_exceptionalRootBijection
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (setup : SteinbergChevalleyRootSystem D C)
    (classification : RootClassification)
    (hClass : D.HasDynkinClassificationForSteinberg classification)
    (hExceptional : IsExceptionalSteinbergType classification (ringChar k)) :
    ExistsUnique (IsAnglePreservingLengthChangingRootBijection D) := by
  rcases hClass with ⟨⟨numbering, hnum⟩⟩
  let numbering' : setup.base.support ≃ Fin classification.rank :=
    { toFun := fun α => numbering ⟨setup.rootEquiv.symm α, by
        simp [setup.realizesRoots.2.2.2.1] at α ⊢⟩
      invFun := fun i => ⟨setup.rootEquiv (numbering.symm i),
        (setup.realizesRoots.2.2.2.1 _).mp (numbering.symm i).property⟩
      left_inv := by
        intro α
        apply Subtype.ext
        simp
      right_inv := by
        intro i
        simp }
  have hbase : ∀ i j, setup.base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry classification (numbering' i) (numbering' j) := by
    intro i j
    calc
      setup.base.cartanMatrixIn ℤ i j =
          D.pairing (setup.rootEquiv.symm i) (setup.rootEquiv.symm j) := by
        rw [RootPairing.Base.cartanMatrixIn_def]
        symm
        simpa using rootPairingInt_eq D setup (setup.rootEquiv.symm i) (setup.rootEquiv.symm j)
      _ = dynkinCartanEntry classification (numbering' i) (numbering' j) := by
        simpa [numbering'] using hnum
          ⟨setup.rootEquiv.symm i, by
            apply (setup.realizesRoots.2.2.2.1 _).mpr
            simpa only [Equiv.apply_symm_apply] using i.property⟩
          ⟨setup.rootEquiv.symm j, by
            apply (setup.realizesRoots.2.2.2.1 _).mpr
            simpa only [Equiv.apply_symm_apply] using j.property⟩
  have hexClass : IsExceptionalDualityClassification classification := by
    rcases hExceptional with hB | hF | hG
    · exact Or.inl ⟨hB.1, hB.2.1⟩
    · exact Or.inr (Or.inl ⟨hF.1, hF.2.1⟩)
    · exact Or.inr (Or.inr ⟨hG.1, hG.2.1⟩)
  rcases existsUnique_exceptionalRootDuality setup.base classification numbering'
      hbase hexClass with ⟨ρ, hρ, hρuniq⟩
  let lift (τ : Equiv.Perm setup.ι) : Equiv.Perm D.Root :=
    setup.rootEquiv.trans (τ.trans setup.rootEquiv.symm)
  refine ⟨lift ρ, (transport_duality D C setup ρ).mp hρ, ?_⟩
  intro σ hσ
  let lower : Equiv.Perm setup.ι := setup.rootEquiv.symm.trans (σ.trans setup.rootEquiv)
  have hreconstruct : lift lower = σ := by
    ext α
    simp only [lift, lower, Equiv.trans_apply, Equiv.symm_apply_apply]
  have hlowerAngle : IsAnglePreservingLengthChangingRootBijection D (lift lower) := by
    rw [hreconstruct]
    exact hσ
  have hlower : setup.pairing.IsPositiveRootDuality setup.base lower :=
    (transport_duality D C setup lower).mpr hlowerAngle
  calc
    σ = lift lower := hreconstruct.symm
    _ = lift ρ := congrArg lift (hρuniq lower hlower)

end Theory.AlgebraicGroup
