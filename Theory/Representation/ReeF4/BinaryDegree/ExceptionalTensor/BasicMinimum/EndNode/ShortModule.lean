module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortRepresentation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortModule.Model

/-!
# A small rational irreducible F4 end-node factor

The literal F4 Chevalley carrier has a rational 26-coordinate short-ideal
representation in characteristic two. This file applies the elementary
simple-head construction to its concrete highest short-root vector:
an invariant cyclic submodule is factored by a
maximal invariant submodule avoiding the chosen vector.  The quotient is an
actual irreducible rational representation, and the root and coroot equations
of the vector descend unchanged.

`ShortModule.Model` proves the highest-vector equations and the dimension
bound. Their assembly here yields the `(0,1)` end-node factor over every
algebraically closed field of characteristic two, with no uniqueness premise.

Sources: GLS3, Theorem 1.14.6(d), Example 1.14.9(c), and Definition 2.8.1(b).
-/

@[expose] public section
set_option maxHeartbeats 500000
set_option linter.style.haveILetI false
open scoped Classical
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.BinaryDegree.ExceptionalTensor

namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode

universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- A vector in the rational short-coordinate module satisfying the source
end-node equations. -/
def ShortBasicHighestVector
    (v : F4Chevalley.shortSubmodule (k := F)) : Prop :=
  v ≠ 0 ∧
    (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (F4Chevalley.shortRepresentation.action
        (algebraicRootElement r t) : Module.End F F4Chevalley.shortSubmodule) v = v) ∧
    (∀ (i : Fin 4) (t : Fˣ),
      (F4Chevalley.shortRepresentation.action
        (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
          Module.End F F4Chevalley.shortSubmodule) v =
        ((t : F) ^ basicCoefficient (0, 1) i) • v)

/-- Every supplied short-module end-node vector has an irreducible rational
quotient retaining its source highest-weight equations. -/
theorem exists_algebraicFactor_of_shortBasicHighestVector
    {v : F4Chevalley.shortSubmodule (k := F)}
    (hv : ShortBasicHighestVector (F := F) v) :
    ∃ C : AlgebraicFactor F,
      C.HasBasicHighestWeight (0, 1) ∧
        Module.finrank F C.Space ≤ Module.finrank F (F4Chevalley.shortSubmodule (k := F)) := by
  classical
  let V := F4Chevalley.shortSubmodule (k := F)
  let ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V :=
    F4Chevalley.shortRepresentation
  let U : Submodule F V :=
    sInf {W : Submodule F V | IsInvariantSubmodule ρ W ∧ v ∈ W}
  have hUInvariant : IsInvariantSubmodule ρ U := by
    intro g x hx
    exact Submodule.mem_sInf.2 fun W hW =>
      hW.1 g x (Submodule.mem_sInf.1 hx W hW)
  have hvU : v ∈ U := by
    apply Submodule.mem_sInf.2
    intro W hW
    exact hW.2
  letI : AddCommGroup U := inferInstance
  letI : Module F U := inferInstance
  obtain ⟨τ, hτRestrict, hτRational⟩ :=
    rationalRepresentation_restriction_exists ρ F4Chevalley.shortRepresentation_isRational U hUInvariant
  let vU : U := ⟨v, hvU⟩
  have hvU_basic :
      vU ≠ 0 ∧
      (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
        (τ.action (algebraicRootElement r t) : Module.End F U) vU = vU) ∧
      (∀ (i : Fin 4) (t : Fˣ),
        (τ.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
          Module.End F U) vU = ((t : F) ^ basicCoefficient (0, 1) i) • vU) := by
    refine ⟨?_, ?_, ?_⟩
    · intro hzero
      exact hv.1 (congrArg Subtype.val hzero)
    · intro r hr t
      apply Subtype.ext
      exact (hτRestrict (algebraicRootElement r t) vU).trans (hv.2.1 r hr t)
    · intro i t
      apply Subtype.ext
      exact (hτRestrict (algebraicCorootElement (typeF4SimpleRootIndex i) t) vU).trans
        (hv.2.2 i t)
  have hτCyclic : IsCyclicRepresentation τ vU := by
    intro Q hQInvariant hvQ
    apply top_unique
    intro y _
    let S : Submodule F V := Q.map U.subtype
    have hSInvariant : IsInvariantSubmodule ρ S := by
      intro g x hx
      rcases hx with ⟨q, hq, rfl⟩
      refine ⟨(τ.action g).1 q, hQInvariant g q hq, ?_⟩
      exact hτRestrict g q
    have hvS : v ∈ S := ⟨vU, hvQ, rfl⟩
    have hUS : U ≤ S := sInf_le ⟨hSInvariant, hvS⟩
    have hyS : y.1 ∈ S := hUS y.2
    obtain ⟨q, hq, hqy⟩ := hyS
    have hqeq : q = y := Subtype.ext hqy
    simpa [hqeq] using hq
  let Candidate : ℕ → Prop := fun n =>
    ∃ W : Submodule F U,
      IsInvariantSubmodule τ W ∧ vU ∉ W ∧ Module.finrank F W = n
  have hCandidateZero : Candidate 0 := by
    refine ⟨⊥, ?_, ?_, ?_⟩
    · intro g x hx
      change x = 0 at hx
      subst x
      simp
    · simpa using hvU_basic.1
    · simp
  let maximalRank := Nat.findGreatest Candidate (Module.finrank F U)
  have hCandidateMaximal : Candidate maximalRank := by
    exact Nat.findGreatest_spec (Nat.zero_le _) hCandidateZero
  obtain ⟨W, hWInvariant, hvW, hWrank⟩ := hCandidateMaximal
  have hWMaximal {S : Submodule F U}
      (hWS : W ≤ S) (hSInvariant : IsInvariantSubmodule τ S) (hvS : vU ∉ S) :
      S = W := by
    have hSCandidate : Candidate (Module.finrank F S) :=
      ⟨S, hSInvariant, hvS, rfl⟩
    have hSrankLe : Module.finrank F S ≤ maximalRank :=
      Nat.le_findGreatest (Submodule.finrank_le S) hSCandidate
    symm
    exact Submodule.eq_of_le_of_finrank_le (K := F) (V := U)
      (S₁ := W) (S₂ := S) hWS
      (by simpa only [hWrank] using hSrankLe)
  obtain ⟨σ, hσQuotient, hσRational⟩ :=
    rationalRepresentation_quotient_exists τ hτRational W hWInvariant
  have hσIrreducible : IsAlgebraicallyIrreducibleRepresentation σ := by
    intro Q hQInvariant
    let S : Submodule F U := Q.comap (W.mkQ : U →ₗ[F] U ⧸ W)
    have hSInvariant : IsInvariantSubmodule τ S := by
      intro g x hx
      have hact := hQInvariant g (W.mkQ x) hx
      change (σ.action g : Module.End F (U ⧸ W)) (Submodule.Quotient.mk x) ∈ Q at hact
      rw [hσQuotient g x] at hact
      exact hact
    have hWS : W ≤ S := by
      intro x hx
      change W.mkQ x ∈ Q
      change Submodule.Quotient.mk x ∈ Q
      rw [(Submodule.Quotient.mk_eq_zero W).2 hx]
      exact Q.zero_mem
    by_cases hqvQ : Submodule.Quotient.mk vU ∈ Q
    · right
      have hSTop : S = ⊤ := hτCyclic S hSInvariant hqvQ
      apply top_unique
      intro y _
      refine Submodule.Quotient.induction_on W y ?_
      intro x
      have hxS : x ∈ S := by rw [hSTop]; exact Submodule.mem_top
      exact hxS
    · left
      have hvS : vU ∉ S := by
        intro hvS
        exact hqvQ (by simpa [S] using hvS)
      have hSW : S = W := hWMaximal hWS hSInvariant hvS
      apply le_antisymm
      · intro y hy
        refine Submodule.Quotient.induction_on W y ?_ hy
        intro x hxQ
        have hxS : x ∈ S := hxQ
        rw [hSW] at hxS
        rw [(Submodule.Quotient.mk_eq_zero W).2 hxS]
        exact Submodule.zero_mem _
      · exact bot_le
  letI : Nontrivial (U ⧸ W) := by
    refine ⟨⟨Submodule.Quotient.mk vU, 0, ?_⟩⟩
    intro h
    exact hvW ((Submodule.Quotient.mk_eq_zero W).mp h)
  let C : AlgebraicFactor F :=
    { Space := U ⧸ W
      action := σ
      irreducible := ⟨hσRational, hσIrreducible⟩ }
  have hqvne : (Submodule.Quotient.mk vU : U ⧸ W) ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hvW
  have hvC : C.HasBasicHighestWeight (0, 1) := by
    let qv : C.Space := Submodule.Quotient.mk vU
    have hqvne' : qv ≠ 0 := by exact hqvne
    refine ⟨qv, hqvne', ?_, ?_⟩
    · intro r hr t
      rw [hσQuotient]
      change Submodule.Quotient.mk ((τ.action (algebraicRootElement r t)).1 vU) =
        Submodule.Quotient.mk vU
      exact congrArg Submodule.Quotient.mk (hvU_basic.2.1 r hr t)
    · intro i t
      rw [hσQuotient]
      change Submodule.Quotient.mk
          ((τ.action (algebraicCorootElement (typeF4SimpleRootIndex i) t)).1 vU) = _
      rw [hvU_basic.2.2 i t]
      exact Submodule.Quotient.mk_smul W _ _
  refine ⟨C, hvC, ?_⟩
  exact (Submodule.finrank_quotient_le W).trans (Submodule.finrank_le U)

/-- The concrete highest short-root coordinate supplies all end-node equations. -/
theorem shortModel_highestVector_isBasic :
    ShortBasicHighestVector (ShortModel.highestVector (F := F)) :=
  ⟨ShortModel.highestVector_ne_zero, ShortModel.highestVector_root,
    ShortModel.highestVector_coroot⟩

/-- A genuine rational irreducible end-node factor of dimension at most 26.
In particular, this applies over the algebraic closure of every finite field
of characteristic two. -/
theorem exists_small_endNode_algebraicFactor :
    ∃ C : AlgebraicFactor F,
      C.HasBasicHighestWeight (0, 1) ∧ Module.finrank F C.Space ≤ 26 := by
  obtain ⟨C, hC, hdim⟩ :=
    exists_algebraicFactor_of_shortBasicHighestVector
      (shortModel_highestVector_isBasic (F := F))
  exact ⟨C, hC, hdim.trans ShortModel.short_finrank⟩

end ReeF4.BinaryDegree.ExceptionalTensor.EndNode
