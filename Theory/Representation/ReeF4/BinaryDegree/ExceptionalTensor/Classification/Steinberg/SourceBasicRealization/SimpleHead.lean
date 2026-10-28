module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible

/-!
# Simple heads retaining actual F4 highest vectors

A nonzero vector in a finite-dimensional rational action generates an
invariant cyclic submodule. Quotient by an invariant submodule of maximal
rank avoiding that vector. Cyclicity makes the resulting nonzero rational
quotient irreducible, while its literal root and coroot equations descend.
This generalizes the short end-node construction to arbitrary source weights
and is used for the alternating tensor and its tensor with the end-node factor.

Source: GLS3 Section 1.14; the cyclic simple-head proof in
`BasicMinimum.EndNode.ShortModule`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- The source equations for a vector before taking a simple quotient. -/
def HighestVector (ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V)
    (a : Weight) (v : V) : Prop :=
  v ≠ 0 ∧
    (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (ρ.action (algebraicRootElement r t) : Module.End F V) v = v) ∧
    (∀ (i : Fin 4) (t : Fˣ),
      (ρ.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) : Module.End F V) v =
        ((t : F) ^ a i) • v)

/-- A rational simple head preserves the nonzero highest vector and its exact weight. -/
theorem exists_factor_of_highestVector
    (ρ : RationalRepresentation (F4Chevalley.Carrier (k := F)) V)
    (hρ : IsRationalRepresentation ρ) {a : Weight} {v : V}
    (hv : HighestVector ρ a v) :
    ∃ C : AlgebraicFactor F, HasHighestWeight C a ∧
      Module.finrank F C.Space ≤ Module.finrank F V := by
  classical
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
  obtain ⟨τ, hτRestrict, hτRational⟩ :=
    rationalRepresentation_restriction_exists ρ hρ U hUInvariant
  let vU : U := ⟨v, hvU⟩
  have hvU_basic :
      vU ≠ 0 ∧
      (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
        (τ.action (algebraicRootElement r t) : Module.End F U) vU = vU) ∧
      (∀ (i : Fin 4) (t : Fˣ),
        (τ.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
          Module.End F U) vU = ((t : F) ^ a i) • vU) := by
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
  let : Nontrivial (U ⧸ W) := by
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
  have hvC : HasHighestWeight C a := by
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

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization
