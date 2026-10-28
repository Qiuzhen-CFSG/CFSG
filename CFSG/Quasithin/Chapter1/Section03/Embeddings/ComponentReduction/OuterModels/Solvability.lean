module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.LinearTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.LinearUnitary
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.ExceptionalRankTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoFour.Adequate
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.HigmanSims
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# Full outer solvability for the complete Theorem C list

The actual inner--diagonal--field and graph calculations give solvable full
outer groups for the classical models. The other completed model calculations
give cyclic or two-group outer quotients. This uses their stronger conclusions,
not the weaker cyclic-normal odd-subgroup condition used in the Xi inspection.
Only full outer solvability of the actual Held and Rudvalis carriers remains an
explicit earlier model input. Their realization and normalizer producers are
retained by the complete outer-model assembly.

Perfect central descent embeds Out(Q) in Out(Q/Z(Q)). For the source application
Q=L/O(L), a perfect ambient actor therefore has trivial outer image. Lifting an
inner implementer through the actual odd-core quotient gives G=L C_G(Q).

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, Theorem C and
Remark A.2.4, p.33, and Proposition A.3.9, pp.45--46. This proves the model and
action implications; the full KnownSimple recognition and A.3.9 assembly remain
with their original owners.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels

open Subgroup Theory.GroupTheory ClassificationModels
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups

private theorem solvable_two_group {D : Type*} [Group D] [Finite D]
    (h : IsPGroup 2 D) : Group.IsSolvable D := by
  let := h.isNilpotent
  infer_instance

private theorem solvable_cyclic {D : Type*} [Group D] [IsCyclic D] :
    Group.IsSolvable D :=
  Group.isSolvable_of_comm IsCyclic.isMulCommutative.is_comm.comm

private theorem outer_transport {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (h : Group.IsSolvable (MulAut.Outer E)) :
    Group.IsSolvable (MulAut.Outer D) := by
  let := h
  exact MulAut.isSolvable_outer_of_mulEquiv e

private theorem alternating_outer_solvable (n : ℕ) (hn : 5 ≤ n) :
    Group.IsSolvable (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases h6 : n = 6
  · subst n
    exact AlternatingSix.ShadowLocal.outer_isSolvable
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  let : Group.IsSolvable (Equiv.Perm (Fin n) ⧸ A) :=
    solvable_two_group (IsPGroup.of_card hc)
  apply Group.isSolvable_of_surjective (f := MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨s, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn h6).surjective a
  exact ⟨QuotientGroup.mk' A s, rfl⟩

private theorem linear_two_even_outer_solvable {S : Type*} [Group S]
    (f : ℕ) (hS : ClassicalGroup.IsPSL S 2 (2 ^ f)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hS
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact outer_transport e
    (Theory.PSL2.OuterSolvable.outer_isSolvable_of_field_coverage
      BenderSuzuki.ZD.Linear.semilinear_coverage)

private theorem linear_two_odd_outer_solvable {S : Type*} [Group S]
    (p a : ℕ) (hp : p.Prime) (ho : Odd p) (hq : 4 ≤ p ^ a)
    (hS : ClassicalGroup.IsPSL S 2 (p ^ a)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hS
  let : Fintype F := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hchar : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    obtain ⟨k, hk⟩ := ho
    omega
  exact outer_transport e
    (Theory.PSL2.OuterSolvable.outer_isSolvable_of_semilinear_coverage
      (Theory.PSL2.OuterSolvable.odd_semilinear_coverage hchar (by omega)))

private theorem linear_three_outer_solvable {F : Type*} [Field F] [Finite F]
    (hcover : Matrix.PSL3.OuterSolvable.standard F = ⊤) :
    Group.IsSolvable (MulAut.Outer PSL(3, F)) := by
  let N := Matrix.PSL3.OuterSolvable.innerDiagonalOuter F
  let : N.Normal := Matrix.PSL3.OuterSolvable.innerDiagonalOuter_normal_of_coverage F hcover
  let : IsMulCommutative N := Matrix.PSL3.OuterSolvable.innerDiagonalOuter_isMulCommutative F
  let : IsMulCommutative (MulAut.Outer PSL(3, F) ⧸ N) :=
    Matrix.PSL3.OuterSolvable.outerDiagonalQuotient_isMulCommutative_of_coverage F hcover
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr
    ⟨Group.isSolvable_of_comm IsMulCommutative.is_comm.comm,
      Group.isSolvable_of_comm IsMulCommutative.is_comm.comm⟩

private theorem linear_three_even_model_outer_solvable {S : Type*} [Group S]
    (f : ℕ) (hf : 1 ≤ f) (hS : ClassicalGroup.IsPSL S 3 (2 ^ f)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hS
  exact outer_transport e (linear_three_outer_solvable
    (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hF))

private theorem linear_three_odd_model_outer_solvable {S : Type*} [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S]
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hS : ClassicalGroup.IsPSL S 3 p) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hS
  let : IsSimpleGroup PSL(3, F) := e.symm.isSimpleGroup
  let : Group.IsPerfect PSL(3, F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact outer_transport e (linear_three_outer_solvable
    (Matrix.PSL3.OuterSolvable.standard_eq_top_of_odd_prime_card F
      (Group.IsPerfect.not_isSolvable _) hp ho hF))

private theorem unitary_three_even_model_outer_solvable {S : Type*} [Group S]
    (f : ℕ) (hf : 2 ≤ f) (hS : ClassicalGroup.IsPSU S 3 (2 ^ f)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hS
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ f :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f (by omega) hcard hconj
  obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ f) hcard hfixed
  let J' := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  exact outer_transport (e.trans eJ)
    (J'.outer_isSolvable_of_semilinear_coverage rfl
      (J'.semilinear_coverage f hf rfl hcard hfixed))

private theorem unitary_three_odd_model_outer_solvable {S : Type*} [Group S]
    [IsSimpleGroup S] (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hS : ClassicalGroup.IsPSU S 3 p) : Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hS
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J p hcard hfixed
  let J' := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let eS := e.trans eJ
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J') := eS.symm.isSimpleGroup
  exact outer_transport eS
    (J'.outer_isSolvable_of_semilinear_coverage rfl
      (HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd
        J' rfl hp ho hcard hfixed))

private theorem symplectic_model_outer_solvable {S : Type*} [Group S]
    (f : ℕ) (hf : 2 ≤ f) (hS : ClassicalGroup.IsPSp S 2 (2 ^ f)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hS
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    have hfour : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    omega
  obtain ⟨N, hN, hcyc, hquot⟩ :=
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.outer_cyclic_normal_cyclic_quotient
      hlarge
      Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  let := hN
  let := hcyc
  let := hquot
  exact outer_transport
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨solvable_cyclic, solvable_cyclic⟩)

private theorem g2_model_outer_solvable {S : Type*} [Group S]
    (f : ℕ) (hf : 2 ≤ f) (hS : IsG2At S (2 ^ f)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hS
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    have hfour : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) hf
    omega
  let := g2_outer_isCyclic_of_coverage
    (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hlarge)
  exact outer_transport e solvable_cyclic

private theorem rank_two_outer_solvable {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] [Group.IsPerfect S] (hS : Section02.LocalModels.RankTwoTheoremC S) :
    Group.IsSolvable (MulAut.Outer S) := by
  cases hS with
  | linear f hf e => exact linear_three_even_model_outer_solvable f hf e
  | symplectic f hf e => exact symplectic_model_outer_solvable f hf e
  | g2 f hf e => exact g2_model_outer_solvable f hf e
  | triality f hf iso =>
      obtain ⟨P, hq, ⟨e⟩⟩ := iso
      let : IsSimpleGroup (Triality.Standard.Carrier P) := e.symm.isSimpleGroup
      let : Group.IsPerfect (Triality.Standard.Carrier P) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      let := Triality.Standard.OuterOdd.outer_isCyclic P f hf hq
      exact outer_transport e solvable_cyclic
  | ree m hm iso =>
      obtain ⟨d, ⟨e⟩⟩ := iso
      let : IsSimpleGroup d.fixedGroup := e.symm.isSimpleGroup
      let : Group.IsPerfect d.fixedGroup :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      let := ReeF4.LocalBlockInput.outer_isCyclic hm d
      exact outer_transport e solvable_cyclic
  | symplectic_derived iso =>
      obtain ⟨e⟩ := iso
      exact outer_transport
        (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
        AlternatingSix.ShadowLocal.outer_isSolvable
  | g2_derived iso =>
      obtain ⟨e⟩ := iso
      let := g2_derived_outer_isCyclic_of_coverage
        Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective
      exact outer_transport e solvable_cyclic
  | tits iso =>
      obtain ⟨e⟩ := iso
      exact outer_transport e (solvable_two_group Tits.OuterOddSubgroups.parrott_outer_isPGroup)

private theorem binary_linear_outer_solvable {S : Type*} [Group S]
    (n : ℕ) (hn : n = 4 ∨ n = 5) (hS : ClassicalGroup.IsPSL S n 2) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hS
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let := BinaryLinear.OuterCyclic.psl_outer_isCyclic hn
  exact outer_transport (e.trans (Atlas.fieldEquivPSL n eF)) solvable_cyclic

private theorem sporadic_outer_solvable
    (hHeld : IsSimpleGroup Held.He → Group.IsSolvable (MulAut.Outer Held.He))
    (hRu : IsSimpleGroup Rudvalis.Model → Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (n : SporadicName) (hne : n ≠ .j3) (e : S ≃* n.Carrier) :
    Group.IsSolvable (MulAut.Outer S) := by
  let : Finite n.Carrier := Finite.of_surjective e e.surjective
  cases n with
  | m11 => exact outer_transport e (solvable_two_group Sporadic.Mathieu.m11_outer_isPGroup_two)
  | m12 => exact outer_transport e (solvable_two_group
      (m12_outer_isPGroup_two_of_sylow_aut
        Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two))
  | m22 => exact outer_transport e (solvable_two_group
      (m22_outer_isPGroup_two_of_coverage Sporadic.Mathieu.m22DesignAutToAut_surjective))
  | m23 => exact outer_transport e (solvable_two_group Sporadic.Mathieu.m23_outer_isTwoGroup)
  | m24 => exact outer_transport e (solvable_two_group
      Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two)
  | j2 => exact outer_transport e (solvable_two_group JankoTwo.outer_isPGroup_two)
  | j3 => exact (hne rfl).elim
  | j4 =>
      let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
      let : Group.IsPerfect Janko4.Model :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      exact outer_transport e (solvable_two_group jankoFour_outer_isPGroup_two)
  | hs => exact outer_transport e (solvable_two_group
      (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow))
  | he => exact outer_transport e (hHeld e.symm.isSimpleGroup)
  | ru => exact outer_transport e (hRu e.symm.isSimpleGroup)

/-- Guarded full solvability for the complete Theorem C list. Simplicity of
the Held/Rudvalis carrier is transported from the actual source equivalence
only in its corresponding branch. -/
public theorem theoremC_outer_isSolvable_of_simple_model_inputs
    (hHeld : IsSimpleGroup Held.He → Group.IsSolvable (MulAut.Outer Held.He))
    (hRu : IsSimpleGroup Rudvalis.Model → Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hS : Section02.LocalModels.TheoremCModel S) :
    Group.IsSolvable (MulAut.Outer S) := by
  cases hS with
  | alternating n hn iso =>
      obtain ⟨e⟩ := iso
      exact outer_transport e (alternating_outer_solvable n hn.1)
  | linear_odd p a hp ho _ hq iso =>
      exact linear_two_odd_outer_solvable p a hp ho hq iso
  | three_odd p hp ho unitary iso =>
      cases unitary with
      | false => exact linear_three_odd_model_outer_solvable p hp ho iso
      | true => exact unitary_three_odd_model_outer_solvable p hp ho iso
  | rank_one iso =>
      cases iso with
      | linear f _ iso => exact linear_two_even_outer_solvable f iso
      | unitary f hf iso => exact unitary_three_even_model_outer_solvable f hf iso
      | suzuki m hm iso =>
          obtain ⟨e⟩ := iso
          let := suzuki_outer_isCyclic m hm
          exact outer_transport e solvable_cyclic
  | rank_two iso => exact rank_two_outer_solvable iso
  | binary_linear n hn iso => exact binary_linear_outer_solvable n hn iso
  | sporadic n hne iso =>
      obtain ⟨e⟩ := iso
      exact sporadic_outer_solvable hHeld hRu n hne e
  | janko_one iso =>
      obtain ⟨e⟩ := iso
      let := Janko1.OuterCertificate.outer_subsingleton
      exact outer_transport e inferInstance

/-- Full outer solvability for every constructor of the genuine Theorem C
model list. Only the two unfinished, concrete Held/Rudvalis model results
remain explicit; no general Schreier or classification premise is assumed. -/
public theorem theoremC_outer_isSolvable
    (hHeld : Group.IsSolvable (MulAut.Outer Held.He))
    (hRu : Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hS : Section02.LocalModels.TheoremCModel S) :
    Group.IsSolvable (MulAut.Outer S) := by
  exact theoremC_outer_isSolvable_of_simple_model_inputs (fun _ => hHeld) (fun _ => hRu) hS

/-- The guarded concrete-model conclusions pass through the literal center
quotient of a quasisimple group. -/
public theorem quasisimple_outer_isSolvable_of_theoremC_of_simple_model_inputs
    (hHeld : IsSimpleGroup Held.He → Group.IsSolvable (MulAut.Outer Held.He))
    (hRu : IsSimpleGroup Rudvalis.Model → Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hQ : Section02.LocalModels.TheoremCModel (Q ⧸ center Q)) :
    Group.IsSolvable (MulAut.Outer Q) := by
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _)
  let := theoremC_outer_isSolvable_of_simple_model_inputs hHeld hRu hQ
  exact Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (Q ⧸ center Q)))

/-- Full outer solvability passes to an actual finite quasisimple central
cover of any model in Theorem C. The inclusion of outer groups is induced
by the literal quotient by the center. -/
public theorem quasisimple_outer_isSolvable_of_theoremC
    (hHeld : Group.IsSolvable (MulAut.Outer Held.He))
    (hRu : Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hQ : Section02.LocalModels.TheoremCModel (Q ⧸ center Q)) :
    Group.IsSolvable (MulAut.Outer Q) := by
  exact quasisimple_outer_isSolvable_of_theoremC_of_simple_model_inputs (fun _ => hHeld) (fun _ => hRu) hQ

/-- Guarded model inputs supply the full outer-solvability step of A.3.9
for the original odd-core quotient and the original perfect actor. -/
public theorem perfect_actor_sup_oddCore_quotient_centralizer_of_simple_model_inputs
    (hHeld : IsSimpleGroup Held.He → Group.IsSolvable (MulAut.Outer Held.He))
    (hRu : IsSimpleGroup Rudvalis.Model → Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (L : Subgroup G) [L.Normal]
    (hQ : IsQuasisimple (L ⧸ pPrimeCore 2 L))
    (hmodel : Section02.LocalModels.TheoremCModel
      ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L))) :
    L ⊔ (normalQuotientAction L (pPrimeCore 2 L)).ker = ⊤ := by
  let Q := L ⧸ pPrimeCore 2 L
  let : IsQuasisimple Q := hQ
  let : Group.IsSolvable (MulAut.Outer Q) :=
    quasisimple_outer_isSolvable_of_theoremC_of_simple_model_inputs hHeld hRu hmodel
  let a := normalQuotientAction L (pPrimeCore 2 L)
  let f : G →* MulAut.Outer Q :=
    (QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp a
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf (g : G) : f g = 1 := congrArg f.range.subtype
    (hs.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1)
  apply top_unique
  intro g _
  have hi : a g ∈ MulAut.innerSubgroup Q := (QuotientGroup.eq_one_iff _).mp (hf g)
  obtain ⟨q, hq⟩ := hi
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) q
  have hl : a (l : G) = a g :=
    (normalQuotientAction_inner L (pPrimeCore 2 L) l).trans hq
  have hk : (l : G)⁻¹ * g ∈ a.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]
  have hm := (L ⊔ a.ker).mul_mem (mem_sup_left l.property) (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hm

/-- The literal perfect-actor step of A.3.9: every ambient element differs
from an element of L by an element centralizing L/O(L). The outer action
is proved trivial from full solvability, and its implementer is lifted
through the actual odd-core quotient. -/
public theorem perfect_actor_sup_oddCore_quotient_centralizer
    (hHeld : Group.IsSolvable (MulAut.Outer Held.He))
    (hRu : Group.IsSolvable (MulAut.Outer Rudvalis.Model))
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (L : Subgroup G) [L.Normal]
    (hQ : IsQuasisimple (L ⧸ pPrimeCore 2 L))
    (hmodel : Section02.LocalModels.TheoremCModel
      ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L))) :
    L ⊔ (normalQuotientAction L (pPrimeCore 2 L)).ker = ⊤ := by
  exact perfect_actor_sup_oddCore_quotient_centralizer_of_simple_model_inputs (fun _ => hHeld) (fun _ => hRu) L hQ hmodel


end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
