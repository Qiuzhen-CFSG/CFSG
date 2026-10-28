module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.Obstruction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.GoldschmidtAlternatives.Cases
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Classical components in the Goldschmidt–FF comparison

The PSL₂, SL₃/PSL₃ and SU₃/PSU₃ carriers in F.6.18 are quasisimple.
The actual PSL₂ image in PGL₂ has index two. For the field and graph
extensions, the defining embedding likewise has normal image of index two;
no splitting or assumption about the square of an outside lift is used.
Thus, when O₂(D) = 1, each of these models has quasisimple F*(D).

The final applications combine these facts with the obstruction for the full
B.5.6(3)–(5) product records on the actual offender-generated subgroup.
The source prime congruences, field degrees, and coefficient-field order p²
for unitary groups are retained. The alternating and covering alternatives
of rows (6) and (8) are left to the separate permutation comparison.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18(4)–(6),(8),(10)–(11), pp.309–310, and
15.4.18, p.1163. The imported linear simplicity and field-transport proofs
retain their ATLAS attribution and license.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace ProductComparison.ClassicalComponents
open GoldschmidtAlternatives

private theorem pslTwo_quasisimple (F : Type*) [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : IsQuasisimple PSL(2,F) := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hF
  refine { toIsPerfect := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
           simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq (GorensteinWalter.psl2_center_eq_bot F)).trans
    QuotientGroup.quotientBot).isSimpleGroup

private theorem slThree_quasisimple (F : Type*) [Field F] : IsQuasisimple SL(3,F) :=
  { toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }

private theorem pslThree_quasisimple (F : Type*) [Field F] : IsQuasisimple PSL(3,F) := by
  let := slThree_quasisimple F
  exact IsQuasisimple.of_surjective (QuotientGroup.mk' (center SL(3,F)))
    (QuotientGroup.mk'_surjective _)

variable {D : Type*} [Group D] [Finite D]

/-- The image supplied by the literal `ExtensionBy` predicate is F*.
Its normality comes from its index, without a complement. -/
theorem extensionBy_fitting {M : Type*} [Group M] [IsQuasisimple M]
    {a : MulAut M} (h : ExtensionBy D a) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨i, _, hi, hindex, _, _⟩ := h
  exact generalizedFitting_isQuasisimple_of_index_two i hi hindex hcore

omit [Finite D] in
/-- Every actual PSL₂(q) model for q ≥ 4 has quasisimple F*. -/
theorem pslTwo_fitting {q : ℕ} (hq : 4 ≤ q) (h : ClassicalGroup.IsPSL D 2 q) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := pslTwo_quasisimple F (by omega)
  let := IsQuasisimple.of_mulEquiv e.symm
  exact generalizedFitting_isQuasisimple_of_quasisimple

/-- The actual PSL₂ image in PGL₂ has index two in source row (5). -/
theorem pglTwo_fitting {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (h : PGLTwo D p) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := pslTwo_quasisimple F (by omega)
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpp : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hodd, by decide, by simpa using hF⟩
  let i : PSL(2,F) →* D := e.symm.toMonoidHom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL
  apply generalizedFitting_isQuasisimple_of_index_two i
    (e.symm.injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective) _ hcore
  change (e.symm.toMonoidHom.comp Matrix.ProjectiveSpecialLinearGroup.toPGL).range.index = 2
  rw [MonoidHom.range_comp]
  exact (Subgroup.index_map_equiv _ e.symm).trans
    (GorensteinWalter.pgl2_psl2Range_index_eq_two F hpp)

/-- The quadratic-field carrier and its actual Frobenius extension in row (8). -/
theorem fieldExtension_fitting {p : ℕ} (hp8 : p % 8 = 3)
    (h : FieldExtension D p) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨F, _, _, hF, _, _, hext⟩ := h
  have hp : 3 ≤ p := by omega
  let := pslTwo_quasisimple F (by nlinarith)
  exact extensionBy_fitting hext hcore

omit [Finite D] in
/-- Both the special and the projective degree-three linear carriers are quasisimple. -/
theorem linearThree_fitting {p : ℕ} (h : LinearThree D p) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨F, _, _, _, he⟩ := h
  rcases he with he | he
  · obtain ⟨e⟩ := he
    let := slThree_quasisimple F
    let := IsQuasisimple.of_mulEquiv e.symm
    exact generalizedFitting_isQuasisimple_of_quasisimple
  · obtain ⟨e⟩ := he
    let := pslThree_quasisimple F
    let := IsQuasisimple.of_mulEquiv e.symm
    exact generalizedFitting_isQuasisimple_of_quasisimple

private theorem unitary_fixed_card {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card {x : F // J.conj x = x} = p := by
  let : Fact p.Prime := ⟨hp⟩
  simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
    (by simpa using hF) (by simpa using hc)

omit [Finite D] in
/-- Both unitary carriers in row (10), over the coefficient field of order p². -/
theorem unitaryThree_fitting {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (h : UnitaryThree D p) : IsQuasisimple (generalizedFitting D) := by
  obtain ⟨F, _, _, J, hF, hc, he⟩ := h
  have hf := unitary_fixed_card J hp hF hc
  rcases he with he | he
  · obtain ⟨e⟩ := he
    let := J.special_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hf
    let := IsQuasisimple.of_mulEquiv e.symm
    exact generalizedFitting_isQuasisimple_of_quasisimple
  · obtain ⟨e⟩ := he
    let := J.projective_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hf
    let := IsQuasisimple.of_mulEquiv e.symm
    exact generalizedFitting_isQuasisimple_of_quasisimple

/-- Either graph extension of the actual SL₃ or PSL₃ carrier has quasisimple F*. -/
theorem linearGraphExtension_fitting {p : ℕ} (h : LinearGraphExtension D p)
    (hcore : pCore 2 D = ⊥) : IsQuasisimple (generalizedFitting D) := by
  obtain ⟨F, _, _, _, he⟩ := h
  rcases he with h | h
  · let := slThree_quasisimple F
    exact extensionBy_fitting h hcore
  · let := pslThree_quasisimple F
    exact extensionBy_fitting h hcore

/-- The unitary graph extensions use the same literal special/projective kernel. -/
theorem unitaryGraphExtension_fitting {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (h : UnitaryGraphExtension D p) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨F, _, _, J, hF, hc, _, he⟩ := h
  have hf := unitary_fixed_card J hp hF hc
  rcases he with h | h
  · let := J.special_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hf
    exact extensionBy_fitting h hcore
  · let := J.projective_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hf
    exact extensionBy_fitting h hcore

variable {G₁ G₂ : Subgroup D}

omit [Finite D] in
/-- F.6.18(4) has quasisimple generalized Fitting subgroup. -/
theorem case4_fitting (h : Case4 G₁ G₂) : IsQuasisimple (generalizedFitting D) := by
  obtain ⟨p, _, hp, hm, _⟩ := h
  exact pslTwo_fitting (by omega) hm

/-- F.6.18(5) has quasisimple generalized Fitting subgroup when O₂ = 1. -/
theorem case5_fitting (h : Case5 G₁ G₂) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨p, hp, hp24, hm, _⟩ := h
  exact pglTwo_fitting hp hp24 hm hcore

omit [Finite D] in
/-- Both signed degree-three alternatives of F.6.18(10). -/
theorem case10_fitting (h : Case10 G₁ G₂) : IsQuasisimple (generalizedFitting D) := by
  obtain ⟨p, hp, hm, _⟩ := h
  rcases hm with ⟨_, hl⟩ | ⟨hp8, hu⟩
  · exact linearThree_fitting hl
  · exact unitaryThree_fitting hp hp8 hu

/-- Both signed graph-extension alternatives of F.6.18(11). -/
theorem case11_fitting (h : Case11 G₁ G₂) (hcore : pCore 2 D = ⊥) :
    IsQuasisimple (generalizedFitting D) := by
  obtain ⟨p, hp, hm, _⟩ := h
  rcases hm with ⟨_, hl⟩ | ⟨hp8, hu⟩
  · exact linearGraphExtension_fitting hl hcore
  · exact unitaryGraphExtension_fitting hp hp8 hu hcore

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}
    (hb : Branch (ρ.comp (offenderSubgroup ρ).subtype))

include hb

/-- The full B.5.6 product branches exclude source row (4). -/
theorem not_case4 : ¬ Case4 G₁ G₂ :=
  fun h => branch_not_quasisimple ρ hb (case4_fitting h)

/-- The linear subcase of row (6), retaining the source prime-power parameters. -/
theorem not_linear_case6 : ¬ ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ e ≤ 2 ∧
    (p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) ∧ ClassicalGroup.IsPSL D 2 (p ^ e) := by
  rintro ⟨p, e, _, _, _, hpe, hm⟩
  exact branch_not_quasisimple ρ hb (pslTwo_fitting (by omega) hm)

/-- The full B.5.6 product records exclude both degree-three signs in row (10). -/
theorem not_case10 : ¬ Case10 G₁ G₂ :=
  fun hm => branch_not_quasisimple ρ hb (case10_fitting hm)

variable {K : GroupClass} (h : ClassifiedAction K ρ G₁ G₂)

include h

/-- Apply the PGL₂ calculation on the same classified actor and its actual two-core. -/
theorem not_case5 : ¬ Case5 G₁ G₂ :=
  fun hm => branch_not_quasisimple ρ hb (case5_fitting hm h.twoCore)

/-- The field-extension subcase of row (8), retaining its prime and congruence. -/
theorem not_field_case8 : ¬ ∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ FieldExtension D p := by
  rintro ⟨p, _, hp8, hm⟩
  exact branch_not_quasisimple ρ hb (fieldExtension_fitting hp8 hm h.twoCore)

/-- The literal classified action excludes both nonsplit graph-extension possibilities. -/
theorem not_case11 : ¬ Case11 G₁ G₂ :=
  fun hm => branch_not_quasisimple ρ hb (case11_fitting hm h.twoCore)

end ProductComparison.ClassicalComponents
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
