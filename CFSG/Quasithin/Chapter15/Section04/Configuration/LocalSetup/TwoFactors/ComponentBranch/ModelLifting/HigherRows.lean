module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Sieve
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Classification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.StarKernel
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.ClassicalComponents
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ProductComparison.PermutationComponents
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover
public import Theory.GroupTheory.GeneralizedFitting.AutomorphismSimple

/-!
# Component carriers in the degree-three and Mathieu rows

Extract actual carrier equivalences for a component from the complete
F.6.18 rows (10)–(13). In row (10) the ambient quasisimple group is its
unique component. In row (11) the prescribed graph-extension embedding
has normal image of index two, which is the unique component even when
the extension is nonsplit. The Mathieu rows use simplicity and the actual
inner automorphism subgroup of Aut(M₁₂).

Linear carriers are transported to ZMod p. For unitary carriers the
prescribed Frobenius formula gives fixed-field order p, and the proved
PSU₃ simplicity theorem discharges the sieve's projective simplicity guard.
Both special and projective alternatives and their prime congruences are
retained. The underlying linear proofs and field transport retain the
attribution and license of the imported ATLAS ports.

The final application uses F.6.11 solvability and the literal map into
I/O_{3′}(I). Selection of these four rows remains explicit; exhaustive
selection and lifting back to the original component belong to the parent.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.18(10)–(13),
printed pp.309–310; the component paragraph of 15.4.18, pp.1162–1163.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.HigherRows
open FFBranch.ClassificationComparison GoldschmidtAlternatives

variable {D : Type*} [Group D] {A B Q : Subgroup D}

private theorem component_equiv_of_quasisimple
    {M : Type*} [Group M] [IsQuasisimple M]
    (hQ : IsComponent D Q) (e : D ≃* M) : Nonempty (Q ≃* M) := by
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple (⊤ : Subgroup D) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have htop : Q = ⊤ := hQ.eq_of_le ⟨.top, inferInstance⟩ le_top
  exact ⟨(MulEquiv.subgroupCongr htop).trans (topEquiv.trans e)⟩

private theorem component_equiv_of_simple
    {M : Type*} [Group M] [IsSimpleGroup M]
    (hQ : IsComponent D Q) (e : D ≃* M) : Nonempty (Q ≃* M) := by
  let : IsSimpleGroup D := e.isSimpleGroup
  let := hQ.2
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  have htop : Q = ⊤ :=
    (hQ.1.eq_bot_or_top_of_isSimpleGroup inferInstance).resolve_left
      ((nontrivial_iff_ne_bot Q).mp inferInstance)
  exact ⟨(MulEquiv.subgroupCongr htop).trans (topEquiv.trans e)⟩

private theorem component_equiv_of_extensionBy
    {M : Type*} [Group M] [IsQuasisimple M] {a : MulAut M}
    (hQ : IsComponent D Q) (h : ExtensionBy D a) : Nonempty (Q ≃* M) := by
  obtain ⟨i, _, hi, hindex, _, _⟩ := h
  let : i.range.Normal := normal_of_index_eq_two hindex
  let : IsQuasisimple i.range := IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hi)
  exact ⟨(MulEquiv.subgroupCongr (hQ.eq_of_index_two_quasisimple hindex)).trans
    (MonoidHom.ofInjective hi).symm⟩

private theorem slThree_quasisimple (F : Type*) [Field F] : IsQuasisimple SL(3,F) :=
  { toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }

private theorem pslThree_quasisimple (F : Type*) [Field F] : IsQuasisimple PSL(3,F) := by
  let := slThree_quasisimple F
  exact IsQuasisimple.of_surjective (QuotientGroup.mk' (center SL(3,F)))
    (QuotientGroup.mk'_surjective _)

private noncomputable def primeFieldEquiv {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) : F ≃+* ZMod p := by
  let := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F (Fact.out : p.Prime)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm

private theorem unitary_fixed_card {F : Type} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    Nat.card {x : F // J.conj x = x} = p := by
  let : Fact p.Prime := ⟨hp⟩
  simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
    (by simpa using hF) (by simpa using hc)

private theorem linear_model (hQ : IsComponent D Q) {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 5) (h : LinearThree D p) :
    IntrinsicComponentModel Q := by
  obtain ⟨F, _, _, hF, he⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let f := primeFieldEquiv hF
  rcases he with he | he
  · obtain ⟨e⟩ := he
    let := slThree_quasisimple F
    obtain ⟨eQ⟩ := component_equiv_of_quasisimple hQ e
    exact .linearSpecial p hp8 (eQ.trans (Atlas.fieldEquivSL 3 f))
  · obtain ⟨e⟩ := he
    let := pslThree_quasisimple F
    obtain ⟨eQ⟩ := component_equiv_of_quasisimple hQ e
    exact .linearProjective p hp8 (eQ.trans (Atlas.fieldEquivPSL 3 f))

private theorem unitary_model (hQ : IsComponent D Q) {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 3) (h : UnitaryThree D p) :
    IntrinsicComponentModel Q := by
  obtain ⟨F, _, _, J, hF, hc, he⟩ := h
  have hfix := unitary_fixed_card J hp hF hc
  have hs := BenderSuzuki.External.huppert_II_10_13 J p (by omega) hF hfix
  rcases he with he | he
  · obtain ⟨e⟩ := he
    let := J.special_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hfix
    obtain ⟨eQ⟩ := component_equiv_of_quasisimple hQ e
    exact .unitarySpecial J p hp hp8 hF hfix hs eQ
  · obtain ⟨e⟩ := he
    let := J.projective_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hfix
    obtain ⟨eQ⟩ := component_equiv_of_quasisimple hQ e
    exact .unitaryProjective J p hp hp8 hF hfix hs eQ

private theorem linear_graph_model (hQ : IsComponent D Q) {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 5) (h : LinearGraphExtension D p) :
    IntrinsicComponentModel Q := by
  obtain ⟨F, _, _, hF, he⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let f := primeFieldEquiv hF
  rcases he with h | h
  · let := slThree_quasisimple F
    obtain ⟨eQ⟩ := component_equiv_of_extensionBy hQ h
    exact .linearSpecial p hp8 (eQ.trans (Atlas.fieldEquivSL 3 f))
  · let := pslThree_quasisimple F
    obtain ⟨eQ⟩ := component_equiv_of_extensionBy hQ h
    exact .linearProjective p hp8 (eQ.trans (Atlas.fieldEquivPSL 3 f))

private theorem unitary_graph_model (hQ : IsComponent D Q) {p : ℕ}
    (hp : p.Prime) (hp8 : p % 8 = 3) (h : UnitaryGraphExtension D p) :
    IntrinsicComponentModel Q := by
  obtain ⟨F, _, _, J, hF, hc, _, he⟩ := h
  have hfix := unitary_fixed_card J hp hF hc
  have hs := BenderSuzuki.External.huppert_II_10_13 J p (by omega) hF hfix
  rcases he with h | h
  · let := J.special_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hfix
    obtain ⟨eQ⟩ := component_equiv_of_extensionBy hQ h
    exact .unitarySpecial J p hp hp8 hF hfix hs eQ
  · let := J.projective_isQuasisimple_of_fixed_card (by omega : 2 < p) hF hfix
    obtain ⟨eQ⟩ := component_equiv_of_extensionBy hQ h
    exact .unitaryProjective J p hp hp8 hF hfix hs eQ

/-- Row (10): identify the component with the actual signed degree-three carrier. -/
theorem case10 (hQ : IsComponent D Q) (h : Case10 A B) : IntrinsicComponentModel Q := by
  obtain ⟨p, hp, hm, _⟩ := h
  rcases hm with ⟨hp8, hl⟩ | ⟨hp8, hu⟩
  · exact linear_model hQ hp hp8 hl
  · exact unitary_model hQ hp hp8 hu

/-- Row (11): recover the special or projective carrier from its graph-extension image. -/
theorem case11 (hQ : IsComponent D Q) (h : Case11 A B) : IntrinsicComponentModel Q := by
  obtain ⟨p, hp, hm, _⟩ := h
  rcases hm with ⟨hp8, hl⟩ | ⟨hp8, hu⟩
  · exact linear_graph_model hQ hp hp8 hl
  · exact unitary_graph_model hQ hp hp8 hu

/-- Row (12): the component of the concrete M₁₂ model is M₁₂ itself. -/
theorem case12 (hQ : IsComponent D Q) (h : Case12 A B) : IntrinsicComponentModel Q := by
  let := Sporadic.Mathieu.m12_isSimpleGroup
  obtain ⟨e⟩ := h.1
  obtain ⟨eQ⟩ := component_equiv_of_simple hQ e
  exact .mathieuTwelve eQ

/-- Row (13): the component is the actual inner automorphism subgroup, hence M₁₂. -/
theorem case13 (hQ : IsComponent D Q) (h : Case13 A B) : IntrinsicComponentModel Q := by
  let := Sporadic.Mathieu.m12_isSimpleGroup
  obtain ⟨e⟩ := h.1
  obtain ⟨eQ⟩ := (hQ.map_equiv e).equiv_simple_of_automorphism Sporadic.Mathieu.m12_center_eq_bot
  exact .mathieuTwelve ((e.subgroupMap Q).trans eQ)

/-- The four higher rows discharge the intrinsic-model premise for a simple
component of a group with trivial two-core. The individual row lemmas above
in fact need neither of these last two restrictions. -/
theorem intrinsicModel (hQ : IsComponent D Q) (_hsimple : IsSimpleGroup Q)
    (_hcore : pCore 2 D = ⊥)
    (h : Case10 A B ∨ Case11 A B ∨ Case12 A B ∨ Case13 A B) :
    IntrinsicComponentModel Q := by
  rcases h with h | h | h | h
  · exact case10 hQ h
  · exact case11 hQ h
  · exact case12 hQ h
  · exact case13 hQ h

/-- Apply the row extraction to the literal star image of the original
component. F.6.11 supplies solvability of the actual kernel; no additional
simplicity, fixed-field, or carrier-classification premise is introduced. -/
theorem star_intrinsicModel {I : Type*} [Group I] [Finite I]
    {A B : Subgroup I} (triple : ChapterF.IsGoldschmidtTriple A B)
    (L : Subgroup I) (hL : IsComponent I L) (hodd : pPrimeCore 2 I = ⊥)
    (h : Case10 (threePrimeImage A) (threePrimeImage B) ∨
      Case11 (threePrimeImage A) (threePrimeImage B) ∨
      Case12 (threePrimeImage A) (threePrimeImage B) ∨
      Case13 (threePrimeImage A) (threePrimeImage B)) :
    IntrinsicComponentModel (threePrimeImage L) := by
  have hs := (f611Conclusion_of_goldschmidt triple).core_solvable
  obtain ⟨hc, hsimple⟩ := star_isComponent_and_simple L hL hodd hs
  exact intrinsicModel hc hsimple triple.primeToThreeCore_quotient_twoCore_eq_bot h

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.ModelLifting.HigherRows
