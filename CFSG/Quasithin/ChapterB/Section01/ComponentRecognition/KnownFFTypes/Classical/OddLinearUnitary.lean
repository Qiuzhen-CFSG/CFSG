module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.Restrictions
public import Theory.SpecificGroups.ClassicalUnitary.OddRankOneComparison
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.Representation.BinaryOffender.CentralKernelImage

/-!
# Odd-field linear and unitary quotients in B.1.13

The four exceptional simple quotients are identified with actual carriers:
PSL₂(5) with A₅, PSL₂(7) with PSL₃(2), PSL₂(9) with A₆, and PSU₃(3) with
G₂(2)′. The PSU₂ comparison works over every odd prime power and every
Hermitian form in the catalogue, retaining its projective kernel.

The remaining assembly is conditional on the two numerical representation
restrictions in `OddLinearUnitary.Restrictions`. It passes to the faithful
image without changing the full normalizer or the central quotient. Thus the
original action need only have central kernel. No assertion about F* of the
full normalizer, or containment of an offender in the original image, is used.
The numerical restrictions themselves are not proved in this module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.13,
B.4.4 and K.2, printed pp.73–74, 87 and 453. The concrete comparisons reuse
the attributed ATLAS ports and `SU3.BinaryG2Comparison`.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical

universe u v
variable {L : Type u} [Group L]

/-- The three exceptional odd PSL₂ parameters have the required actual
alternating or characteristic-two simple quotient, without any covering claim. -/
theorem quotientAlternative_of_psl2_small_odd {q : ℕ}
    (hq : q = 5 ∨ q = 7 ∨ q = 9)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) : QuotientAlternative L := by
  obtain rfl | rfl | rfl := hq
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : Fintype F := Fintype.ofFinite F
    let f : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
    exact Or.inr ⟨5, by decide,
      ⟨(e.trans (Atlas.fieldEquivPSL 2 f)).trans
        Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩⟩
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    have hp : KnownSimple.LinearParameters 3 2 :=
      ⟨(isPrimePow_nat_iff 2).mpr ⟨2, 1, by decide, by decide, by decide⟩,
        by decide, by omega⟩
    exact Or.inl (.classical 2 (by decide) (.linear 3 hp
      ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
        ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hc)⟩⟩))
  · obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    exact Or.inr ⟨6, by decide,
      ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hc)⟩⟩

/-- The exceptional PSU₃(3) quotient is the actual derived binary G₂ carrier. -/
theorem quotientAlternative_of_psu3_three
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 3 3) : QuotientAlternative L := by
  obtain ⟨F, _, _, J, hc, hj, ⟨e⟩⟩ := h
  exact Or.inl (.g2Derived ⟨e.trans (J.projectiveEquivBinaryG2Derived hc hj)⟩)

/-- Every odd-field dimension-two unitary catalogue model is an actual
PSL₂ model over the fixed field of its original stored involution. -/
theorem isPSL_two_of_isPSU_two_odd {q : ℕ} (hq : IsPrimePow q) (ho : Odd q)
    {S : Type u} [Group S] (h : ClassicalGroup.IsPSU S 2 q) :
    ClassicalGroup.IsPSL S 2 q := by
  obtain ⟨F, _, _, J, hc, hj, ⟨e⟩⟩ := h
  have hk := J.fixed_card_prime_power hq hc hj
  obtain ⟨ep⟩ := J.nonempty_projectiveTwoEquiv_odd hq ho hc hj
  exact ⟨FixedBy.subfield F J.conj, inferInstance, inferInstance, hk, ⟨e.trans ep⟩⟩

/-- In particular every small odd dimension-two unitary alias is recognized. -/
theorem quotientAlternative_of_psu2_small_odd {q : ℕ}
    (hp : KnownSimple.UnitaryParameters 2 q) (ho : Odd q)
    (hq : q = 5 ∨ q = 7 ∨ q = 9)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 2 q) : QuotientAlternative L :=
  quotientAlternative_of_psl2_small_odd hq (isPSL_two_of_isPSU_two_odd hp.1 ho h)

variable [Finite L] [IsQuasisimple L]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) L W)

/-- Conditional linear assembly. The representation restriction is applied to
the faithful image; its numerical output identifies the original quotient. -/
theorem quotientAlternative_of_odd_psl_of_restriction
    (hc : OddLinearUnitary.LinearRestriction.{v})
    (hi : σ.IsIrreducible) (hk : σ.ker ≤ center L)
    (hff : IsFFModule (normalizerRepresentation σ))
    {n q : ℕ} (hp : KnownSimple.LinearParameters n q) (ho : Odd q)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) n q) : QuotientAlternative L := by
  let : IsQuasisimple (actionImage σ) := actionImage_quasisimple_of_central_kernel σ hk
  obtain ⟨hn, hq⟩ := hc (imageRepresentation σ) (imageRepresentation_injective σ)
    (imageRepresentation_isIrreducible σ hi)
    ((isFFModule_normalizer_imageRepresentation_iff σ).mpr hff) hp ho
    (h.of_mulEquiv (simpleQuotientEquivImage σ hk).symm)
  exact quotientAlternative_of_psl2_small_odd hq (hn ▸ h)

/-- Conditional unitary assembly, including all dimension-two aliases.
The unitary restriction is used only in dimensions at least three. -/
theorem quotientAlternative_of_odd_psu_of_restrictions
    (hl : OddLinearUnitary.LinearRestriction.{v})
    (hu : OddLinearUnitary.UnitaryRestriction.{v})
    (hi : σ.IsIrreducible) (hk : σ.ker ≤ center L)
    (hff : IsFFModule (normalizerRepresentation σ))
    {n q : ℕ} (hp : KnownSimple.UnitaryParameters n q) (ho : Odd q)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) n q) : QuotientAlternative L := by
  by_cases hn : n = 2
  · subst n
    exact quotientAlternative_of_odd_psl_of_restriction σ hl hi hk hff
      ⟨hp.1, hp.2.1, hp.2.2.1⟩ ho (isPSL_two_of_isPSU_two_odd hp.1 ho h)
  · have hn3 : 3 ≤ n := by have := hp.2.1; omega
    let : IsQuasisimple (actionImage σ) := actionImage_quasisimple_of_central_kernel σ hk
    obtain ⟨hn, hq⟩ := hu (imageRepresentation σ) (imageRepresentation_injective σ)
      (imageRepresentation_isIrreducible σ hi)
      ((isFFModule_normalizer_imageRepresentation_iff σ).mpr hff) hp hn3 ho
      (h.of_mulEquiv (simpleQuotientEquivImage σ hk).symm)
    apply quotientAlternative_of_psu3_three
    simpa only [hn, hq] using h

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
