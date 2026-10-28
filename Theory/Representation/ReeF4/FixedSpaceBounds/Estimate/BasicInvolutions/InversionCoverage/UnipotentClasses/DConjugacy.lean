module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Reduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Middle
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression

/-!
# Assembly of root conjugacy for involutions in the Ree D section

Every nonidentity square-one element of the literal subgroup
D = Y₁X₂X₃X₄X₅X₆Y₇ is conjugate to a nonzero point of y₅ or x₄.
Supported factorization and the proved D-to-D₂ transport first place it in
the elementary five-coordinate tail. Tail compression and the middle-tail
conjugators then reach the two root curves. All conjugators lie in the
actual fixed Ree model; no class count or classification premise is used.

Source: GLS3 Table 2.4, 2.4.5(d), and Lemma 3.3.9; Guralnick--Malle,
*Classification of 2F-modules, II*, Lemma 8.8, internal p.57.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
open EvenInvolutionGeometry ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent

/-- The two literal coordinate transports imply D involution coverage.
The middle-tail root conjugators are constructed in `Middle`. -/
theorem dConjugacy_of_transports (m : ℕ) (hm : 1 ≤ m)
    (hD : DConjugacy.TransportToD₂ m) (hT : DConjugacy.CompressTail m) :
    DConjugacy m := by
  intro x hx hne hsq
  obtain ⟨p, hp, rfl⟩ := (sectionFacts m hm).support_D x hx
  obtain ⟨g, q, hq, hg⟩ := hD p hp hsq
  have hsq' : wordElement m q ^ 2 = 1 := by
    rw [← hg, ← MulAut.conj_apply]
    rw [← map_pow, hsq, map_one]
  obtain ⟨v, hv⟩ := (DConjugacy.mem_D₂_and_sq_iff m hm (wordElement m q)).mp
    ⟨wordElement_mem_D₂ m q hq, hsq'⟩
  have h1 : IsConj (wordElement m p) (tailElement m v) :=
    isConj_iff.mpr ⟨g, hg.trans hv.symm⟩
  obtain ⟨k, b, c, e, hk⟩ := hT v
  have h2 : IsConj (tailElement m v) (tailElement m ![0, b, c, 0, e]) :=
    isConj_iff.mpr ⟨k, hk⟩
  have hconj := h1.trans h2
  have hne' : tailElement m ![0, b, c, 0, e] ≠ 1 := by
    intro he
    obtain ⟨a, ha⟩ := isConj_iff.mp hconj
    exact hne ((MulAut.conj a).injective (ha.trans (he.trans (map_one _).symm)))
  rcases DConjugacy.root_classes_middle m b c e hne' with ⟨a, ha, hc⟩ | ⟨a, ha, hc⟩
  · exact Or.inl ⟨a, ha, hc.trans hconj.symm⟩
  · exact Or.inr ⟨a, ha, hc.trans hconj.symm⟩

/-- Every involution in the literal D section lies in one of the two root
classes. Both coordinate transports are discharged by their explicit
fixed-model conjugators. -/
theorem dConjugacy (m : ℕ) (hm : 1 ≤ m) : DConjugacy m :=
  dConjugacy_of_transports m hm
    (DConjugacy.transportToD₂ m hm) (DConjugacy.compressTail m hm)

/-- The D-section conclusion with an ambient conjugator and its literal
split-root word. The nonzero parameter rules out the identity on either curve. -/
theorem exists_conjugator_to_rootWord_of_mem_D (m : ℕ) (hm : 1 ≤ m)
    (x : Model m) (hx : x ∈ ElementaryTwoBound.D m) (hne : x ≠ 1)
    (hsq : x ^ 2 = 1) :
    ∃ (g : Model m) (a : CoefficientField m), a ≠ 0 ∧
      (toSplitGroup m (g * x * g⁻¹) =
          Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.centralWord m 4 a ∨
        toSplitGroup m (g * x * g⁻¹) =
          Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.rootWord m 3 a) := by
  rcases dConjugacy m hm x hx hne hsq with ⟨a, ha, h⟩ | ⟨a, ha, h⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp h.symm
    exact ⟨g, a, ha, Or.inl ((congrArg (toSplitGroup m) hg).trans
      (longRootElement_coe m a))⟩
  · obtain ⟨g, hg⟩ := isConj_iff.mp h.symm
    exact ⟨g, a, ha, Or.inr ((congrArg (toSplitGroup m) hg).trans
      (shortRootElement_coe m a))⟩

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
