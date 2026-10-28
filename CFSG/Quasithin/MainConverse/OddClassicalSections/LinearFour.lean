module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.LinearFour.LeviSections
public import CFSG.Quasithin.MainConverse.AlternatingSections.SmallDegrees
public import Theory.SpecificGroups.PSL4Three.SectionReduction

/-!
# Proper-section reduction for PSL₄(3)

Coefficient transport identifies every `IsPSL G 4 3` witness with the
concrete matrix quotient over `ZMod 3`. Given a proved proper-overgroup
cover by the normal layers in `PSL4Three.HasSmallLayers`, a simple section
passes through the two solvable layers to GL₃(3), A₆, or PSp₄(3).
The GL₃(3) calculation is proved in `LeviSections`, and the A₆ calculation
is the proved `AlternatingSections.SmallDegrees` theorem.

The theorems below are conditional assembly lemmas. The intrinsic cover and
the PSp₄(3) section calculation are still explicit premises; this
module does not yet assert the unconditional PSL₄(3) proper-K theorem.
The quotient theorem uses normality inside the section subgroup V.

Source: Aschbacher–Smith, Theorem 0.1.2(4) and condition K, printed pp.4
and 482 of `refs/quasithin.pdf`.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

/-- The field witness is transported entrywise, then through the center quotient. -/
public noncomputable def psl4_three_equiv
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 4 3) :
    G ≃* Matrix.PSL4Three.PSL := by
  apply Classical.choice
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 3 :=
    (ZMod.ringEquivOfPrime F Nat.prime_three
      (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)⟩

private theorem section_of_isKGroup
    {H S : Type*} [Group H] [Group S] [IsSimpleGroup S]
    (hH : IsKGroup IsConstructedCarrier H)
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let := e.isSimpleGroup
  exact (hH.simple_quotient U f.ker).of_mulEquiv e.symm

private theorem smallLayers_simpleSection
    {H S : Type*} [Group H] [Group S] [IsSimpleGroup S]
    (hH : Matrix.PSL4Three.HasSmallLayers H)
    (hSp : IsKGroup IsConstructedCarrier Matrix.PSL4Three.PSp)
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  rcases hH with h | h | h
  · rcases h.simpleSection U f hf with hsolv | ⟨W, g, hg⟩
    · let := hsolv
      exact .cyclic (primeCyclic_of_solvable_simple S)
    · exact LinearFour.gl3_simpleSection_constructed (MonoidHom.id _) Function.injective_id
        W g hg
  · rcases h.simpleSection U f hf with hsolv | ⟨W, g, hg⟩
    · let := hsolv
      exact .cyclic (primeCyclic_of_solvable_simple S)
    · exact section_of_isKGroup
        (alternatingSix_isKGroup_constructed (MulEquiv.refl _)) W g hg
  · rcases h.simpleSection U f hf with hsolv | ⟨W, g, hg⟩
    · let := hsolv
      exact .cyclic (primeCyclic_of_solvable_simple S)
    · exact section_of_isKGroup hSp W g hg

private theorem concrete_proper_simpleSection
    (hcover : ∀ U : Subgroup Matrix.PSL4Three.PSL, U ≠ ⊤ →
      ∃ M : Subgroup Matrix.PSL4Three.PSL, U ≤ M ∧ Matrix.PSL4Three.HasSmallLayers M)
    (hSp : IsKGroup IsConstructedCarrier Matrix.PSL4Three.PSp)
    (U : Subgroup Matrix.PSL4Three.PSL) (hU : U ≠ ⊤)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  obtain ⟨M, hUM, hM⟩ := hcover U hU
  let j := Subgroup.inclusion hUM
  let e := MonoidHom.ofInjective (Subgroup.inclusion_injective hUM)
  exact smallLayers_simpleSection hM hSp j.range
    (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

/-- Conditional section assembly, including targets in another universe.
The two intrinsic input theorems must be supplied for the source result. -/
public theorem psl4_three_simpleSection_of_overgroups
    (hcover : ∀ U : Subgroup Matrix.PSL4Three.PSL, U ≠ ⊤ →
      ∃ M : Subgroup Matrix.PSL4Three.PSL, U ≤ M ∧ Matrix.PSL4Three.HasSmallLayers M)
    (hSp : IsKGroup IsConstructedCarrier Matrix.PSL4Three.PSp)
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 4 3)
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : V →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  let eG := psl4_three_equiv hG
  have hpU : U.map eG.toMonoidHom ≠ ⊤ := by
    intro h
    apply hU
    apply Subgroup.map_injective (f := eG.toMonoidHom) eG.injective
    rw [h, Subgroup.map_top_of_surjective _ eG.surjective]
  let j := eG.toMonoidHom.comp U.subtype
  have hj : Function.Injective j := eG.injective.comp U.subtype_injective
  have hpV : V.map j ≠ ⊤ := by
    intro h
    apply hpU
    apply top_unique
    rw [← h]
    rintro x ⟨v, _, rfl⟩
    exact ⟨v, v.property, rfl⟩
  let e := Subgroup.equivMapOfInjective V j hj
  exact concrete_proper_simpleSection hcover hSp (V.map j) hpV
    (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

/-- Conditional quotient assembly: `N.Normal` means normality in `V`. -/
public theorem psl4_three_simpleQuotient_of_overgroups
    (hcover : ∀ U : Subgroup Matrix.PSL4Three.PSL, U ≠ ⊤ →
      ∃ M : Subgroup Matrix.PSL4Three.PSL, U ≤ M ∧ Matrix.PSL4Three.HasSmallLayers M)
    (hSp : IsKGroup IsConstructedCarrier Matrix.PSL4Three.PSp)
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 4 3)
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    (N : Subgroup V) [N.Normal] [IsSimpleGroup (V ⧸ N)] :
    IsConstructedCarrier (V ⧸ N) :=
  psl4_three_simpleSection_of_overgroups hcover hSp hG U hU V
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Conditional proper-K assembly. The overgroup cover and the remaining
target-section theorem are not discharged by this implication. -/
public theorem psl4_three_properK_of_overgroups
    (hcover : ∀ U : Subgroup Matrix.PSL4Three.PSL, U ≠ ⊤ →
      ∃ M : Subgroup Matrix.PSL4Three.PSL, U ≤ M ∧ Matrix.PSL4Three.HasSmallLayers M)
    (hSp : IsKGroup IsConstructedCarrier Matrix.PSL4Three.PSp)
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 4 3) :
    HasProperKSubgroups IsConstructedCarrier G := by
  intro U hU S _ hS V f hf
  let := hS
  exact psl4_three_simpleSection_of_overgroups hcover hSp hG U hU V f hf

end CFSG.Quasithin.MainConverse
