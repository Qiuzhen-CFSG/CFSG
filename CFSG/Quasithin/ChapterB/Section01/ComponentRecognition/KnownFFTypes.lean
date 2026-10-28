module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The general known-group input to B.1.13

B.1.11 constructs the literal irreducible section I/C_I(L). Its overgroup H
normalizes L, so the faithful H-action image embeds in the full linear
normalizer of the L-action. Transporting the offender along that inclusion
proves the FF property for the full normalizer, with no SQTK hypothesis.

The kernel of L on this section is central, and its image is quasisimple.
Perfect centralizer lifting gives an actual equivalence between L/Z(L) and
the image modulo its center. The full known-simple catalogue therefore
applies to that image as well as to the original component quotient.
Perfectness excludes its prime-cyclic branch; every other catalogue branch
is retained explicitly. The component's intrinsic two-core is also trivial
when the ambient two-core is trivial.

These are proved reductions for the general recognition theorem, not that
theorem itself. The classical, exceptional and sporadic FF classification
branches, and the actual Lie-type identification of the original covering
component in the surviving branches, still require proofs. In particular,
no assertion about an arbitrary central extension is substituted for an
isomorphism to a concrete group of Lie type.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.1.11 and B.1.13, printed pp. 72–74 (PDF pp. 83–85).
B.1.13 cites Guralnick–Malle, *Classification of 2F-modules, II*, Table 2
(DOI 10.1515/9783110198126.117) for the remaining general classification.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The literal B.1.11 action extends as an FF-module to the full linear normalizer. -/
theorem centralSection_normalizer_isFF (L H : Subgroup G) (hLH : L ≤ H)
    (I : Submodule (ZMod 2) V) (hLI : L ≤ subspaceStabilizer ρ I)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G))
    (hff : IsFFModule (imageRepresentation
      (centralSectionRepresentation ρ L H I hHI hHN))) :
    IsFFModule (normalizerRepresentation (centralQuotientRepresentation ρ L I hLI)) := by
  have hn : (inclusion hLH).range.Normal := by
    rw [inclusion_range]
    exact (normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  exact isFFModule_linearNormalizer_of_normal_range
    (centralSectionRepresentation ρ L H I hHI hHN) (inclusion hLH) hff

/-- The kernel on an actual Irr⁺ quotient lies in the center of its quasisimple actor. -/
theorem centralQuotient_kernel_le_center (L : Subgroup G) [IsQuasisimple L]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) :
    (centralQuotientRepresentation ρ L I hI.choose).ker ≤ center L := by
  have hc := centralSection_kernel_le_centralizer ρ L L le_rfl I hI hI.choose
    (le_normalizer : L ≤ normalizer (L : Set G))
  intro l hl
  have hcent := (hc (mem_map_of_mem L.subtype hl)).2
  exact mem_center_iff.mpr fun k => Subtype.ext ((mem_centralizer_iff.mp hcent) k k.property)

/-- Instantiate the complete source K-group hypothesis on the actual simple quotient of L. -/
theorem component_quotient_known (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (L : Subgroup G) [IsQuasisimple L] : KnownSimple.IsKnownSimple (L ⧸ center L) :=
  hK _ IsQuasisimple.simple L (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _)

/-- The simple quotient of a quasisimple group cannot occupy the prime-cyclic catalogue row. -/
theorem quasisimple_quotient_not_cyclic (L : Type*) [Group L] [IsQuasisimple L] :
    ¬ KnownSimple.IsPrimeCyclicCarrier (L ⧸ center L) := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  rintro ⟨p, _, ⟨e⟩⟩
  apply Group.IsPerfect.not_isMulCommutative (L ⧸ center L)
  exact IsMulCommutative.of_comm fun a b => e.injective (by simp [mul_comm])

/-- A central section of a quasisimple actor has nontrivial action image. -/
theorem centralQuotient_actionImage_nontrivial (L : Subgroup G) [IsQuasisimple L]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) :
    Nontrivial (actionImage (centralQuotientRepresentation ρ L I hI.choose)) := by
  let σ := centralQuotientRepresentation ρ L I hI.choose
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  by_contra hs
  let : Subsingleton (actionImage σ) := not_nontrivial_iff_subsingleton.mp hs
  have hc : center L = ⊤ := by
    apply top_unique
    intro l _
    apply centralQuotient_kernel_le_center ρ L I hI
    have h := congrArg (imageRepresentation σ)
      (Subsingleton.elim (actionHom σ l) 1)
    change σ l = 1
    simpa only [imageRepresentation_actionHom, map_one] using h
  exact Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp hc)

/-- The actual action image of L on its Irr⁺ section remains quasisimple. -/
theorem centralQuotient_actionImage_quasisimple (L : Subgroup G) [IsQuasisimple L]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) :
    IsQuasisimple (actionImage (centralQuotientRepresentation ρ L I hI.choose)) := by
  let σ := centralQuotientRepresentation ρ L I hI.choose
  let := centralQuotient_actionImage_nontrivial ρ L I hI
  exact IsQuasisimple.of_surjective (actionHom σ) σ.asGroupHom.rangeRestrict_surjective

/-- The original component and its section image have genuinely isomorphic simple central quotients. -/
noncomputable def centralQuotient_simpleQuotientEquiv (L : Subgroup G) [IsQuasisimple L]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) :
    L ⧸ center L ≃*
      actionImage (centralQuotientRepresentation ρ L I hI.choose) ⧸
        center (actionImage (centralQuotientRepresentation ρ L I hI.choose)) := by
  let σ := centralQuotientRepresentation ρ L I hI.choose
  let f := actionHom σ
  have hf : Function.Surjective f := σ.asGroupHom.rangeRestrict_surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    apply centralQuotient_kernel_le_center ρ L I hI
    change σ l = 1
    simpa only [f, imageRepresentation_actionHom, map_one] using
      congrArg (imageRepresentation σ) (show f l = 1 from hl)
  have hc : (center (actionImage σ)).comap f = center L := by
    have he := comap_centralizer_map_eq_of_perfect f (⊤ : Subgroup L)
      (by simpa only [coe_top, centralizer_univ] using hk)
    simpa only [Subgroup.map_top_of_surjective f hf,
      coe_top, centralizer_univ] using he
  let q := (QuotientGroup.mk' (center (actionImage σ))).comp f
  have hq : q.ker = center L := by
    rw [show q.ker = (center (actionImage σ)).comap f by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']]
    exact hc
  exact (QuotientGroup.quotientMulEquivOfEq hq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hf))

/-- Apply the full concrete catalogue to the simple central quotient of the actual section image. -/
theorem centralQuotient_actionImage_known
    (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (L : Subgroup G) [IsQuasisimple L]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) :
    KnownSimple.IsKnownSimple
      (actionImage (centralQuotientRepresentation ρ L I hI.choose) ⧸
        center (actionImage (centralQuotientRepresentation ρ L I hI.choose))) :=
  (component_quotient_known hK L).of_mulEquiv
    (centralQuotient_simpleQuotientEquiv ρ L I hI).symm

/-- Ambient trivial two-core implies trivial intrinsic two-core for the subnormal component. -/
theorem component_twoCore_eq_bot [Finite G] (hcore : pCore 2 G = ⊥)
    (L : Subgroup G) (hL : IsComponent G L) : pCore 2 L = ⊥ := by
  rw [pCore_subnormal_eq_comap 2 hL.1, hcore, MonoidHom.comap_bot]
  exact (MonoidHom.ker_eq_bot_iff L.subtype).mpr L.subtype_injective

/-- Construct an Irr⁺ section with the full-normalizer FF property and central kernel, using B.1.11. -/
theorem exists_normalizer_ff_section [Finite G] [FiniteDimensional (ZMod 2) V]
    (hfaith : Function.Injective ρ) (L A : Subgroup G) [IsQuasisimple L]
    (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A) :
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I),
      IsFFModule (normalizerRepresentation (centralQuotientRepresentation ρ L I hI.choose)) ∧
      (centralQuotientRepresentation ρ L I hI.choose).ker ≤ center L ∧
      IsQuasisimple (actionImage (centralQuotientRepresentation ρ L I hI.choose)) := by
  obtain ⟨H, I, hLH, hI, hHI, hHN, hff, _⟩ :=
    source_lemma_B_1_11 ρ hfaith L A hLA hA
  exact ⟨I, hI, centralSection_normalizer_isFF ρ L H hLH I hI.choose hHI hHN hff,
    centralQuotient_kernel_le_center ρ L I hI,
    centralQuotient_actionImage_quasisimple ρ L I hI⟩

/-- Exhaust the full known-simple catalogue, eliminating only its impossible cyclic branch. -/
theorem known_component_quotient_cases (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (L : Subgroup G) [IsQuasisimple L] :
    (∃ m : ℕ, 5 ≤ m ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin m))) ∨
      KnownSimple.IsClassicalModel (L ⧸ center L) ∨
      KnownSimple.IsG2Carrier (L ⧸ center L) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        (L ⧸ center L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
      KnownSimple.IsExceptionalExtensionModel (L ⧸ center L) ∨
      Triality.Standard.IsTrialityGroup (L ⧸ center L) ∨
      ReeF4.IsReeF4Model (L ⧸ center L) ∨
      KnownSimple.IsSmallDerivedCarrier (L ⧸ center L) ∨
      KnownSimple.IsSporadicCarrier (L ⧸ center L) := by
  have hc := (component_quotient_known hK L).2.2
  cases hc with
  | cyclic h => exact (quasisimple_quotient_not_cyclic L h).elim
  | alternating m hm e => exact Or.inl ⟨m, hm, e⟩
  | classical h => exact Or.inr (Or.inl h)
  | g2 h => exact Or.inr (Or.inr (Or.inl h))
  | suzuki m hm e => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, e⟩)))
  | exceptional h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  | triality h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  | reeF4 h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  | smallDerived h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  | sporadic h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

/-- The actual source component supplies all structural inputs to the remaining
family recognition proofs. No recognition or covering conclusion is assumed. -/
theorem known_ff_reduction [Finite G] [FiniteDimensional (ZMod 2) V]
    (hK : IsKGroup KnownSimple.IsKnownSimple G) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (L A : Subgroup G) (hL : IsComponent G L)
    (hLA : ⁅L, A⁆ = L) (hA : IsBestOffender ρ A) :
    pCore 2 L = ⊥ ∧
      ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I),
        IsFFModule (normalizerRepresentation (centralQuotientRepresentation ρ L I hI.choose)) ∧
        (centralQuotientRepresentation ρ L I hI.choose).ker ≤ center L ∧
        IsQuasisimple (actionImage (centralQuotientRepresentation ρ L I hI.choose)) ∧
        KnownSimple.IsKnownSimple
          (actionImage (centralQuotientRepresentation ρ L I hI.choose) ⧸
            center (actionImage (centralQuotientRepresentation ρ L I hI.choose))) := by
  let := hL.2
  obtain ⟨I, hI, hff, hk, hq⟩ := exists_normalizer_ff_section ρ hfaith L A hLA hA
  exact ⟨component_twoCore_eq_bot hcore L hL, I, hI, hff, hk, hq,
    centralQuotient_actionImage_known ρ hK L I hI⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes
