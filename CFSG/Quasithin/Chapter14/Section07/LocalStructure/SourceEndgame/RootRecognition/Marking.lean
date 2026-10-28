module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RuRecords

/-!
# The original alternating marking in 14.7.73

Restrict the original H → S₅ map to K = O²(H), and use the inverse of the
marking already attached to the natural U/U₀ module. The resulting surjection
onto SL₂(4) has kernel O₂(K), since K is normal in H. This does not identify
O₂(K) with O₂(H). Once 14.7.72 gives U₀ = V₁, the same coordinates give the
natural K-section U/V₁ and the order |U| = 32.

Source: Aschbacher–Smith, 14.7.73, printed pp.1076–1077, manuscript of
1 March 2004. These markings are used by the original-root quotient proof.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition
open Chapter12.Section08 CriticalFusion.Source

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The original L-conjugate span, without replacing it by its later core identification. -/
def S (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G :=
  conjugateSpanBy F.U L

/-- The original intersection, using right conjugation. -/
def E (L : Subgroup G) (F : InvariantFlag T V 3) (k : K F) : Subgroup G :=
  S L F ⊓ (S L F).conjBy ((k : G)⁻¹)

/-- The source product candidate, before proving it is the two-core. -/
def P₀ (L : Subgroup G) (F : InvariantFlag T V 3) (k : K F) : Subgroup G :=
  (S L F ⊓ F.H.pCoreIn 2) ⊔ ((S L F).conjBy ((k : G)⁻¹) ⊓ F.H.pCoreIn 2)

omit [Finite G] in
theorem K_core_eq_intersection : (K F).pCoreIn 2 = K F ⊓ F.H.pCoreIn 2 := by
  apply le_antisymm
  · exact le_inf (pCoreIn_le 2 _) (pCoreIn_mono_of_normalizes
      (K_le_H F) (H_normalizes_K F))
  · apply le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 F.H).of_injective (inclusion inf_le_right)
        (inclusion_injective _)) inf_le_left
    exact (le_inf (K F).le_normalizer ((K_le_H F).trans
      (F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)))).trans
        inf_normalizer_le_normalizer_inf

variable (d : Data T L V F W)

/-- K maps into the alternating group under the original H-marking. -/
def alternatingMap : K F →* alternatingGroup (Fin 5) :=
  (d.qH.comp (inclusion (K_le_H F))).codRestrict _ (fun k => by
    rw [← d.K_image]
    exact mem_map_of_mem d.qH k.property)

theorem alternatingMap_surjective : Function.Surjective (alternatingMap d) := by
  intro a
  have ha := d.K_image.ge a.property
  obtain ⟨h, hh, he⟩ := ha
  exact ⟨⟨h, hh⟩, Subtype.ext he⟩

/-- No new natural-module marking is chosen. -/
def qK : K F →* SL2FourNatural.SL :=
  d.naturalQuotient.marking.symm.toMonoidHom.comp (alternatingMap d)

theorem qK_surjective : Function.Surjective (qK d) :=
  d.naturalQuotient.marking.symm.surjective.comp (alternatingMap_surjective d)

theorem qK_marking (k : K F) :
    d.qH ⟨k, K_le_H F k.property⟩ = alternatingActor d.naturalQuotient (qK d k) := by
  exact (congrArg Subtype.val (d.naturalQuotient.marking.apply_symm_apply
    (alternatingMap d k))).symm

theorem qK_ker : (qK d).ker = ((K F).pCoreIn 2).subgroupOf (K F) := by
  ext k
  change d.naturalQuotient.marking.symm (alternatingMap d k) = 1 ↔ _
  rw [← d.naturalQuotient.marking.symm.map_one,
    d.naturalQuotient.marking.symm.injective.eq_iff, Subtype.ext_iff]
  change d.qH ⟨k, K_le_H F k.property⟩ = 1 ↔ (k : G) ∈ (K F).pCoreIn 2
  rw [← MonoidHom.mem_ker, d.qH_ker, K_core_eq_intersection]
  exact ⟨fun h => ⟨k.property, h⟩, fun h => h.2⟩

theorem qK_ker_isPGroup : IsPGroup 2 (qK d).ker := by
  rw [qK_ker]
  exact (isPGroup_pCoreIn 2 (K F)).comap_subtype

theorem U_card (hpoint : d.U₀ = F.Vi 1) : Nat.card F.U = 32 := by
  have h := (source_natural_U_section d hpoint).card_section
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  rw [hp, show Nat.card ChapterJ.FourSpace = 16 by
    rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]] at h
  exact h

/-- Restrict the genuine natural U/V₁ section to the original K. -/
def natural_U_section (hpoint : d.U₀ = F.Vi 1) (hUK : F.U ≤ K F) :
    BinaryConjugationSection (K F) F.U (F.Vi 1)
      (SL2FourNatural.naturalRepresentation.comp (qK d)) where
  section_le := hUK
  kernel_le := d.conjugationSection.kernel_le
  normalized := (K_le_H F).trans d.conjugationSection.normalized
  coordinates := (source_natural_U_section d hpoint).coordinates
  onto := (source_natural_U_section d hpoint).onto
  kernel_eq := (source_natural_U_section d hpoint).kernel_eq
  equivariant k x := by
    have h := (source_natural_U_section d hpoint).equivariant
      ⟨k, K_le_H F k.property⟩ x
    refine h.trans ?_
    change d.naturalQuotient.action (d.qH ⟨k, K_le_H F k.property⟩) _ = _
    rw [qK_marking]
    exact d.naturalQuotient.restriction _ _

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition
