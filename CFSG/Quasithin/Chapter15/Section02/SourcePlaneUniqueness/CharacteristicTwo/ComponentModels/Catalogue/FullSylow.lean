module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Preparation
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.FullSylowBlocks

/-!
# Normalizing the actual escaping component in 15.2.23

Apply C.2.4(1) inside the original I to R = O₂(M ∩ I). The full Sylow
intersection makes R Sylow in the component join, even when R permutes
components. The C.1.29 ordered chi-zero product then makes an escaping
component a chi-zero block. The independent no-chi conclusion excludes
this alternative of C.2.4(2), so R normalizes the same component already
normalized by K = O²(H).

The source S₃ action and no-chi conclusion remain explicit. Their source
constructions belong respectively to this component/Omega family and
`qt-e-152-char2-block-exclusion`; `qt-e-152-plane-uniqueness` retains final
discharge of the earlier plane premises. No radical-normalization or
full-Sylow block implication remains as an input to the selection theorem.

Source: Aschbacher--Smith, C.2.4(1), printed p.144, and 15.2.23,
printed p.1116, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open ComponentCatalogue
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

include hsource in
/-- C.2.4(1) on the literal subgroup of I, without assuming that R acts on X. -/
theorem intersection_fullSylowBlocks (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2) : FullSylowBlocks M I := by
  have hs := intersection_pushingUpSetup (hsource := hsource) hI hcore
  have ho : pPrimeCore 2 I = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  intro X hX hq hf hout hsy
  let := hq
  obtain ⟨P,hP⟩ := hsy
  have hb := ChapterC.CatalogueFullSylow.constrained_component_chiZero_of_full_sylow
    hs.sqtk (((M ⊓ I).pCoreIn 2).subgroupOf I) ((M ⊓ I).subgroupOf I) X
    hs.radical hs.characteristic_control hX ho hf hout P (hP.le.trans inf_le_left)
  exact ⟨⟨inferInstance,hb.chi.short,hX.subnormal⟩,hb⟩

include hsource in
/-- Eliminate the full-Sylow alternative for this selected component. -/
theorem component_normalized_of_no_chi (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (s : Selected H M I X) : Normalized H M I X :=
  component_normalized_of_fullSylow_blocks (hsource := hsource) hI hfit hcore
    (intersection_fullSylowBlocks (hsource := hsource) hI hfit hcore) hno s

variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original escaping component is normalized by both O²(H) and O₂(NI).
The S₃ map has exactly the original V-centralizer as kernel. -/
theorem escaping_normalized_component_of_symmetricThree
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y) :
    ∃ X : Subgroup G, Normalized H M I X := by
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  exact d.escaping_normalized_component_of_fullSylow_blocks hI hfit f hf hker hno
    (intersection_fullSylowBlocks (hsource := hsource) hI hfit hcore)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
