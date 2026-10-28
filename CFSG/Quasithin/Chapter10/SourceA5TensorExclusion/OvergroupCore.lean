module

public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupCharacteristic

/-!
# The source tensor line lies in the overgroup two-core

Source 9.3.4 makes T₁ the actual Sylow subgroup of the overgroup. Its
central omega lies in the source line V₁. The nontrivial two-core meets
this omega subgroup, and the Cartan group's irreducibility on V₁ forces
all of V₁ into the two-core. The tensor centralizer bound and a central
involution then give characteristic two; fixed-freeness of the Cartan
actor forces the overgroup center to be trivial.

The earlier-source omega containment and Cartan action remain explicit.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 9.3.6, printed pp.733–734.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The source omega containment and irreducibility put V₁ in the actual core. -/
theorem source_a5_tensor_line_le_overgroup_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H U A : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hLH : L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hout : ¬ H ≤ D.maximalLocal)
    (hOmega : omegaCenterIn ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤ U)
    (hAH : A ≤ H) (hAU : A ≤ normalizer (U : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ U → A ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = U) : U ≤ H.pCoreIn 2 := by
  obtain ⟨P,hP⟩ := source_a5_local_outside_overgroup_sylow D e hn hcore hLH hRH hout
  apply pCoreIn_contains_irreducible_of_omegaCenter_le H _ U A
    ((pCoreIn_le_sylow H P).trans_eq hP) hRH
    (T.isPGroup'.to_le inf_le_left) ?_ hOmega hAH hAU hirr
  intro he
  exact hcore (((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp he)

/-- The source Cartan action and tensor line give all of source 9.3.6's
characteristic-two and center conclusions on the original overgroup. -/
theorem source_a5_outside_characteristicTwo_of_irreducible_tensor_line
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H U A : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hLH : L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hout : ¬ H ≤ D.maximalLocal)
    (hOmega : omegaCenterIn ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤ U)
    (hAH : A ≤ H) (hAU : A ≤ normalizer (U : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ U → A ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = U)
    (hfixed : U ⊓ centralizer (A : Set G) = ⊥)
    (hCT : (T : Subgroup G) ⊓ centralizer (componentOrbit U L : Set G) ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G))
    (z : G) (hz : orderOf z = 2) (hzU : z ∈ U)
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t) :
    U ≤ H.pCoreIn 2 ∧ H ∈ Chapter1.He G ∧
      generalizedFitting H = pCore 2 H ∧ center H = ⊥ := by
  have hU := source_a5_tensor_line_le_overgroup_core D e hn H U A hcore
    hLH hRH hout hOmega hAH hAU hirr
  obtain ⟨hHe,hfit⟩ := source_a5_outside_characteristicTwo_of_tensor_core D e hn H U
    hcore hLH hRH hout hU hCT z hz hzU hzc
  refine ⟨hU,hHe,hfit,?_⟩
  obtain ⟨P,hP⟩ := source_a5_local_outside_overgroup_sylow D e hn hcore hLH hRH hout
  exact center_eq_bot_of_omegaCenter_le_fixedFree H _ U A
    ((inf_centralizer_pCoreIn_le_iff 2 H).mpr (Chapter1.mem_He_iff.mp hHe))
    ((pCoreIn_le_sylow H P).trans_eq hP) hRH
    (T.isPGroup'.to_le inf_le_left) hOmega hAH hfixed

end CFSG.Quasithin.Chapter10
