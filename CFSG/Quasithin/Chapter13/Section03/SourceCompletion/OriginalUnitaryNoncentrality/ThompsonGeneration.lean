module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.SourceComponentGeometry
public import CFSG.Quasithin.Chapter3.Section02.SourceComponentThompson

/-!
# Thompson generation of the actual unitary moved component

The flag point lies in the Sylow omega-center. Its full normalizer
normalizes the selected component, so the omega-center centralizer does
also. The two distinct maximal normalizers supply the outside-local
witness for the genuine Chapter 3 theorem. This gives the literal
commutator needed before the B.5 module analysis.

Source: Aschbacher--Smith 13.3.14 following (f), printed p.892.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

/-- The original normalizer geometry supplies every Chapter 3 premise. -/
theorem unitary_component_thompson_generation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (Z H M : Subgroup G) (hZT : Z ≤ (T : Subgroup G)) (hZ : Nat.card Z = 2)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hH : H = normalizer (Z : Set G))
    (K : Subgroup H) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T)
    (hstar : K.map H.subtype ∈ Chapter1.LStar G T)
    (hHN : H ≤ normalizer (K.map H.subtype : Set G))
    (hN : IsMaximalTwoLocal (normalizer (K.map H.subtype : Set G)))
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hKM : ¬ K.map H.subtype ≤ M) :
    ⁅K.map H.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K.map H.subtype := by
  let A := K.map H.subtype
  have hTO : Z ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    intro z hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hZT hz,?_,?_⟩
    · have he : (⟨z,hz⟩ : Z) ^ 2 = 1 := by
        rw [←hZ]
        exact pow_card_eq_one'
      exact congrArg Z.subtype he
    · intro t ht
      exact ((normalizer_le_centralizer_of_card_two Z hZ (hTZ ht)) z hz).symm
  have hTN : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (hH ▸ hTZ).trans hHN
  have hout : Chapter3.HasMaximalOutside T (normalizer (A : Set G)) :=
    Chapter3.hasMaximalOutside_of_two_distinct hN hM hTN hTM
      (by intro he; exact hKM (he.symm ▸ A.le_normalizer))
  have hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (A : Set G) := by
    apply le_trans (centralizer_le hTO)
    apply le_trans (Subgroup.centralizer_le_normalizer _)
    rw [←hH]
    exact hHN
  let := hq
  let eK : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK))
  exact Chapter3.Section02.source_component_thompson_generation hG T A hstar
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T A).mp hf).2
    hqA hTN hout hC
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
