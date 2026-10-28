module

public import CFSG.Quasithin.Chapter13.Section01.LocalModelRigidity
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement.Models
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.SolvableOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.SpecificGroups.SU3.BinaryG2Comparison

/-!
# The five-model local rigidity step in 13.3.2

All proper Sylow-two overgroups in the five literal quotient models are
solvable. The triple cover is retained as a perfect central cover of A₆;
the unitary case is transported through the proved PSU₃(3)–G₂(2)′ comparison.
Thus a local component contained in a component with one of these quotients
coincides with it. Applying this to the actual faithful family transfers the
upper component's T-normality and its unchanged quotient model.

These are the genuine 13.1.2(5) and containment steps in 13.3.2(1–2), printed
pp.866,884–885. The preceding maximal-component model list and normality are
still independent source obligations; no classification theorem is asserted here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter1 Chapter1.Section02.LocalModels
variable {Q : Type*} [Group Q] [Finite Q]

/-- The full five-model list has solvable proper Sylow-two overgroups. -/
theorem MidSizeModel.solvableSylowOvergroups (h : MidSizeModel Q) :
    SolvableSylowOvergroups Q := by
  rcases h with ⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨hq,_,⟨e⟩⟩ |
    ⟨F,_,_,J,hF,hJ,⟨e⟩⟩
  · exact SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  · let := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    exact SolvableSylowOvergroups.of_equiv (e.trans (Atlas.fieldEquivPSL 3 eF))
      Matrix.PSL3Two.solvableSylowOvergroups
  · exact SolvableSylowOvergroups.of_equiv e
      AlternatingSix.ProperSylowOvergroups.isSolvable
  · let := hq
    exact SolvableSylowOvergroups.of_central_quotient (QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _) (by simp)
      (SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable)
  · exact SolvableSylowOvergroups.of_equiv
      (e.trans (J.projectiveEquivBinaryG2Derived hF hJ))
      Atlas.G2.binaryDerived_solvableSylowOvergroups

variable {G : Type*} [Group G] [Finite G]

/-- Source 13.1.2(5): any local component below the actual five-model component
is the whole component. The quotient is literally I/O₂(I). -/
theorem local_eq_of_midSize {T I K : Subgroup G}
    (hI : I ∈ L G T) (hK : K ∈ L G T) (hKI : K ≤ I)
    (hm : MidSizeModel (XiQuotient I)) : K = I :=
  Section01.LocalModelRigidity.local_eq_of_solvableSylowOvergroups hI hK hKI
    hm.solvableSylowOvergroups

/-- The actual faithful-family consumer in 13.3.2. Equality preserves the
original subgroup, normalizer, and intrinsic two-core quotient. -/
theorem faithful_normal_model_of_contained_midSize (T : Sylow 2 G)
    {K I : Subgroup G} (hK : K ∈ MainForward.faithfulLocalComponents T)
    (hI : I ∈ L G T) (hKI : K ≤ I) (hTI : (T : Subgroup G) ≤ normalizer I)
    (hm : MidSizeModel (XiQuotient I)) :
    K = I ∧ (T : Subgroup G) ≤ normalizer K ∧ MidSizeModel (XiQuotient K) := by
  have he := local_eq_of_midSize hI
    ((Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hK).1 hKI hm
  subst K
  exact ⟨rfl,hTI,hm⟩
end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
