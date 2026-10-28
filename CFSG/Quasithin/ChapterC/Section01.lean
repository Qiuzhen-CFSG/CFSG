module

public import CFSG.Quasithin.ChapterC.Defs

/-!
# Blocks and basic pushing-up: the initial subgroup lemmas

The elementary radical-subgroup results C.1.2(1–3) follow from maximality of
Sylow subgroups and maximal normalizer-preserving enlargement, respectively. Normalizer control transfers radicality to an overgroup.
The definitions C.1.3–C.1.6 imply that (CPU) is stronger than (PU): a normal
nontrivial characteristic subgroup would have normalizer all of G, contradicting
the proper overgroup in (CPU).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §C.1, pp. 121–143. This module currently supplies
the initial subgroup lemmas; the later block and pushing-up results are separate
prerequisites to be assembled here.
-/

public section

namespace CFSG.Quasithin.ChapterC

variable {G : Type*} [Group G]

/-- C.1.2(1): a nontrivial Sylow 2-subgroup is radical. -/
theorem twoRadical_sylow (S : Sylow 2 G) (hne : (S : Subgroup G) ≠ ⊥) :
    IsTwoRadical (S : Subgroup G) := Subgroup.isPRadical_sylow S hne

/-- C.1.2(2): a radical enlargement preserving the original normalizer. -/
theorem exists_twoRadical [Finite G] (R : Subgroup G)
    (hR : IsNontrivialTwoSubgroup R) :
    ∃ B : Subgroup G, IsTwoRadical B ∧ R ≤ B ∧
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (B : Set G) :=
  Subgroup.exists_isPRadical_of_isPGroup R hR.2 hR.1

/-- C.1.2(3): radicality transfers under normalizer control. -/
theorem twoRadical_subgroupOf_of_normalizer_le (R H K : Subgroup G)
    (hRH : R ≤ H) (hHK : H ≤ K) (hR : IsTwoRadical (R.subgroupOf H))
    (hNK : K ⊓ Subgroup.normalizer (R : Set G) ≤ H) :
    IsTwoRadical (R.subgroupOf K) :=
  Subgroup.IsPRadical.subgroupOf_of_normalizer_le R H K hRH hHK hR hNK

/-- Radical 2-subgroups belong to S₂(G). -/
theorem IsTwoRadical.nontrivialTwoSubgroup {R : Subgroup G} (hR : IsTwoRadical R) :
    IsNontrivialTwoSubgroup R := ⟨hR.1, hR.isPGroup⟩

/-- Under (PU), each characteristic-subgroup normalizer is proper. -/
theorem PushingUp.normalizer_lt_top {R : Subgroup G} (hR : PushingUp R)
    (C : Subgroup R) [hC : C.Characteristic] (hne : C ≠ ⊥) :
    Subgroup.normalizer (C.map R.subtype : Set G) < ⊤ := by
  rw [lt_top_iff_ne_top, Ne, Subgroup.normalizer_eq_top_iff]
  exact hR.2 C hC hne

/-- The stronger pushing-up hypothesis (CPU) implies (PU). -/
theorem CharacteristicPushingUp.pushingUp {R : Subgroup G}
    (hR : CharacteristicPushingUp R) : PushingUp R := by
  obtain ⟨hrad, M, hRM, hM, _⟩ := hR
  refine ⟨hrad, ?_⟩
  intro C hC hne
  let := hC
  exact Subgroup.not_normal_of_characteristicNormalizerClosure_le R M hM hRM C hne

/-- The overgroup in (CPU) contains the whole normalizer of R. -/
theorem CharacteristicPushingUp.exists_overgroup {R : Subgroup G}
    (hR : CharacteristicPushingUp R) :
    ∃ M : Subgroup G, Subgroup.normalizer (R : Set G) ≤ M ∧ M < ⊤ ∧
      IsSylowInNormalClosure R M := by
  obtain ⟨hrad, M, hRM, hM, hSyl⟩ := hR
  exact ⟨M, (Subgroup.normalizer_le_characteristicNormalizerClosure_self R hrad.1).trans hRM,
    hM, hSyl⟩

end CFSG.Quasithin.ChapterC
