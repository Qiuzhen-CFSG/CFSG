module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.ElementaryAbelian.Quotient

/-!
# E-generation transfer through a normal subgroup

Suppose H is normal and G = HT. Remove the trivial subgroup from an invariant
family before restricting it to H. If every remaining member in T lies in H,
its weak closure is unchanged. Ambient tau containment then transports every
intrinsic E-member back to G using E.1.8, including its literal quotient ranks
and local tau orbit. Thus generation of H supplies the H contribution in G.

The final reduction handles small actors with a whole-group E-member, large
actors in H by this transfer, and actors outside H by an E-member supplementing
T. Swapping.lean applies it to the actual parabolic-class action kernel.
The model centralizer and external-member calculations remain explicit.

Source: Aschbacher--Smith, E.1.1--8 and E.1.14(1), printed pp.209--211,214.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping
variable {G : Type*} [Group G] [Finite G]

/-- Nontrivial family members on the actual intrinsic subgroup carrier. -/
def nontrivialRestriction (H : Subgroup G) (Ω : Set (Subgroup G)) : Set (Subgroup H) :=
  {B | B.map H.subtype ∈ Ω ∧ B ≠ ⊥}

omit [Finite G] in
/-- Restriction and removal of the trivial subgroup preserve the family axioms. -/
theorem nontrivialRestriction_elementary (H : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    IsElementaryFamily (nontrivialRestriction H Ω) := by
  constructor
  · intro B hB
    let := hΩ.1 _ hB.1
    let e := (B.equivMapOfInjective H.subtype H.subtype_injective).symm
    exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  · intro g B hB
    constructor
    · have he : (B.map (MulAut.conj g).toMonoidHom).map H.subtype =
          (B.map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
        rw [map_map, map_map]
        rfl
      rw [he]
      exact hΩ.2 g _ hB.1
    · intro h
      apply hB.2
      exact (Subgroup.map_injective (MulAut.conj g).injective) (by simpa using h)

omit [Finite G] in
/-- The original weak closure is recovered when all its nontrivial generators lie in H. -/
theorem map_weakClosure_nontrivialRestriction (T H : Subgroup G)
    (Ω : Set (Subgroup G))
    (hinside : ∀ A ∈ Ω, A ≤ T → A ≠ ⊥ → A ≤ H) :
    (weakClosure (T.subgroupOf H) (nontrivialRestriction H Ω)).map H.subtype =
      weakClosure T Ω := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro B ⟨hB, hBT⟩
    apply map_le_iff_le_comap.mp
    exact le_sSup ⟨hB.1, map_le_iff_le_comap.mpr hBT⟩
  · apply sSup_le
    rintro A ⟨hA, hAT⟩
    by_cases hne : A = ⊥
    · simp [hne]
    have hAH := hinside A hA hAT hne
    rw [← map_subgroupOf_eq_of_le hAH]
    apply map_mono
    apply le_sSup
    refine ⟨⟨?_, ?_⟩, comap_mono hAT⟩
    · rwa [map_subgroupOf_eq_of_le hAH]
    · intro h
      apply hne
      have hm := congrArg (Subgroup.map H.subtype) h
      simpa only [map_subgroupOf_eq_of_le hAH, Subgroup.map_bot] using hm

/-- Ambient tau containment supplies all of E0 in the embedding inheritance theorem. -/
theorem map_eFamilySubgroup_nontrivialRestriction_le (i : ℕ) (T : Sylow 2 G)
    (H : Subgroup G) {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (htau : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → A ≤ H →
      tau (T : Subgroup G) A ≤ H) :
    (eFamilySubgroup i ((T : Subgroup G).subgroupOf H)
      (nontrivialRestriction H Ω)).map H.subtype ≤
        eFamilySubgroup i (T : Subgroup G) Ω := by
  apply map_le_iff_le_comap.mpr
  apply iSup_le
  intro B
  let A := B.val.map H.subtype
  have hA : A ∈ Ω := B.property.1.1
  have hAT : A ≤ (T : Subgroup G) := map_le_iff_le_comap.mpr B.property.2
  have hAH : A ≤ H := (B.val.map_le_range _).trans_eq H.range_subtype
  have hne : A ≠ ⊥ := by
    intro h
    apply B.property.1.2
    exact (Subgroup.map_injective H.subtype_injective) (by simpa using h)
  have he : A.subgroupOf H = B.val := comap_map_eq_self (by rw [H.ker_subtype]; exact bot_le)
  let := hΩ.1 A hA
  apply sSup_le
  intro K hK
  apply map_le_iff_le_comap.mp
  have hmem : IsEMemberAt i (T : Subgroup G) A (K.map H.subtype) :=
    IsEMemberAt.inherit T A H hAT (htau A hA hAT hne hAH) (he.symm ▸ hK)
  exact (show K.map H.subtype ≤ eSubgroup i (T : Subgroup G) A from le_sSup hmem).trans
    (le_iSup_of_le (⟨A, hA, hAT⟩ : {A : Subgroup G // A ∈ Ω ∧ A ≤ (T : Subgroup G)})
      le_rfl)

/-- Intrinsic generation supplies H even when H does not contain the ambient Sylow. -/
theorem subgroup_le_generation_of_family_tau {i : ℕ} (T : Sylow 2 G)
    (H : Subgroup G) (S : Sylow 2 H)
    (hS : (S : Subgroup H) = (T : Subgroup G).subgroupOf H)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hinside : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → A ≤ H)
    (htau : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → A ≤ H →
      tau (T : Subgroup G) A ≤ H)
    (hgen : IsEGenerated i H) :
    H ≤ eFamilySubgroup i (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  have hg := hgen S (nontrivialRestriction H Ω) (nontrivialRestriction_elementary H hΩ)
  change eFamilySubgroup i (S : Subgroup H) _ ⊔ normalizer (weakClosure (S : Subgroup H) _ : Set H) = ⊤ at hg
  rw [hS] at hg
  have hh := congrArg (Subgroup.map H.subtype) hg
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  rw [← hh]
  apply sup_le
  · exact (map_eFamilySubgroup_nontrivialRestriction_le i T H hΩ htau).trans le_sup_left
  · have hm := le_normalizer_map H.subtype
      (H := weakClosure ((T : Subgroup G).subgroupOf H) (nontrivialRestriction H Ω))
    rw [map_weakClosure_nontrivialRestriction (T : Subgroup G) H Ω hinside] at hm
    exact hm.trans le_sup_right

/-- Generation from a normal subgroup, small top members, and external supplements. -/
theorem isEGenerated_of_normal_subgroup_and_external_members {i : ℕ}
    (T : Sylow 2 G) (H : Subgroup G) [H.Normal]
    (hHT : H ⊔ (T : Subgroup G) = ⊤)
    (hgen : IsEGenerated i H)
    (htop : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      A ≠ ⊥ → Group.rank A ≤ i → IsEMemberAt i (T : Subgroup G) A ⊤)
    (htau : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      A ≤ H → i < Group.rank A → tau (T : Subgroup G) A ≤ H)
    (hout : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      ¬ A ≤ H → i < Group.rank A → ∃ K : Subgroup G,
        IsEMemberAt i (T : Subgroup G) A K ∧ K ⊔ (T : Subgroup G) = ⊤) :
    IsEGenerated i G := by
  classical
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  let M := eFamilySubgroup i (T : Subgroup G) Ω ⊔
    normalizer (weakClosure (T : Subgroup G) Ω : Set G)
  have hT : (T : Subgroup G) ≤ M :=
    (Subgroup.le_normalizer.trans
      (RankOneUpper.normalizer_le_weakClosure_normalizer (T : Subgroup G) hΩ)).trans le_sup_right
  have hmember : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → ∀ K,
      IsEMemberAt i (T : Subgroup G) A K → K ≤ M := by
    intro A hA hAT K hK
    exact (show K ≤ eSubgroup i (T : Subgroup G) A from le_sSup hK).trans
      ((le_iSup (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)} =>
        eSubgroup i (T : Subgroup G) B.1) ⟨A, hA, hAT⟩).trans le_sup_left)
  by_cases hs : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ Group.rank A ≤ i
  · obtain ⟨A, hA, hAT, hne, hr⟩ := hs
    exact top_unique (hmember A hA hAT ⊤ (htop A (hΩ.1 A hA) hAT hne hr))
  have hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → i < Group.rank A := by
    intro A hA hAT hne
    exact Nat.lt_of_not_ge (fun hr => hs ⟨A, hA, hAT, hne, hr⟩)
  by_cases hext : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ ¬ A ≤ H
  · obtain ⟨A, hA, hAT, hAH⟩ := hext
    have hne : A ≠ ⊥ := fun h => hAH (h ▸ bot_le)
    obtain ⟨K, hK, hKT⟩ := hout A (hΩ.1 A hA) hAT hAH (hlarge A hA hAT hne)
    apply top_unique
    rw [← hKT]
    exact sup_le (hmember A hA hAT K hK) hT
  · obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal H
    have hHM : H ≤ M := subgroup_le_generation_of_family_tau T H S hS hΩ
      (fun A hA hAT _ => by by_contra h; exact hext ⟨A, hA, hAT, h⟩)
      (fun A hA hAT hne hAH => htau A (hΩ.1 A hA) hAT hAH (hlarge A hA hAT hne)) hgen
    apply top_unique
    rw [← hHT]
    exact sup_le hHM hT

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping
