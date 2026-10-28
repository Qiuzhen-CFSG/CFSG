module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.Families
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import Theory.ElementaryAbelian.Quotient
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Kernel

/-!
# Solvable overgroups lie in the ambient generation target

Restrict Ω to the members contained in an overgroup H of T. Its weak closure
maps to the original weak closure, and E.1.8(2) maps its E-members into the
ambient E-family. Thus intrinsic generation of H places H in the generation
target. In particular the proved solvable generation theorem applies to every
solvable overgroup of T at every positive rank. A minimal supplement then
extends this to overgroups with solvable quotient and kernel in the target.

This is the containment needed for the minimal supplement in the odd-prime
chief-section branch of E.1.11. The orbit quotient and its solvability must
still be constructed in the application.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed pp.212--214.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
def restrictedFamily (H : Subgroup G) (Ω : Set (Subgroup G)) : Set (Subgroup H) :=
  {B | B.map H.subtype ∈ Ω}

omit [Finite G] in
theorem restrictedFamily_elementary (H : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    IsElementaryFamily (restrictedFamily H Ω) := by
  constructor
  · intro B hB
    let _ := hΩ.1 _ hB
    let e := (B.equivMapOfInjective H.subtype H.subtype_injective).symm
    exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
  · intro g B hB
    have he : (B.map (MulAut.conj g).toMonoidHom).map H.subtype =
        (B.map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [map_map, map_map]
      rfl
    change (B.map (MulAut.conj g).toMonoidHom).map H.subtype ∈ Ω
    rw [he]
    exact hΩ.2 g _ hB

omit [Finite G] in
theorem map_weakClosure_restrictedFamily (T H : Subgroup G) (hTH : T ≤ H)
    (Ω : Set (Subgroup G)) :
    (weakClosure (T.subgroupOf H) (restrictedFamily H Ω)).map H.subtype =
      weakClosure T Ω := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro B ⟨hB, hBT⟩
    apply map_le_iff_le_comap.mp
    exact le_sSup ⟨hB, map_le_iff_le_comap.mpr hBT⟩
  · apply sSup_le
    rintro A ⟨hA, hAT⟩
    have hAH := hAT.trans hTH
    rw [← map_subgroupOf_eq_of_le hAH]
    apply map_mono
    apply le_sSup
    refine ⟨?_, comap_mono hAT⟩
    change (A.subgroupOf H).map H.subtype ∈ Ω
    rwa [map_subgroupOf_eq_of_le hAH]

theorem map_eFamilySubgroup_restrictedFamily_le (n : ℕ) (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    (eFamilySubgroup n ((T : Subgroup G).subgroupOf H) (restrictedFamily H Ω)).map
      H.subtype ≤ eFamilySubgroup n (T : Subgroup G) Ω := by
  apply map_le_iff_le_comap.mpr
  apply iSup_le
  intro B
  let A := B.val.map H.subtype
  have hA : A ∈ Ω := B.property.1
  have hAT : A ≤ (T : Subgroup G) := map_le_iff_le_comap.mpr B.property.2
  have he : A.subgroupOf H = B.val := comap_map_eq_self (by rw [H.ker_subtype]; exact bot_le)
  let _ := hΩ.1 A hA
  apply sSup_le
  intro K hK
  apply map_le_iff_le_comap.mp
  have hmem : IsEMemberAt n (T : Subgroup G) A (K.map H.subtype) :=
    IsEMemberAt.inherit T A H hAT ((tau_le _ _).trans hTH) (he.symm ▸ hK)
  have hKE : K.map H.subtype ≤ eSubgroup n (T : Subgroup G) A := le_sSup hmem
  exact hKE.trans
    (le_iSup_of_le (⟨A, hA, hAT⟩ : {A : Subgroup G // A ∈ Ω ∧ A ≤ (T : Subgroup G)})
      (show eSubgroup n (T : Subgroup G) A ≤ eSubgroup n (T : Subgroup G) A from le_rfl))

theorem overgroup_le_generationTarget {n : ℕ} (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) (hgen : IsEGenerated n H) :
    H ≤ generationTarget n T Ω := by
  have hg := hgen (T.subtype hTH) (restrictedFamily H Ω) (restrictedFamily_elementary H hΩ)
  have hh := congrArg (Subgroup.map H.subtype) hg
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  rw [← hh]
  apply sup_le
  · exact (map_eFamilySubgroup_restrictedFamily_le n T H hTH hΩ).trans le_sup_left
  · have hm := le_normalizer_map H.subtype
      (H := weakClosure ((T : Subgroup G).subgroupOf H) (restrictedFamily H Ω))
    rw [map_weakClosure_restrictedFamily (T : Subgroup G) H hTH Ω] at hm
    exact hm.trans le_sup_right

theorem solvable_overgroup_le_generationTarget {n : ℕ} (hn : 0 < n) (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) [Group.IsSolvable H]
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    H ≤ generationTarget n T Ω :=
  overgroup_le_generationTarget T H hTH hΩ (isEGenerated_one_of_solvable.mono hn)

/-- A solvable quotient of an overgroup is enough when its kernel is already
in the target. A minimal supplement has solvable kernel by E.1.10(2), hence
is solvable; rank-one generation of that supplement removes the quotient. -/
theorem overgroup_le_target_of_solvable_quotient {n : ℕ} (hn : 0 < n) (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (Y : Subgroup H) [Y.Normal] [Group.IsSolvable (H ⧸ Y)]
    (hYM : Y.map H.subtype ≤ generationTarget n T Ω) :
    H ≤ generationTarget n T Ω := by
  let S := T.subtype hTH
  obtain ⟨K, hK⟩ := exists_minimalSupplement (S : Subgroup H) ⊤ Y le_top
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hk : f.ker = Y.subgroupOf K := by
    ext k
    change f k = 1 ↔ (k : H) ∈ Y
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : H)
  let _ : Group.IsSolvable f.ker := hk ▸ hK.isSolvable_kernel S
  let _ : Group.IsSolvable K := Group.isSolvable_of_ker_le_range
    f.ker.subtype f (by rw [f.ker.range_subtype])
  let _ : Group.IsSolvable (K.map H.subtype) :=
    Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective K)
  have hTK : (T : Subgroup G) ≤ K.map H.subtype := by
    have h := map_mono (f := H.subtype) hK.1.1
    simpa only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using h
  have hKM := solvable_overgroup_le_generationTarget hn T (K.map H.subtype) hTK hΩ
  have hcover : K ⊔ Y = ⊤ := by simpa using hK.1.2.2
  have he := congrArg (map H.subtype) hcover
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  rw [← he]
  exact sup_le hKM hYM


end CFSG.Quasithin.ChapterE.ChiefOrbit
