module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.FixedBlockInputs
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# From the fixed plane to the maximum elementary family

A maximum elementary subgroup outside V has order at least sixteen.
Its intersection with V has order at most four, since any of its elements
outside V fixes precisely E. Thus its image is the entire quotient R/V
of order four. The fixed plane then supplies the hypotheses of B.2.21.

The escaping normalizer supplies a maximum subgroup outside V: if a
chosen maximum lies in V, it equals V, and an escaping conjugate moves it.
All family and fixed-space comparisons use the literal inclusion R → G.
The order and single-element fixed-plane facts remain explicit B.4.8 inputs.

Source: Aschbacher–Smith, 12.4.5(3) and 12.4.6, printed pp.813–814,
using B.4.8(2) and B.2.21.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02
universe u

private theorem max_image_eq_top
    {X H : Type*} [Group X] [Group H] [Finite X] [Finite H]
    (V E : Subgroup X) [IsElementaryAbelian 2 V]
    (q : X →* H) (hker : q.ker = V) (hH : Nat.card H = 4)
    (hV : Nat.card V = 16) (hE : Nat.card E = 4)
    (hplane : ∀ a : X, a ∉ V → V ⊓ centralizer ({a} : Set X) = E)
    (A : Subgroup X) (hA : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup X))
    (hAV : ¬ A ≤ V) : A.map q = ⊤ := by
  let _ := hA.2.1
  obtain ⟨a, ha, hav⟩ := SetLike.not_le_iff_exists.mp hAV
  have hi : A ⊓ V ≤ E := by
    rw [← hplane a hav]
    exact le_inf inf_le_right (inf_le_left.trans
      (A.le_centralizer.trans (centralizer_le (Set.singleton_subset_iff.mpr ha))))
  have hi4 : Nat.card (A ⊓ V : Subgroup X) ≤ 4 := (card_le_of_le hi).trans_eq hE
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup X) (A ⊓ V) A bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, ← hker,
    relIndex_ker, hker] at hcount
  have hA16 : 16 ≤ Nat.card A := hV ▸ hA.2.2 V le_top inferInstance
  have hlo : 16 ≤ 4 * Nat.card (A.map q) := hA16.trans
    (hcount ▸ Nat.mul_le_mul_right (Nat.card (A.map q)) hi4)
  have hhi : Nat.card (A.map q) ≤ 4 :=
    (Nat.card_le_card_of_injective _ (A.map q).subtype_injective).trans_eq hH
  have he : Nat.card (A.map q) = 4 := by omega
  apply eq_of_le_of_card_ge le_top
  simp only [card_top, hH, he, le_refl]

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Escape from N_G(V)=N_G(L) produces a maximum elementary subgroup
of the actual R that is not contained in V. -/
theorem exists_max_not_le_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G)) :
    ∃ A ∈ elementaryAbelianMaxSubgroups d.R, ¬ A ≤ V := by
  classical
  let _ := D.elementary
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty d.R
  by_cases hAV : A ≤ V
  · have he : A = V := eq_of_le_of_card_ge hAV (hA.2.2 V hVR inferInstance)
    subst A
    obtain ⟨_, z, _, _, _, hM, _, _⟩ := exists_slThree_fixed_involution_setup
      h D structural marked uniquenessEarlier_knownSimple hmodel hne
    obtain ⟨g, hg, hgM⟩ := SetLike.not_le_iff_exists.mp hescape
    let f := (MulAut.conj g).toMonoidHom
    have hR : d.R.map f = d.R := mem_normalizer_iff_map_conj_eq.mp hg
    have hB := (maxFamily_map_injective_iff f (MulAut.conj g).injective d.R V).mpr hA
    rw [hR] at hB
    refine ⟨V.map f, hB, ?_⟩
    intro hBV
    have hBVeq : V.map f = V := eq_of_le_of_card_ge hBV
      (hB.2.2 V hVR inferInstance)
    apply hgM
    rw [hM]
    exact mem_normalizer_iff_map_conj_eq.mpr hBVeq
  · exact ⟨A, hA, hAV⟩

/-- The common actor image and B.2.21 yield the two-member family from
the literal order-four quotient and its single-element fixed planes. -/
theorem fixedBlock_pair_of_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) (d : LocalGeometry D)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hself : (T : Subgroup G) ⊓ centralizer (V : Set G) = V)
    (hVcard : Nat.card V = 16)
    (hindex : V.relIndex d.R = 4)
    (hplane : ∀ a ∈ d.R, a ∉ V → V ⊓ centralizer ({a} : Set G) = d.E) :
    ∃ A : Subgroup G, V ∈ elementaryAbelianMaxSubgroups d.R ∧
      elementaryAbelianMaxSubgroups d.R ⊆ {V, A} := by
  classical
  let _ := D.elementary
  have hVR : V ≤ d.R := le_inf D.le_sylow
    (V.le_centralizer.trans (centralizer_le d.le_module))
  let W := V.subgroupOf d.R
  let E := d.E.subgroupOf d.R
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVR
  have hER : d.E ≤ d.R := d.le_module.trans hVR
  have hWcard : Nat.card W = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv).trans hVcard
  have hEcard : Nat.card E = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv).trans d.card_plane
  have hWN : (V.subgroupOf d.R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVR).mpr
      (inf_le_left.trans ((structural G T L h).2.2 V D).1)
  let _ := hWN
  let q : d.R →* (d.R ⧸ W) := QuotientGroup.mk' W
  have hker : q.ker = W := QuotientGroup.ker_mk' W
  have hquot : Nat.card (d.R ⧸ W) = 4 := hindex
  have hWself : centralizer (W : Set d.R) = W := by
    apply le_antisymm ?_ W.le_centralizer
    intro x hx
    have hc : (x : G) ∈ centralizer (V : Set G) := by
      intro v hv
      exact congrArg Subtype.val (hx ⟨v, hVR hv⟩ hv)
    change (x : G) ∈ V
    exact hself.le ⟨x.property.1, hc⟩
  have hplanes : ∀ a : d.R, a ∉ W → W ⊓ centralizer ({a} : Set d.R) = E := by
    intro a ha
    ext x
    change ((x : G) ∈ V ∧ x ∈ centralizer ({a} : Set d.R)) ↔ (x : G) ∈ d.E
    rw [← hplane a a.property ha]
    simp only [mem_inf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => Subtype.ext_iff
  obtain ⟨A, hA, hAV⟩ := exists_max_not_le_module h structural marked hmodel hne d hescape
  obtain ⟨B, hB, hAB⟩ := (maxFamily_equiv_iff d.R (MulEquiv.refl d.R) A).mp hA
  have hBW : ¬ B ≤ W := by
    intro hBW
    apply hAV
    rw [hAB]
    rintro _ ⟨x, hx, rfl⟩
    exact hBW hx
  have himage := max_image_eq_top W E q hker hquot hWcard hEcard hplanes B hB hBW
  obtain ⟨a, ha, haw⟩ := SetLike.not_le_iff_exists.mp hBW
  have hfixed : W ⊓ centralizer (B : Set d.R) = E := by
    apply le_antisymm
    · rw [← hplanes a haw]
      exact inf_le_inf_left W (centralizer_le (Set.singleton_subset_iff.mpr ha))
    · intro x hx
      refine ⟨d.le_module hx, ?_⟩
      intro b hb
      apply Subtype.ext
      have hxfixed : (x : G) ∈ V ⊓ centralizer (d.R : Set G) := d.fixed_plane ▸ hx
      exact hxfixed.2 b b.property
  have hf := ambient_maxFamily_eq_pair_of_common_image d.R W B q
    (hker.trans hWself.symm) hWself hB hWcard
    (by rw [himage, card_top]; exact hquot)
    (by rw [hfixed]; exact hEcard) a ha (hfixed.trans (hplanes a haw).symm)
    (by intro C hC hCW; rw [himage]; exact
      max_image_eq_top W E q hker hquot hWcard hEcard hplanes C hC hCW)
  rw [map_subgroupOf_eq_of_le hVR] at hf
  refine ⟨B.map d.R.subtype, ?_, ?_⟩
  · rw [hf]
    exact Or.inl rfl
  · exact hf.le

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
