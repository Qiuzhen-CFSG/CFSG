module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.OriginalSource
public import Theory.SpecificGroups.Tits.SylowActorCentralizer

/-!
# The original Tits branch of 15.3.43

The actor has order divisible by three and is normalized by the common Sylow
subgroup. In the Tits component its Sylow centralizer is trivial. Consequently
the ambient Sylow centralizer of the actor centralizes the component Sylow:
their commutator lies in the trivial component intersection. The intrinsic Tits
automorphism calculation then says this centralizer fixes the whole component,
contradicting 15.3.43(c).

This direct centralizer argument uses the original reduced configuration.
It needs no containment of the source involution centralizer in M and leaves
the original equality C_G(z) = M_c intact.

Source: Aschbacher--Smith, 15.3.43(a)--(c) and the binary paragraph,
printed pp.1139--1140.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The actual Tits component makes the two original Sylow centralizers equal. -/
theorem centralizers_eq_of_original_tits
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    (iso : Nonempty (L ≃* Tits.ParrottGroup)) :
    S ⊓ centralizer (Yplus : Set G) = S ⊓ centralizer (L : Set G) := by
  obtain ⟨e⟩ := iso
  obtain ⟨P, hP⟩ := component_sylow c
  have hPL : (P : Subgroup L) = S.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hP, subgroupOf_map_subtype]
  obtain ⟨f, hf⟩ := Tits.RelativeSylowMarking.exists_sylow_marking
    (e.trans Tits.parrottFiniteImageEquiv) P
  let Y := (Yplus.subgroupOf L).map f.toMonoidHom
  have hthree : 3 ∣ Nat.card Y := by
    change 3 ∣ Nat.card ((Yplus.subgroupOf L).map f.toMonoidHom)
    rw [card_map_of_injective f.injective,
      Nat.card_congr (subgroupOfEquivOfLe c.y_le_component).toEquiv, ← c.index]
    exact (pCore 2 Yplus).index_dvd_card
  have hSY : S ≤ normalizer (Yplus : Set G) :=
    (sylow_le_local c).trans (local_normalizes_actor c)
  have hnorm : Tits.atlas1600SylowTwoSubgroup ≤ normalizer (Y : Set Tits.Atlas1600Group) := by
    change Tits.atlas1600SylowTwoSubgroup ≤
      normalizer (((Yplus.subgroupOf L).map f.toMonoidHom) : Set Tits.Atlas1600Group)
    rw [← hf, hPL, ← map_equiv_normalizer_eq]
    apply map_mono
    rw [← subgroupOf_normalizer_eq c.y_le_component]
    exact fun x hx => hSY hx
  have hzero := Tits.SylowActorCentralizer.sylow_inf_centralizer_eq_bot Y hnorm hthree
  let N := S ⊓ centralizer (Yplus : Set G)
  let K := S ⊓ L
  have hNL : N ⊓ L = ⊥ := by
    apply bot_unique
    intro x hx
    let xl : L := ⟨x, hx.2⟩
    have hxS : f xl ∈ Tits.atlas1600SylowTwoSubgroup := by
      rw [← hf, hPL]
      exact mem_map_of_mem f.toMonoidHom hx.1.1
    have hxC : f xl ∈ centralizer (Y : Set Tits.Atlas1600Group) := by
      rintro _ ⟨y, hy, rfl⟩
      change f y * f xl = f xl * f y
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (hx.1.2 y hy))
    have he : f xl = 1 := hzero.le ⟨hxS, hxC⟩
    exact congrArg Subtype.val (f.injective (he.trans (map_one f).symm))
  have hSN : S ≤ normalizer (N : Set G) :=
    (le_inf S.le_normalizer (hSY.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hSL : S ≤ normalizer (L : Set G) :=
    ((sylow_le_local c).trans inf_le_right).trans c.normalizes
  have hSK : S ≤ normalizer (K : Set G) :=
    (le_inf S.le_normalizer hSL).trans inf_normalizer_le_normalizer_inf
  have hcomm : ⁅N, K⁆ = ⊥ := by
    apply bot_unique
    have hN : ⁅N, K⁆ ≤ N := le_normalizer_iff_commutator_le_left.mp
      ((show K ≤ S from inf_le_left).trans hSN)
    have hK : ⁅N, K⁆ ≤ K := le_normalizer_iff_commutator_le_right.mp
      ((show N ≤ S from inf_le_left).trans hSK)
    exact (le_inf hN (hK.trans inf_le_right)).trans hNL.le
  apply le_antisymm
  · intro s hs
    refine ⟨hs.1, ?_⟩
    let a : MulAut L := L.normalizerMonoidHom ⟨s, hSL hs.1⟩
    let b : MulAut Tits.Atlas1600Group := (f.symm.trans a).trans f
    have hfixS : ∀ x ∈ Tits.atlas1600SylowTwoSubgroup, b x = x := by
      intro x hx
      rw [← hf, hPL] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      change f (a (f.symm (f y))) = f y
      rw [f.symm_apply_apply]
      apply congrArg f
      apply Subtype.ext
      change s * (y : G) * s⁻¹ = (y : G)
      have hc := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hs y ⟨hy, y.property⟩
      rw [← hc, mul_inv_cancel_right]
    have hfixY : ∀ x ∈ Y, b x = x := by
      rintro _ ⟨y, hy, rfl⟩
      change f (a (f.symm (f y))) = f y
      rw [f.symm_apply_apply]
      apply congrArg f
      apply Subtype.ext
      change s * (y : G) * s⁻¹ = (y : G)
      rw [← hs.2 y hy, mul_inv_cancel_right]
    have hb := Tits.SylowActorCentralizer.eq_one_of_fixes_sylow_and_actor Y hthree b hfixS hfixY
    intro x hx
    let xl : L := ⟨x, hx⟩
    have he := MulEquiv.congr_fun hb (f xl)
    change f (a (f.symm (f xl))) = f xl at he
    rw [f.symm_apply_apply] at he
    have he' := congrArg Subtype.val (f.injective he)
    change s * x * s⁻¹ = x at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · exact inf_le_inf_left S (centralizer_le c.y_le_component)

/-- The original reduced configuration excludes Tits without a source-involution
centralizer assumption. -/
theorem not_tits_of_original_configuration
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    (iso : Nonempty (L ≃* Tits.ParrottGroup)) : False :=
  centralizers_ne c (centralizers_eq_of_original_tits c iso)

/-- The actual 15.3.43 consumer for the Tits component. -/
theorem source_not_symmetricThreeShadow_of_tits
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G}
    (hI : I ∈ d.HplusMinimal) (h : ReductionSourceInputs d I L)
    (halt : Candidates.Alternatives15343 d.Yplus I L (localSpan L d.S))
    (iso : Nonempty (L ≃* Tits.ParrottGroup)) :
    ¬ SymmetricThreeShadow d.Yplus d.S := by
  intro hshadow
  exact not_tits_of_original_configuration
    (reducedConfiguration_of_source d hI h hshadow halt) iso

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
