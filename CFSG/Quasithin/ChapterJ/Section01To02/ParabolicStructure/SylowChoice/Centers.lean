module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center

/-!
# Sylow centers before the Ru2 choice

Ru1 alone determines the center of every ambient Sylow two-subgroup to have
order two. First extend a Sylow subgroup of L to an ambient Sylow; its center
lies in V and embeds in the fixed line of the natural action. Then transport
only the center order by Sylow isomorphism. No Ru2 data is transported here.

Source: Aschbacher–Smith, J.1 (Ru1) and the first argument of J.2.1,
printed pp.431–432 (combined manuscript of 1 March 2004).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The center equality needs only Ru1 and containment of its special core. -/
theorem RuOne.sylowCenter_eq_of_core_le {L V : Subgroup G} (r : RuOne L V)
    (T : Sylow 2 G) (hS : L.pCoreIn 2 ≤ (T : Subgroup G)) :
    sylowCenter T = V ⊓ centralizer ((T : Subgroup G) : Set G) := by
  have hVS : V ≤ L.pCoreIn 2 := r.V_le_S
  have hVT := hVS.trans hS
  apply le_antisymm
  · intro z hz
    obtain ⟨z, hz, rfl⟩ := hz
    have hzc : (z : G) ∈ centralizer ((T : Subgroup G) : Set G) :=
      fun t ht => congrArg (fun a : T => (a : G)) ((mem_center_iff.mp hz) ⟨t, ht⟩)
    refine ⟨?_, hzc⟩
    rw [← r.centralizer_S]
    exact centralizer_le hS hzc
  · intro z hz
    refine mem_map.mpr ⟨⟨z, hVT hz.1⟩, ?_, rfl⟩
    exact mem_center_iff.mpr (fun t => Subtype.ext (hz.2 t t.property))

/-- Ru1 fixes the center order for every Sylow, without changing a Ru2 witness. -/
theorem RuOne.card_sylowCenter {L V : Subgroup G} (r : RuOne L V)
    (T : Sylow 2 G) : Nat.card (sylowCenter T) = 2 := by
  let P₀ : Sylow 2 L := Sylow.nonempty.some
  obtain ⟨R, hPR⟩ := (P₀.isPGroup'.map L.subtype).exists_le_sylow
  have hinter := inf_eq_sylow_map P₀ R.isPGroup' hPR
  have hS : L.pCoreIn 2 ≤ (R : Subgroup G) := (pCoreIn_le_sylow L P₀).trans hPR
  have hcenter := r.sylowCenter_eq_of_core_le R hS
  have hcardR : Nat.card (sylowCenter R) = 2 := by
    let P := P₀.mapSurjective r.quotient_surjective
    have hZV : sylowCenter R ≤ V := hcenter.le.trans inf_le_left
    let f : sylowCenter R →
        BinaryOffender.fixedSpace BinaryLinearThree.W (P : Subgroup BinaryLinearThree.Group) :=
      fun z => ⟨(r.natural.coordinates ⟨z, hZV z.property⟩).toAdd, by
        intro a
        obtain ⟨p, hp, hpa⟩ := a.property
        have hpT : (p : G) ∈ (R : Subgroup G) := by
          have hpm : (p : G) ∈ (P₀ : Subgroup L).map L.subtype :=
            mem_map.mpr ⟨p, hp, rfl⟩
          rw [← hinter] at hpm
          exact hpm.1
        have hzC := (hcenter.le z.property).2
        have he := r.natural.equivariant p ⟨z, hZV z.property⟩
        have heq : p.val * z.val * p.val⁻¹ = z.val := by
          rw [hzC p hpT, mul_inv_cancel_right]
        have hv : (⟨p.val * z.val * p.val⁻¹,
            by rw [heq]; exact hZV z.property⟩ : V) = ⟨z, hZV z.property⟩ :=
          Subtype.ext heq
        rw [hv] at he
        change BinaryLinearThree.W (a : BinaryLinearThree.Group) _ = _
        rw [← hpa]
        exact he.symm⟩
    have hi : Function.Injective f := by
      intro x y h
      have hinj : Function.Injective r.natural.coordinates := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        rw [r.natural.kernel_eq, bot_subgroupOf]
      have hc := congrArg Subtype.val h
      have hxy := hinj (Multiplicative.toAdd.injective hc)
      have hexy := congrArg Subtype.val hxy
      exact Subtype.ext hexy
    have hu := (Nat.card_le_card_of_injective f hi).trans
      (BinaryLinearThree.card_sylow_natural_fixed_le_two P)
    have hVT := r.V_le_S.trans hS
    have hTcard : 1 < Nat.card R := by
      have hv := card_le_of_le hVT
      rw [r.card_V] at hv
      omega
    let : Fintype R := Fintype.ofFinite R
    let : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_eq_fintype_card] using hTcard)
    let : Nontrivial (center R) := R.isPGroup'.center_nontrivial
    let : Fintype (center R) := Fintype.ofFinite (center R)
    have hl : 1 < Nat.card (sylowCenter R) := by
      change 1 < Nat.card ((center R).map (R : Subgroup G).subtype)
      rw [card_map_of_injective (R : Subgroup G).subtype_injective,
        Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega

  change Nat.card ((center T).map (T : Subgroup G).subtype) = 2
  rw [card_map_of_injective (T : Subgroup G).subtype_injective,
    Nat.card_congr (centerCongr (T.equiv R)).toEquiv]
  simpa only [sylowCenter, card_map_of_injective (R : Subgroup G).subtype_injective]
    using hcardR

/-- The Ru2 witness has center order two even before the compatible Sylow choice. -/
theorem TypeRuSetup.card_Z (d : TypeRuSetup G) : Nat.card d.Z = 2 :=
  d.ru1.card_sylowCenter d.T

/-- Elementary abelianness of U does not require the compatible Sylow choice. -/
theorem TypeRuSetup.elementary_U (d : TypeRuSetup G) : IsElementaryAbelian 2 d.U :=
  d.elementary_U_of_card_Z d.card_Z

end CFSG.Quasithin.ChapterJ
