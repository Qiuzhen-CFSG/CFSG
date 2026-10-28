module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OuterInvolutions
public import Theory.Mathieu.SmallModuleRanks.M12Automorphism
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient.Native
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Outer
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# No offenders on the literal Aut(M₁₂) heart

Every nontrivial inner involution displaces four dimensions of the actual
binary ten-dimensional heart, while an elementary inner subgroup has rank at
most three. An elementary subgroup containing an outer involution has rank
at most four, while that involution displaces five dimensions. Fixed spaces
only decrease on enlarging the actor, so neither case can contain an offender.

The outer displacement uses the checked finite fusion theorem, and the inner
action is exactly the original M₁₂ heart action. No centralizer-table, fixer,
classification, or representation-recognition premise is retained.
Source: Aschbacher–Smith H.11.1 and K.4.2.
-/
public section
open Subgroup Representation.BinaryOffender Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
open M12ExceptionalExtension

/-- All outer involutions of the actual full automorphism group fuse. -/
theorem outer_involution_fusion : LocalActors.OuterInvolutionFusion := by
  intro s t hs ht hs2 ht2
  have aux (a : MulAut M12) (ha : a ∉ MulAut.innerSubgroup M12) (ha2 : orderOf a = 2) :
      IsConj LocalActors.outerInvolution a := by
    let x := automorphismEquiv.symm a
    have hxo : x ∉ M12ExceptionalExtension.inner := by
      intro hi
      let y := innerModel.equiv.symm ⟨x,hi⟩
      have he : innerModel.embedding y = x := by
        exact congrArg Subtype.val (innerModel.equiv.apply_symm_apply ⟨x,hi⟩)
      apply ha
      refine ⟨y, ?_⟩
      rw [← automorphismEquiv_embedding, he, MulEquiv.apply_symm_apply]
    have hx2 : orderOf x = 2 := (automorphismEquiv.symm.orderOf_eq a).trans ha2
    obtain ⟨g,hg⟩ := isConj_iff.mp (OuterInvolutions.fusion x hx2 hxo)
    refine isConj_iff.mpr ⟨automorphismEquiv g, ?_⟩
    have hh := congrArg automorphismEquiv hg
    simpa only [map_mul,map_inv, x,MulEquiv.apply_symm_apply,
      OuterInvolutions.seed, LocalActors.outerInvolution, LocalActors.outerSeed] using hh
  exact (aux s hs hs2).symm.trans (aux t ht ht2)

private theorem rank_le {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElementaryTwo A) {r : ℕ} (hr : primeRank 2 G ≤ r) : rank A ≤ r := by
  have hc := (primeRank_le_iff_elementary_card_le G).mp hr A hA.2
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

private theorem inner_offender_rank (A : Subgroup (MulAut M12))
    (hA : IsElementaryTwo A) (hAi : A ≤ MulAut.innerSubgroup M12) : rank A ≤ 3 := by
  let I := MulAut.innerSubgroup M12
  let E := A.subgroupOf I
  let : IsElementaryAbelian 2 A := hA.2
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hAi
  have hc := (primeRank_le_iff_elementary_card_le I).mp M12AutomorphismRank.inner_twoRank_le_three E hE
  have he : Nat.card E = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAi).toEquiv
  rw [he] at hc
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

private theorem inner_displacement (t : MulAut M12) (hi : t ∈ MulAut.innerSubgroup M12)
    (ht : orderOf t = 2) : fixedCodim Ambient.automorphismRepresentation (zpowers t) = 4 := by
  obtain ⟨x,rfl⟩ := hi
  have hx : orderOf x = 2 := (orderOf_injective _ M12AutomorphismRank.conjugation_injective x).symm.trans ht
  have he := fixedSpace_comp_map Ambient.automorphismRepresentation MulAut.conj (zpowers x)
  rw [Ambient.automorphismRepresentation_inner, MonoidHom.map_zpowers] at he
  change Module.finrank (ZMod 2) (M12Heart ⧸ fixedSpace _ _) = 4
  rw [← he]
  exact fixedCodim_involution x hx

private theorem involution_bound (A : Subgroup (MulAut M12))
    (hA : IsOffender Ambient.automorphismRepresentation A) (t : MulAut M12) (ht : t ∈ A) :
    fixedCodim Ambient.automorphismRepresentation (zpowers t) ≤ rank A := by
  have hle : fixedSpace Ambient.automorphismRepresentation A ≤
      fixedSpace Ambient.automorphismRepresentation (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hfix := Submodule.finrank_mono hle
  have hdimA := fixedCodim_add_finrank Ambient.automorphismRepresentation A
  have hdimt := fixedCodim_add_finrank Ambient.automorphismRepresentation (zpowers t)
  have hb := hA.2
  omega

/-- The literal binary ten-dimensional heart of Aut(M₁₂) has no offender. -/
theorem automorphismRepresentation_not_isFFModule :
    ¬ IsFFModule Ambient.automorphismRepresentation := by
  rintro ⟨A,hA⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  by_cases hAi : A ≤ MulAut.innerSubgroup M12
  · obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1.1
    have ht2 : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
    have hd := inner_displacement t (hAi ht) ht2
    have hb := involution_bound A hA t ht
    have hr := inner_offender_rank A hA.1 hAi
    omega
  · obtain ⟨t,ht,hto⟩ := SetLike.not_le_iff_exists.mp hAi
    have ht1 : t ≠ 1 := fun he => hto (he ▸ (MulAut.innerSubgroup M12).one_mem)
    have ht2 : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
    have hd := LocalActors.fixedCodim_native_outer outer_involution_fusion
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_faithful hto ht2
    have hb := involution_bound A hA t ht
    have hr := rank_le hA.1 M12AutomorphismRank.twoRank_le_four
    omega
end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
