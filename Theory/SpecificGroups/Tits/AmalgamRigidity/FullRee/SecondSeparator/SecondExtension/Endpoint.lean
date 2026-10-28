module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.Setup

/-!
# Literal endpoint generation for the full Ree extension

The verified coordinate map supplies the actual inclusion into the full
second parabolic. Adjoining its specified Weyl lift generates that parabolic:
the generated subgroup contains the full Sylow group and the canonically
embedded Tits second parabolic, of orders 4096 and 6144 respectively.
Their least common multiple is the independently established endpoint order.
All maps retain the actual root marking; no amalgam isomorphism is assumed.

Source: Parrott (1972), p.683; Aschbacher–Smith F.1.11–12, pp.262–263.
-/

@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee.SecondExtension
open ReeTwo
open ReeF4.Parabolics.Binary.FixedGeometry

abbrev Endpoint := ExceptionalParabolics.FullRee.second

/-- The literal overlap inclusion, with the verified coordinate marking. -/
abbrev inclusion : SylowModel →* Endpoint := coordinateAmalgam.right

/-- The specified linear Weyl element in the literal full second endpoint. -/
def reflection : Endpoint :=
  ⟨weylLift 0 .linear, weylLift_mem_seed 0 .linear⟩

@[simp] theorem inclusion_coe (x : SylowModel) :
    (inclusion x : ReeF4.Model 0) = ParabolicMarkedComparison.Verified.sylowMap x := rfl

@[simp] theorem inclusion_root (i : CoreRoot) :
    (inclusion (SylowModel.root i) : ReeF4.Model 0) =
      ParabolicMarkedComparison.Ambient.root i := by
  exact ParabolicMarkedComparison.sylowMap_root ParabolicMarkedComparison.RootVerification.relations i

@[simp] theorem inclusion_rootOne :
    (inclusion SylowModel.rootOne : ReeF4.Model 0) =
      ParabolicMarkedComparison.Ambient.rootOne := by
  exact ParabolicMarkedComparison.sylowMap_rootOne ParabolicMarkedComparison.RootVerification.relations

theorem inclusion_injective : Function.Injective inclusion :=
  ExceptionalParabolics.FullRee.amalgam_right_injective.comp borelEquiv.injective

/-- Adding the actual reflection to the full Sylow image generates the full endpoint.
The generated subgroup contains groups of orders 4096 and 6144, whose least
common multiple is the independently proved endpoint order 12288. -/
theorem endpoint_generated :
    Subgroup.closure (insert reflection (Set.range inclusion)) = ⊤ := by
  let H : Subgroup Endpoint := Subgroup.closure (insert reflection (Set.range inclusion))
  let J : Subgroup (ReeF4.Model 0) := H.map Endpoint.subtype
  have hs : ExceptionalParabolics.FullRee.S ≤ J := by
    rw [← ParabolicMarkedComparison.Verified.sylowMap_range]
    rintro _ ⟨x, rfl⟩
    exact ⟨inclusion x, Subgroup.subset_closure (Or.inr ⟨x, rfl⟩), rfl⟩
  have hr : ExceptionalParabolics.FullRee.atlasEmbedding (atlas1600ParrottAssignment .r8) ∈ J := by
    rw [ParabolicMarkedComparison.Ambient.atlas_generator]
    exact ⟨reflection, Subgroup.subset_closure (Or.inl rfl), rfl⟩
  have ht : ExceptionalParabolics.second.map ExceptionalParabolics.FullRee.atlasEmbedding ≤ J := by
    rw [ExceptionalParabolics.second, Subgroup.map_sup]
    apply sup_le (ExceptionalParabolics.FullRee.atlas_sylow_map_le.trans hs)
    rw [Subgroup.map_le_iff_le_comap]
    exact (Subgroup.closure_le _).mpr (by rintro _ (rfl : _ = _); exact hr)
  have h4096 : 4096 ∣ Nat.card J := by
    simpa only [ExceptionalParabolics.FullRee.sylow_card] using Subgroup.card_dvd_of_le hs
  have h6144 : 6144 ∣ Nat.card J := by
    have hcard : Nat.card
        (ExceptionalParabolics.second.map ExceptionalParabolics.FullRee.atlasEmbedding) = 6144 := by
      rw [Nat.card_congr (ExceptionalParabolics.second.equivMapOfInjective
        ExceptionalParabolics.FullRee.atlasEmbedding
        ExceptionalParabolics.FullRee.atlasEmbedding_injective).toEquiv.symm]
      exact ExceptionalParabolics.second_card
    simpa only [hcard] using Subgroup.card_dvd_of_le ht
  have hge : 12288 ≤ Nat.card J := by
    have hd := Nat.lcm_dvd h4096 h6144
    norm_num at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have he : J = Endpoint := Subgroup.eq_of_le_of_card_ge
    (by rintro _ ⟨z, _, rfl⟩; exact z.property) (by simpa only [ExceptionalParabolics.FullRee.second_card] using hge)
  apply Subgroup.map_injective Endpoint.subtype_injective
  simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he

end Tits.AmalgamRigidity.FullRee.SecondExtension
