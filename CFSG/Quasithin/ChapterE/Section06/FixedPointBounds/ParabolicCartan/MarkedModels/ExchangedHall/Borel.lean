module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import Theory.GroupTheory.PCoreAbelianQuotient
public import Theory.GroupTheory.SylowKernelCore

/-!
# The exchanged Borel commutator calculation

In characteristic two, the concrete PSL₂ and Suzuki Borels have a normal
two-subgroup and a commutative torus supplement. Their derived subgroups
therefore lie in their intrinsic two-cores. Transport this calculation
through the same component/Borel marking used in E.2.2, and then through
the literal quotient by the source kernel. No unmarked Borel recognition
or splitting of the upstairs extension is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2(1a),
pp.215--216, and the Borel calculation in 4.4.13, pp.623--624.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall
variable {G : Type*} [Group G]

private theorem split_commutator_le_core (B U T : Subgroup G)
    (hU : IsPGroup 2 U) (hn : (U.subgroupOf B).Normal)
    (hsup : U ⊔ T = B) (hc : IsMulCommutative T) :
    ⁅B, B⁆ ≤ B.pCoreIn 2 := by
  have hUB : U ≤ B := hsup ▸ le_sup_left
  have hTB : T ≤ B := hsup ▸ le_sup_right
  let := hn
  have hc' : IsMulCommutative (T.subgroupOf B) := by
    let := hc
    infer_instance
  have hs : U.subgroupOf B ⊔ T.subgroupOf B = ⊤ := by
    apply map_injective B.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUB, map_subgroupOf_eq_of_le hTB,
      ← MonoidHom.range_eq_map, range_subtype, hsup]
  have hd := Normal.commutator_le_of_self_sup_commutative_eq_top hs hc'
  have hd' : ⁅B, B⁆ ≤ U := by
    simpa only [map_subtype_commutator, map_subgroupOf_eq_of_le hUB] using
      map_mono (f := B.subtype) hd
  exact hd'.trans (le_pCoreIn_of_normalizes hU hUB
    ((normal_subgroupOf_iff_le_normalizer hUB).mp hn))

open BenderSuzuki.Converse BenderSuzuki.MatrixGroups
/-- The projective linear Borel has two-group derived subgroup, using its actual root and torus ranges. -/
theorem psl2_commutator {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) :
    ⁅PBorel F, PBorel F⁆ ≤ (PBorel F).pCoreIn 2 := by
  apply split_commutator_le_core (PBorel F) (PUnip F) (PTorus F)
  · exact IsPGroup.of_card (PUnip_card.trans hF)
  · exact PUnip_normal_in_PBorel
  · exact PUnip_sup_PTorus
  · have he : Nonempty (Fˣ ≃* PTorus F) := by
      rw [PTorus, Torus_eq_range]
      exact ⟨(MonoidHom.ofInjective (torHom_injective (F := F))).trans
        (Subgroup.equivMapOfInjective _ (pi F) pi_injective)⟩
    obtain ⟨e⟩ := he
    exact ⟨⟨fun x y => e.symm.injective (by simp only [map_mul, mul_comm])⟩⟩

/-- The Suzuki Borel has two-group derived subgroup, with the standard root group normal only in the Borel. -/
theorem suzuki_commutator (m : ℕ) (hm : 0 < m) :
    ⁅SuzukiBorelSubgroup m, SuzukiBorelSubgroup m⁆ ≤ (SuzukiBorelSubgroup m).pCoreIn 2 := by
  apply split_commutator_le_core (SuzukiBorelSubgroup m) (SuzukiRootSubgroup m)
    (SuzukiSplitTorus m) (suzukiRootSubgroup_isPGroup m hm)
    (suzukiRootSubgroup_normal_in_borel m) (suzukiBorelSubgroup_eq_sup m).symm
  let := suzukiSplitTorus_isCyclic m hm
  infer_instance

/-- Transport the derived-subgroup bound through the simultaneous component and Borel marking. -/
theorem marked_borel_commutator {M K : Subgroup G}
    {A : Type*} [Group A] {B : Subgroup A} (hB : ModelBorelPair M K B)
    (hd : ⁅B, B⁆ ≤ B.pCoreIn 2) :
    ⁅sourceImage M (M ⊓ K), sourceImage M (M ⊓ K)⁆ ≤
      (sourceImage M (M ⊓ K)).pCoreIn 2 := by
  obtain ⟨e, he⟩ := hB
  have hO : ⁅componentOverlap M K, componentOverlap M K⁆ ≤
      (componentOverlap M K).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rwa [map_commutator, map_pCoreIn_of_injective 2 _ _ e.injective, he]
  have hmap : (componentOverlap M K).map (sourceImage M K).subtype =
      sourceImage M (M ⊓ K) :=
    map_subgroupOf_eq_of_le (map_mono (f := QuotientGroup.mk' (sourceKernel M)) inf_le_right)
  have hh := map_mono (f := (sourceImage M K).subtype) hO
  rwa [map_commutator, map_pCoreIn_of_injective 2 _ _ (sourceImage M K).subtype_injective,
    hmap] at hh

/-- Both exchanged models give the derived-subgroup bound in the literal source quotient. -/
theorem model_overlap_commutator {M K : Subgroup G} {n : ℕ}
    (hm : ExchangedModel M K n) :
    ⁅sourceImage M (M ⊓ K), sourceImage M (M ⊓ K)⁆ ≤
      (sourceImage M (M ⊓ K)).pCoreIn 2 := by
  rcases hm with ⟨F, hF, hfin, hchar, _, hcard, hB⟩ | ⟨m, hm, _, hB⟩
  · let := hF
    let := hfin
    let := hchar
    exact marked_borel_commutator hB (psl2_commutator hcard)
  · exact marked_borel_commutator hB (suzuki_commutator m (by omega))

/-- Lift the Borel bound to the original overlap using the source kernel equality. -/
theorem overlap_commutator [Finite G] {M K T : Subgroup G} {n : ℕ}
    (hc : ExchangedClauses M K T) (hm : ExchangedModel M K n) :
    ⁅M ⊓ K, M ⊓ K⁆ ≤ (M ⊓ K).pCoreIn 2 := by
  apply commutator_self_le_pCoreIn_of_map (QuotientGroup.mk' (sourceKernel M))
  · rw [QuotientGroup.ker_mk', hc.kernel_eq]
    exact pCore_isPGroup
  · exact model_overlap_commutator hm
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall
