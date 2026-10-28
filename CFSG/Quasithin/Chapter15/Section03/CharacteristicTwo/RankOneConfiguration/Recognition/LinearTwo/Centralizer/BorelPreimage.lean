module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.NaturalModel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.BlockAction

/-!
# Locating the full Borel preimage and its residual

Relative normality puts O₂(L) in the common Sylow subgroup, hence in M.
The marked image therefore identifies M ∩ L with the full Borel preimage.
Functoriality of the prime-to-three residual then places its residual in
Y₊, using exactly the earlier equality Y₊ = O^{3′}(M ∩ I).

Source: Aschbacher–Smith 15.3.26–30, printed pp.1130–1132.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

private theorem residual_map_le {A B : Type*} [Group A] [Group B]
    (p : ℕ) (f : A →* B) : (primeToResidual p A).map f ≤ primeToResidual p B := by
  apply le_sInf
  rintro N ⟨hN, hc⟩
  let := hN
  rw [map_le_iff_le_comap]
  apply primeToResidual_le
  rw [N.index_comap]
  exact hc.coprime_dvd_right (N.relIndex_dvd_index_of_normal f.range)

variable {G : Type*} [Group G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} {F : Type*} [Field F]

/-- The block's intrinsic two-core lies in M ∩ L, by relative normality
and the common Sylow subgroup. No ambient normality of L is asserted. -/
theorem Earlier.core_le_intersection (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S) :
    pCore 2 c.L ≤ d.M.subgroupOf c.L := by
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp h.component_normal
  have hcore : c.L.pCoreIn 2 ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 c.L)
      ((pCoreIn_le 2 c.L).trans (component_le c))
      (hIL.trans (normalizer_le_normalizer_characteristic_image c.L (pCore 2 c.L)))
  have hS : c.L.pCoreIn 2 ≤ d.S := hcore.trans (hP ▸ pCoreIn_le_sylow I P)
  intro l hl
  exact (hS.trans (inf_le_left.trans d.sylow_le)) (mem_map_of_mem c.L.subtype hl)

/-- The full matrix-Borel preimage is the actual intersection M ∩ L. -/
theorem MarkedBlockModel.blockBorel_eq (a : MarkedBlockModel d I c F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    blockBorel a.model = d.M.subgroupOf c.L := by
  have hk : (blockLinearMap a.model).ker ≤ d.M.subgroupOf c.L := by
    rw [blockLinearMap_ker]
    exact h.core_le_intersection P hP
  change (Matrix.SpecialLinearGroup.rankOneBorel F).comap (blockLinearMap a.model) = _
  rw [← a.borel]
  exact comap_map_eq_self hk

/-- The genuine earlier residual equality puts the Borel residual in Y₊.
This does not replace the residual by the two-core or assume U(L) lies in it. -/
theorem MarkedBlockModel.blockBorelResidual_le_yplus (a : MarkedBlockModel d I c F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hres : d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype) :
    blockBorelResidual a.model ≤ d.Yplus.subgroupOf c.L := by
  have he := a.blockBorel_eq h P hP
  let f : blockBorel a.model →* d.MI I := {
    toFun x := ⟨((x : c.L) : G),
      ⟨show ((x : c.L) : G) ∈ d.M from (show (x : c.L) ∈ d.M.subgroupOf c.L by
          rw [← he]
          exact x.property),
        component_le c (x : c.L).property⟩⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  rintro _ ⟨x, hx, rfl⟩
  change ((x : c.L) : G) ∈ d.Yplus
  rw [hres]
  exact ⟨f x, residual_map_le 3 f (mem_map_of_mem f hx), rfl⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
