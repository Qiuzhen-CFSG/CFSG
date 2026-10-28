module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingSetup
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction

/-!
# The original nonbinary MS-pair hypotheses

In the original configuration, IS contains the full Sylow intersection,
and its two-core is R = O₂(I). The genuine C.2.7 input therefore supplies
an odd-index core witness; restriction to KR retains that same radical.
Its characteristic-normalizer control also supplies MS3 with normality
relative to KR. The two subgroup formulations are transported through
the actual inclusions, without assuming ambient normality.

The final constructor supplies every field of LinearThreeMSPair once the
full K/O₂(K) ≅ SL₃(F) marking is available. No MS hypothesis, odd-index
witness or characteristic condition is left as a callback. The quotient
recognition and C.1.34 module alternatives remain with the source assembly
owner `qt-d-1222-rankone-uniqueness-nonblock`.
Source: Aschbacher--Smith, original 4.3.8, printed p.616;
C.1.31, p.135, and C.4.1/C.4.4, pp.151--153.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem noCharacteristicNormal_of_relative {K R : Subgroup G}
    (h : MSCharacteristicCondition (R.subgroupOf (K ⊔ R))) :
    MSNoCharacteristicNormal K R := by
  let J := K ⊔ R
  let e : R.subgroupOf J ≃* R := subgroupOfEquivOfLe (show R ≤ J from le_sup_right)
  intro C hC hn
  let := hC
  let C₀ := C.map e.symm.toMonoidHom
  let : C₀.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr e a) y,
      characteristic_iff_le_comap.mp hC (MulAut.congr e a) hy, ?_⟩
    exact e.symm_apply_apply (a (e.symm y))
  have hm : C₀.map (R.subgroupOf J).subtype = (C.map R.subtype).subgroupOf J := by
    ext j
    constructor
    · rintro ⟨r,⟨a,ha,rfl⟩,rfl⟩
      exact ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,he⟩
      refine ⟨e.symm a,⟨a,ha,rfl⟩,?_⟩
      exact Subtype.ext he
  have hz : C₀ = ⊥ := h.eq_bot_of_normal C₀ (hm.symm ▸ hn)
  exact (map_eq_bot_iff_of_injective C e.symm.injective).mp hz

omit [Finite G] in
private theorem oddIndex_of_relative {K R : Subgroup G}
    (h : MSOddIndexRadical (R.subgroupOf (K ⊔ R))) : MSOddIndex K R := by
  let J := K ⊔ R
  obtain ⟨P,hp,ho,hcore⟩ := h
  refine ⟨P.map J.subtype, ?_, ?_, ?_⟩
  · apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    apply hp.ne
    apply map_injective J.subtype_injective
    rw [he, ←MonoidHom.range_eq_map, range_subtype]
  · have he : (P.map J.subtype).subgroupOf J = P :=
      P.comap_map_eq_self_of_injective J.subtype_injective
    rwa [he]
  · rw [←map_pCoreIn_of_injective 2 P J.subtype J.subtype_injective]
    change P.pCoreIn 2 = R.subgroupOf J at hcore
    rw [hcore, map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)]

theorem ms_characteristic (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    MSNoCharacteristicNormal (K c) (c.I.pCoreIn 2) :=
  noCharacteristicNormal_of_relative (join_msCharacteristic_from_source (c.block_source_input hf))

theorem ms_oddIndex (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    MSOddIndex (K c) (c.I.pCoreIn 2) := by
  let h := c.block_source_input hf
  have hIH : c.I ⊔ S c ≤ c.H := sup_le c.I_le_H inf_le_right
  have hRplus : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hIN : c.I ≤ normalizer (L : Set G) := c.I_le.trans
    (sup_le L.le_normalizer (hRplus.trans D.sylow_normalizes_component))
  have hIP : c.I ⊔ S c ≤ c.H ⊓ normalizer (L : Set G) :=
    le_inf hIH (sup_le hIN (inf_le_left.trans D.sylow_normalizes_component))
  obtain ⟨P,hP⟩ := c.sylow
  have hPS : (P : Subgroup c.H) ≤ (c.I ⊔ S c).subgroupOf c.H := by
    intro x hx
    apply (le_sup_right : S c ≤ c.I ⊔ S c)
    change (x : G) ∈ (T : Subgroup G) ⊓ c.H
    rw [←hP]
    exact mem_map_of_mem _ hx
  exact oddIndex_of_relative (msOddIndexRadical_join_from_source h
    (msOddIndexRadical_of_first_core h (c.I ⊔ S c) hIH hIP P hPS c.core_join))

theorem msPair_of_quotient {F : Type} [Field F] [Finite F]
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    LinearThreeMSPair KnownSimple.IsKnownSimple (K c) (c.I.pCoreIn 2) n F := by
  let h := c.block_source_input hf
  exact {
    positive := hn
    field_card := hF
    model := ⟨e⟩
    sqtk := (source_join_input h).setup.sqtk
    fitting := source_join_fitting h
    component := (source_join_input h).component
    radical := Or.inl (ms_oddIndex c D hf)
    characteristic := ms_characteristic c hf }
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
