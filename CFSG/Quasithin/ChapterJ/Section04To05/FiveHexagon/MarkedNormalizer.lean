module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedInverter
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer

/-!
# The marked original-source five-normalizer

The literal first-endpoint equivalence carries the proved model I into the
original endpoint. Its image has order16 and type C₄ × C₄, contains the
original z and the constructed inverter, and supplements the original B₅
in its endpoint normalizer. The cyclic diagonal is retained under that same
map. Only the earlier endpoint and five-subgroup markings are used.
Source: Aschbacher--Smith, proof of J.4.7, printed pp.442--443.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Subgroup
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.RootRelations

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- Transport through precisely the endpoint equivalence used for the inverter. -/
def sourceI : Subgroup G := (I.subgroupOf first).map (F.subtype.comp e.toMonoidHom)

/-- The same marked cyclic diagonal, before identifying its original Q₀ intersection. -/
def sourceIz : Subgroup G := (Iz.subgroupOf first).map (F.subtype.comp e.toMonoidHom)

omit [Finite G] in
private theorem sourceMap_injective : Function.Injective (F.subtype.comp e.toMonoidHom) :=
  F.subtype_injective.comp e.injective

private theorem I_le_first : I ≤ first := I_le_sylow.trans sylow_le_first

private theorem five_le_first : five ≤ first := zpowers_le.mpr rotation_mem_first

private theorem local_five : five.subgroupOf first = zpowers modelRotation := by
  apply map_injective first.subtype_injective
  rw [map_subgroupOf_eq_of_le five_le_first, MonoidHom.map_zpowers]
  rfl

private theorem source_five
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    (five.subgroupOf first).map e.toMonoidHom = (B5Image B5).subgroupOf F := by
  apply map_injective F.subtype_injective
  rw [map_map, local_five, hfive]
  apply (map_subgroupOf_eq_of_le ?_).symm
  rw [← hfive]
  rintro x ⟨a,ha,rfl⟩
  exact (e a).property

omit [Finite G] in
/-- The model subgroup keeps its exact order in the original ambient group. -/
theorem sourceI_card : Nat.card (sourceI e) = 16 := by
  rw [sourceI, card_map_of_injective (sourceMap_injective e)]
  exact (Nat.card_congr (subgroupOfEquivOfLe I_le_first).toEquiv).trans I_card

omit [Finite G] in
/-- The actual image, rather than a separately chosen C₄², has the required type. -/
theorem sourceI_equiv :
    Nonempty (sourceI e ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  obtain ⟨a⟩ := I_equiv
  exact ⟨((I.subgroupOf first).equivMapOfInjective (F.subtype.comp e.toMonoidHom)
    (sourceMap_injective e)).symm.trans ((subgroupOfEquivOfLe I_le_first).trans a)⟩

/-- Both original involutions belong to the same transported I. -/
theorem source_marks_mem (hz : (e modelZ : G) = c.z) :
    c.z ∈ sourceI e ∧ sourceU e ∈ sourceI e := by
  have hq : q ∈ I := mem_sup_right (mem_zpowers q)
  have hs : s ∈ I := mem_sup_left (mem_zpowers s)
  have hu : u ∈ I := q_square ▸ I.pow_mem hq 2
  have hzI : z ∈ I := diagonal_square ▸ I.pow_mem (I.mul_mem hs (I.inv_mem hq)) 2
  refine ⟨?_, ?_⟩
  · rw [← hz]
    exact mem_map_of_mem _ hzI
  · exact mem_map_of_mem _ hu

/-- The literal original endpoint normalizer is B₅ times the transported I. -/
theorem source_normalizer
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    F ⊓ normalizer (B5Image B5 : Set G) = B5Image B5 ⊔ sourceI e := by
  have hf := source_five B5 e hfive
  have hmodel : normalizer ((five.subgroupOf first : Subgroup first) : Set first) =
      five.subgroupOf first ⊔ I.subgroupOf first := by
    rw [← subgroupOf_normalizer_eq five_le_first]
    have hh := congrArg (fun A : Subgroup (ReeF4.Model 0) => A.subgroupOf first)
      first_inf_normalizer
    have he : (first ⊓ fiveNormalizer).subgroupOf first =
        fiveNormalizer.subgroupOf first := by
      ext x
      exact and_iff_right x.property
    rw [he, subgroupOf_sup five_le_first I_le_first] at hh
    exact hh
  have hm := congrArg (fun A : Subgroup first => A.map e.toMonoidHom) hmodel
  rw [map_equiv_normalizer_eq, hf, Subgroup.map_sup] at hm
  have hB : B5Image B5 ≤ F := by
    rw [← hfive]
    rintro x ⟨a,ha,rfl⟩
    exact (e a).property
  have hh := congrArg (fun A : Subgroup F => A.map F.subtype) hm
  rw [← subgroupOf_normalizer_eq hB, subgroupOf_map_subtype, Subgroup.map_sup,
    map_map, local_five, hfive] at hh
  simpa only [inf_comm, sourceI, map_map] using hh

/-- The transported I lies in the original involution centralizer H. -/
theorem sourceI_le_H (hz : (e modelZ : G) = c.z) : sourceI e ≤ d.toTypeRuSetup.H := by
  rintro x ⟨a,ha,rfl⟩
  rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff, ← hz]
  have hc : a*modelZ = modelZ*a := by
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (first_eq_centralizer_z ▸ a.property)
  exact congrArg (fun a : F => (a : G)) (by simpa only [map_mul] using congrArg e hc)

/-- Its normalization is normalization of the original specified B₅. -/
theorem sourceI_le_normalizer
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    sourceI e ≤ normalizer (B5Image B5 : Set G) := by
  exact (show sourceI e ≤ B5Image B5 ⊔ sourceI e from le_sup_right).trans
    ((source_normalizer B5 e hfive).symm.le.trans inf_le_right)

private theorem Iz_le_I : Iz ≤ I := zpowers_le.mpr
  (I.mul_mem (mem_sup_left (mem_zpowers s)) (I.inv_mem (mem_sup_right (mem_zpowers q))))

omit [Finite G] in
/-- The same source diagonal is cyclic of order four. -/
theorem sourceIz_card : Nat.card (sourceIz e) = 4 := by
  rw [sourceIz, card_map_of_injective (sourceMap_injective e)]
  exact (Nat.card_congr (subgroupOfEquivOfLe (Iz_le_I.trans I_le_first)).toEquiv).trans Iz_card

omit [Finite G] in
/-- The marked diagonal remains inside the same source I. -/
theorem sourceIz_le_I : sourceIz e ≤ sourceI e := map_mono (fun _ hx => Iz_le_I hx)

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
