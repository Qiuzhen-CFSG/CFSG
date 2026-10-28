module
public import CFSG.Quasithin.Chapter5.A5Source.ConjugateCore
public import Theory.GroupTheory.PGroup.DihedralSquareAutomorphisms

/-!
# The original 5.1.7 normalizer endgame on the dihedral square

Once the source conjugate-core geometry identifies Baum(T) with an
 elementary central factor times D8×D8, its full normalizer has two-residual
normalizing Q=O2(L Baum(T)). Uniqueness over LT controls N(Q), and the
original Sylow supplements that two-residual. This is the literal Chapter5
consumer of the intrinsic dihedral-square automorphism theorem.
Source: Aschbacher--Smith 5.1.7(1), printed p.634.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
open ChapterC.Section05.CounterexampleCharacteristic
variable {G E : Type*} [Group G] [Finite G] [Group E] [Finite E] [IsElementaryAbelian 2 E]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem baumann_normalizer_of_dihedral_square
    (e : baumann (T : Subgroup G) ≃* E × (DihedralGroup 4 × DihedralGroup 4)) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let N := normalizer (S : Set G)
  have hTS : (T : Subgroup G) ≤ N :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hQS : Q ≤ S := baumann_core_le_of_escape d hout
  have hVQ : V ≤ Q := by
    change V ≤ (L ⊔ baumann (T : Subgroup G)).pCoreIn 2
    rw [baumann_core_product_of_escape d hout]
    exact le_sup_left
  have hnorm : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) := by
    apply (show L ⊔ (T : Subgroup G) ≤ normalizer ((L ⊔ S : Subgroup G) : Set G) from ?_).trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ S) (pCore 2 ↥(L ⊔ S)))
    apply sup_le ((show L ≤ L ⊔ S from le_sup_left).trans (L ⊔ S).le_normalizer)
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (d.normalizes_L ht),
      mem_normalizer_iff_map_conj_eq.mp (hTS ht)]
  have hNQ : normalizer (Q : Set G) ≤ normalizer (L : Set G) :=
    normalizer_of_local_normal d Q
      (fun h => d.chosen.ne_bot (bot_unique (hVQ.trans_eq h)))
      (hQS.trans inf_le_left) (normal_subgroupOf_of_le_normalizer hnorm)
  have hZ : (center S).map S.subtype ≤ Q := by
    have he := ReducedMarking.normal_short_extension_centralizer L S hb.2.1
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left))
      (inf_le_left.trans d.normalizes_L)
    change (L ⊔ S) ⊓ centralizer ((blockU L).map L.subtype : Set G) = Q at he
    rw [hV] at he
    apply le_trans ?_ he.le
    refine le_inf ((map_subtype_le _).trans le_sup_right) ?_
    rintro _ ⟨z,hz,rfl⟩ v hv
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨v,hQS (hVQ hv)⟩)
  have hres : (pResidual 2 N).map N.subtype ≤ normalizer (L : Set G) :=
    (pResidual_normalizer_le_normalizer_of_dihedral_square S Q e hQS hZ).trans hNQ
  have hgen := congrArg (Subgroup.map N.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTS))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTS,
    ←MonoidHom.range_eq_map,range_subtype] at hgen
  exact hout (hgen.symm.le.trans (sup_le hres d.normalizes_L))

end CFSG.Quasithin.Chapter5.A5Source
