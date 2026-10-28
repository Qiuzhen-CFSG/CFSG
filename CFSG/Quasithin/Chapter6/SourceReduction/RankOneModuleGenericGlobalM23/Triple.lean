module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Sylow
public import Theory.GroupTheory.Recognition.QuasithinM23.TripleNormalizer
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Compatible pair and triple stabilizers in the original exceptional local

Use the same A₇ quotient map that marks the original H and K as setwise
and pointwise pair stabilizers. The image of the original S is an elementary
four-group fixing that pair. Its fixed triple has normalizer precisely the
image of M ∩ J, by the intrinsic two-root-plane calculation. Pulling back
through the full two-core gives the original intersection, of order 1152.

Source: Aschbacher–Smith 5.2.11(2), printed pp.653–654
(`refs/quasithin.pdf`). Both orientations and the selected field from the
original compatible comparison are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

theorem Preparation.linear_exceptional_pair_triple_marking
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) :
    ∃ e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7),
      ∃ (i j : Fin 7) (s : Finset (Fin 7)), i ≠ j ∧ s.card = 3 ∧ i ∈ s ∧ j ∈ s ∧
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
        (residual H).subgroupOf J =
          (fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
        H.subgroupOf J =
          (MulAction.stabilizer (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
        (normalizer (L : Set G)).subgroupOf J =
          (MulAction.stabilizer (alternatingGroup (Fin 7)) (s : Set (Fin 7))).comap q := by
  obtain ⟨e,i,j,hij,hK,hHm,_⟩ := d.linear_exceptional_pair_marking h hH hp F hm hF he hJ hKJ
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  obtain ⟨hgen,_,_,_,hNJ,_⟩ := d.linear_exceptional_sylow_planes h hH hp F hm hF he hJ hKJ
  have hSK : sourceS L H ≤ residual H := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 1
  have hSJ : sourceS L H ≤ J := hSK.trans hKJ.le
  have hVS : L.pCoreIn 2 ≤ sourceS L H := hgen ▸ le_sup_left
  have hUS : J.pCoreIn 2 ≤ sourceS L H := hgen ▸ le_sup_right
  have hVJ : L.pCoreIn 2 ≤ J := hVS.trans hSJ
  have hUJ : J.pCoreIn 2 ≤ J := pCoreIn_le 2 J
  let Q := ((sourceS L H).subgroupOf J).map q
  have hker : q.ker ≤ (sourceS L H).subgroupOf J := by
    intro x hx
    rw [hk] at hx
    exact hUS (mem_map_of_mem J.subtype hx)
  have hpre : Q.comap q = (sourceS L H).subgroupOf J := comap_map_eq_self hker
  have hnormal : (normalizer (Q : Set (alternatingGroup (Fin 7)))).comap q =
      (normalizer (L : Set G)).subgroupOf J := by
    rw [comap_normalizer_eq_of_surjective Q hq,hpre,←subgroupOf_normalizer_eq hSJ]
    ext x
    exact (show (x : G) ∈ normalizer (sourceS L H : Set G) ↔
      (x : G) ∈ normalizer (L : Set G) from
      ⟨fun hx => (hNJ.le ⟨hx,x.property⟩).1,
       fun hx => (hNJ.ge ⟨hx,x.property⟩).1⟩)
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) := by
    intro hK
    exact hKJ.ne (hK.2 J hJ.1 hKJ.le).symm
  obtain ⟨_,_,_,hcores,_,_,_,_,hScard,_⟩ :=
    d.linear_nonmaximal_core_geometry h hH hp F hm hF he hnonmax
  have haV : IsElementaryAbelian 2 (pCore 2 L) := (hcores 0).1
  let := haV
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := haV.map L.subtype
  let : IsElementaryAbelian 2 ((L.pCoreIn 2).subgroupOf J) := IsElementaryAbelian.subgroupOf hVJ
  have hUpre : (J.pCoreIn 2).subgroupOf J = pCore 2 J :=
    comap_map_eq_self_of_injective J.subtype_injective _
  have hQmap : Q = ((L.pCoreIn 2).subgroupOf J).map q := by
    change ((sourceS L H).subgroupOf J).map q = _
    rw [←hgen,subgroupOf_sup hVJ hUJ,hUpre,Subgroup.map_sup]
    have hzero : (pCore 2 J).map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hk.ge
    rw [hzero,sup_bot_eq]
  let : IsElementaryAbelian 2 Q := by
    rw [hQmap]
    exact IsElementaryAbelian.map q
  have hQcard : Nat.card Q = 4 := by
    have hc := IsElementaryAbelian.card_inf_ker_mul_card_map ((sourceS L H).subgroupOf J) q
    rw [inf_eq_right.mpr hker,hk,
      Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv,hScard] at hc
    have hcore := (d.linear_overcomponent_core h hH.1.1.2 hp F hm hF he hJ.1 hKJ.le).1
    have hcard : Nat.card (pCore 2 J) = 16 := by
      have hc' := congrArg (fun X : Subgroup G => Nat.card X) hcore
      change Nat.card ((pCore 2 J).map J.subtype) =
        Nat.card ((pCore 2 (residual H)).map (residual H).subtype) at hc'
      rw [card_map_of_injective J.subtype_injective,
        card_map_of_injective (residual H).subtype_injective] at hc'
      exact hc'.trans (hcores 1).2
    rw [hcard] at hc
    change 16 * Nat.card Q = 64 at hc
    omega
  have hfix (k : Fin 7) (hk : k ∈ ({i,j} : Set (Fin 7))) (x : Q) : x.val.val k = k := by
    obtain ⟨y,hy,hxy⟩ := x.property
    have hyK : y ∈ (residual H).subgroupOf J := hSK hy
    rw [hK] at hyK
    have hh := hyK ⟨k,hk⟩
    change (q y).val k = k at hh
    rw [hxy] at hh
    exact hh
  obtain ⟨s,hs,hi,hj,_,hN⟩ := QuasithinM23.four_fixing_pair_normalizer Q hQcard i j hij
    (hfix i (by simp)) (hfix j (by simp))
  refine ⟨e,i,j,s,hij,hs,hi,hj,hK,hHm,?_⟩
  exact hnormal.symm.trans (congrArg (Subgroup.comap q) hN)

/-- The original maximal-local intersection has the order of the full triple preimage. -/
theorem Preparation.linear_exceptional_intersection_card
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) :
    Nat.card (normalizer (L : Set G) ⊓ J : Subgroup G) = 1152 := by
  obtain ⟨e,i,j,s,_,hs,_,_,_,_,hM⟩ :=
    d.linear_exceptional_pair_triple_marking h hH hp F hm hF he hJ hKJ
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  let C := (normalizer (L : Set G)).subgroupOf J
  have hker : q.ker ≤ C := by
    change q.ker ≤ (normalizer (L : Set G)).subgroupOf J
    rw [hM]
    exact ker_le_comap q _
  have hmap : C.map q = MulAction.stabilizer (alternatingGroup (Fin 7)) (s : Set (Fin 7)) := by
    rw [show C = _ from hM,map_comap_eq_self_of_surjective hq]
  have hn := (d.block_overcomponent_parameter h hH.1.1.2 hp F hm hF (.inl he) hJ.1 hKJ).1
  have hcard := (d.linear_overcomponent_action h hH.1.1.2 hp F hm hF he hJ.1 hKJ.le).2.1
  rw [hn] at hcard
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map C q
  rw [inf_eq_right.mpr hker,hk,hmap,QuasithinM23.seven_triple_stabilizer_card s hs,hcard] at hc
  have heq : Nat.card C = Nat.card (normalizer (L : Set G) ⊓ J : Subgroup G) := by
    rw [←card_map_of_injective (K := C) J.subtype_injective]
    rw [show C = (normalizer (L : Set G)).subgroupOf J from rfl,subgroupOf_map_subtype]
  rw [←heq]
  exact hc.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
