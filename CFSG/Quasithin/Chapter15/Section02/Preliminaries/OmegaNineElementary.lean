module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaNineExtension
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# The elementary-nine branch on the original chosen module

If Y* is the elementary branch, its action image also has order nine,
so its module kernel is trivial. The normal subgroup quotient identification
then gives C_Y(V)=O₂(Y). Source15.2.3(5) centralizes C_M(V)* and the two
star subgroups are disjoint. Additivity of three-rank, together with the
standing bound two, forces C_M(V)* to have order prime to three. Lifting
through its original two-kernel gives the same conclusion for C_M(V).

The sole branch premise is |Y*|=9, supplied by OmegaNineExtension's proved
classification. Source: Aschbacher--Smith15.2.3(1)(i), printed p.1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- In the elementary branch, the original module centralizer in Y is O₂(Y),
and the full original C_M(V) has order prime to three. -/
theorem source_omega_nine_elementary_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hcard : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = 9)
    (hstar : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (QuotientGroup.mk' (pCore 2 M))) = 9) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 ∧
      Nat.Coprime 3 (Nat.card (M ⊓ centralizer (V : Set G) : Subgroup G)) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let A := Y.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let P := A.map q
  let f := (actionHom M V hV.normalized).rangeRestrict
  let g := omegaStarActor hV.normalized ho
  let C := g.ker
  have hcore : pCore 2 M ≤ f.ker := source_omega_core_le_kernel hV.normalized ho
  have himage : Nat.card (P.map g) = 9 := by rwa [omegaStarActor_map]
  have hinj : Function.Injective (g.subgroupMap P) :=
    ((g.subgroupMap_surjective P).bijective_of_nat_card_le (by rw [hstar,himage])).1
  have hd : Disjoint P C := by
    apply disjoint_def.mpr
    intro x hx hk
    have hkg : g x = 1 := hk
    have hh : (⟨x,hx⟩ : P) = 1 :=
      hinj (Subtype.ext (hkg.trans (map_one g).symm))
    exact congrArg Subtype.val hh
  have hbound : A ⊓ f.ker ≤ pCore 2 M := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact disjoint_def.mp hd (mem_map_of_mem q hx.1) (show g (q x) = 1 from hx.2)
  have hYM : Y ≤ M := source_omega_caseIIResidual_le T hM.2 hV.normalized ho
  let : A.Normal := source_omega_lemma_15_2_3_2 T hM.2 hV.normalized ho
  have hcentral : P ≤ centralizer (C : Set (M ⧸ pCore 2 M)) := by
    dsimp only [C,g]
    rw [omegaStarActor_ker]
    exact le_sup_right.trans (source_omega_lemma_15_2_3_5 T hM.2 hu hV ho)
  have hrank : primeRank 3 (M ⧸ pCore 2 M) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup]
    exact (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hCr : primeRank 3 C = 0 := by
    have hPr : primeRank 3 P = 2 := source_omega_nine_star_rank hG T hM hu hV ho hcard
    have he := primeRank_sup_eq_add_of_disjoint_commuting P C hd hcentral 3
    have hr := (primeRank_subgroup_le 3 (P ⊔ C)).trans hrank
    omega
  constructor
  · have hAcore := pCore_subnormal_eq_comap 2 (inferInstance : A.Normal).isSubnormal
    have he : A ⊓ f.ker = A.pCoreIn 2 := by
      apply le_antisymm
      · intro x hx
        refine ⟨⟨x,hx.1⟩,?_,rfl⟩
        rw [hAcore]
        exact hbound hx
      · exact le_inf (pCoreIn_le 2 A)
          ((pCoreIn_le_of_subnormal 2 (inferInstance : A.Normal).isSubnormal).trans hcore)
    have hh := congrArg (Subgroup.map M.subtype) he
    rw [map_inf _ _ _ M.subtype_injective,
      map_pCoreIn_of_injective 2 A M.subtype M.subtype_injective,
      show A.map M.subtype = Y from map_subgroupOf_eq_of_le hYM,
      show f.ker = (actionHom M V hV.normalized).ker from MonoidHom.ker_rangeRestrict _,
      actionHom_ker,subgroupOf_map_subtype] at hh
    change Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2
    simpa only [← inf_assoc,
      inf_eq_left.mpr ((inf_le_left : Y ⊓ centralizer (V : Set G) ≤ Y).trans hYM)] using hh
  · have hqk : IsPGroup 2 (q.subgroupMap f.ker).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    obtain ⟨k,hk⟩ := hqk.exists_card_eq
    have hCp : Nat.Coprime 3 (Nat.card (q.subgroupMap f.ker).ker) := by
      rw [hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    have he := primeRank_eq_of_surjective_of_coprime 3 (q.subgroupMap f.ker)
      (q.subgroupMap_surjective f.ker) hCp
    have hgker : C = f.ker.map q := QuotientGroup.ker_lift _ _ _
    rw [← hgker] at he
    have hCmap : f.ker.map M.subtype = M ⊓ centralizer (V : Set G) := by
      rw [show f = (actionHom M V hV.normalized).rangeRestrict from rfl,
        MonoidHom.ker_rangeRestrict,actionHom_ker,subgroupOf_map_subtype,inf_comm]
    have he2 := Theory.GroupTheory.primeRank_equiv 3
      ((f.ker.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCmap))
    have hz : primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) = 0 := by omega
    exact Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)

end CFSG.Quasithin.Chapter15.Section02
end
