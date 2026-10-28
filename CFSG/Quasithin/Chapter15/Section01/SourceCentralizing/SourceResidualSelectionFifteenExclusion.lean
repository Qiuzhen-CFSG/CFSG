module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFifteenAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionFifteenKernel
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Quasithin.CoprimeRank

/-!
# The rank obstruction in the original full marked-five row

Finite descent inside an actual third maximal local selects an original
H-star subgroup there. Its independently proved wreath quotient gives its
two-residual three-rank at least two. The original local residual theorem
places that residual in the centralizer of the Thompson fixed plane, which
is the third local's own module. All subgroup inclusions are retained. The actual symmetric-three action of
the third local bounds that same centralizer rank by one, contradicting
the original marked-five source without any global residual assumption.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private def cubicPermutation : Multiplicative (ZMod 3) →* Equiv.Perm (Fin 3) where
  toFun a := (Equiv.swap 0 1 * Equiv.swap 1 2) ^ a.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem cubicPermutation_injective : Function.Injective cubicPermutation := by decide +kernel

private theorem symmetricThree_wreath_threeRank_ge_two :
    2 ≤ primeRank 3 (RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  let E := Multiplicative (ZMod 2) → Multiplicative (ZMod 3)
  let f : E →* RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)) :=
    { toFun := fun a => ⟨fun i => cubicPermutation (a i),1⟩
      map_one' := by
        apply RegularWreathProduct.ext
        · funext i
          exact cubicPermutation.map_one
        · rfl
      map_mul' := by
        intro a b
        apply RegularWreathProduct.ext
        · funext i
          change cubicPermutation (a i * b i) =
            cubicPermutation (a i) * cubicPermutation (b (1⁻¹ * i))
          simp only [inv_one,one_mul,map_mul]
        · rfl }
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 2) ?_ ?_ f ?_
  · intro a
    funext i
    exact (show ∀ z : Multiplicative (ZMod 3), z^3=1 by decide +kernel) (a i)
  · norm_num [E,Nat.card_eq_fintype_card]
  · intro a b he
    funext i
    exact cubicPermutation_injective (congrArg (fun z => z.left i) he)

private theorem exists_HStar_le_third
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) :
    ∃ H : Subgroup G, H ≤ N ∧ H ∈ Chapter3.HStar (T : Subgroup G) M := by
  have ho : N ∈ Chapter1.HOver G (T : Set G) ∧ ¬ N ≤ M :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩,
      fun hn => hNM (hN.1.eq_of_le h.maximal.1.1.1 hn)⟩
  exact Finite.exists_le_minimal (p := fun H : Subgroup G =>
    H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ M) ho

private theorem wreath_residual_rank_ge_two {H : Subgroup G}
    (e : (H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) :
    2 ≤ primeRank 3 ((pResidual 2 H).map H.subtype) := by
  rw [← primeRank_equiv 3 ((pResidual 2 H).equivMapOfInjective
    H.subtype H.subtype_injective),
    ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
  have hh := primeRank_quotient_le_of_isTwoGroup 3 (by decide : Odd 3)
    (pCore 2 H) pCore_isPGroup
  rw [primeRank_equiv 3 e] at hh
  exact symmetricThree_wreath_threeRank_ge_two.trans hh

/-- The actual original H-star residual inside the third local gives
three-rank at least two to its own local-module centralizer. -/
theorem ChosenSmallSource.marked_five_third_centralizer_rank_ge_two
    {T : Sylow 2 G} {M Mc V N : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    2 ≤ primeRank 3 (N ⊓ centralizer (localModule T N : Set G) : Subgroup G) := by
  obtain ⟨H,hHN,hH⟩ := exists_HStar_le_third h hN hNM
  obtain ⟨e⟩ := h.HStar_wreath_of_marked_five hd hH
  have hres := h.prepared.source_thompsonFixed_local_residuals h.ambient T h.empty
    h.maximal h.centralizing H hH
  have he := (h.marked_five_third_module_and_normalizer hd hfull hN hNM hNMc).1
  have hle : (pResidual 2 H).map H.subtype ≤
      N ⊓ centralizer (localModule T N : Set G) := by
    rw [he]
    exact le_inf ((map_subtype_le _).trans hHN) hres
  exact (wreath_residual_rank_ge_two e).trans (Theory.GroupTheory.primeRank_le_of_injective 3
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))

/-- The original full marked-five source with Sylow image of order four
is impossible. This uses only the prior-free H-star residual centralization,
not the global residual containment of 15.1.14. -/
theorem source_chosen_full_marked_five_contradiction
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hfour : Nat.card (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict) = 4)
    (hfull : V = localModule T M) : False := by
  obtain ⟨N,hN,hNM,hNMc⟩ := h.exists_third_of_marked_five hd
  obtain ⟨e⟩ := h.marked_five_third_action_symmetricThree hd hfour hfull hN hNM hNMc
  have hlo := h.marked_five_third_centralizer_rank_ge_two hd hfull hN hNM hNMc
  have hhi := source_local_symmetricThree_centralizer_rank h.ambient T h.empty hN
    h.partner h.many hNMc e
  omega

end CFSG.Quasithin.Chapter15.Section02
