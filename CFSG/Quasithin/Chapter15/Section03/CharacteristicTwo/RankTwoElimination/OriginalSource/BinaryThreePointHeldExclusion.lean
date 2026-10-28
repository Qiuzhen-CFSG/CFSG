module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSporadicPlacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreJoin
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5MovingCore

/-!
# Held is excluded at the original binary-three point

The actual smaller subgroup in C_G(z)/O₂(C_G(z)) is max5 if its containing
component is Held. Its moving core has a nontrivial central derived subgroup.
The original identity [Q′,L]=Q′ passes through the actual quotient and
contradicts that centrality. The full original Sylow and quotient are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93

private theorem max5_image_contradiction
    {X : Type*} [Group X] [Finite X] (B : Subgroup X)
    (eB : B ≃* Held.TwoLocalCandidates.subgroup 2)
    (hm : ⁅⁅LinearThree.commutatorCore B,LinearThree.commutatorCore B⁆,B⁆ =
      ⁅LinearThree.commutatorCore B,LinearThree.commutatorCore B⁆) : False := by
  let R := ⁅pCore 2 B,(⊤ : Subgroup B)⁆
  have hR : R.map B.subtype = LinearThree.commutatorCore B := by
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hi : ⁅⁅R,R⁆,(⊤ : Subgroup B)⁆ = ⁅R,R⁆ := by
    apply map_injective B.subtype_injective
    simpa only [map_commutator,hR,←MonoidHom.range_eq_map,range_subtype] using hm
  have hRe : R.map eB.toMonoidHom =
      ⁅pCore 2 (Held.TwoLocalCandidates.subgroup 2),(⊤ : Subgroup _)⁆ := by
    rw [map_commutator,pCore_map_iso,map_top_of_surjective eB.toMonoidHom eB.surjective]
  have hh := congrArg (Subgroup.map eB.toMonoidHom) hi
  simp only [map_commutator,hRe,map_top_of_surjective eB.toMonoidHom eB.surjective] at hh
  obtain ⟨hne,hz⟩ := Held.TwoLocalCandidates.Cores.max5_moving_core_derived
  exact hne (hh.symm.trans hz)

private theorem original_image_derived_identity
    {G : Type*} [Group G] [Finite G] (L C : Subgroup G) (hLC : L ≤ C)
    (hm : ⁅⁅LinearThree.commutatorCore L,LinearThree.commutatorCore L⁆,L⁆ =
      ⁅LinearThree.commutatorCore L,LinearThree.commutatorCore L⁆) :
    let B := (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))
    ⁅⁅LinearThree.commutatorCore B,LinearThree.commutatorCore B⁆,B⁆ =
      ⁅LinearThree.commutatorCore B,LinearThree.commutatorCore B⁆ := by
  let Q := LinearThree.commutatorCore L
  let q := QuotientGroup.mk' (pCore 2 C)
  have hQC : Q ≤ C := ((LinearThree.commutatorCore_le L).trans (L.pCoreIn_le 2)).trans hLC
  have hi : ⁅⁅Q.subgroupOf C,Q.subgroupOf C⁆,L.subgroupOf C⁆ =
      ⁅Q.subgroupOf C,Q.subgroupOf C⁆ := by
    apply map_injective C.subtype_injective
    simpa only [map_commutator,map_subgroupOf_eq_of_le hQC,
      map_subgroupOf_eq_of_le hLC] using hm
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hQ : (Q.subgroupOf C).map q = LinearThree.commutatorCore ((L.subgroupOf C).map q) :=
    binary_three_original_core_image_of_le L C hLC q hk
  have hh := congrArg (Subgroup.map q) hi
  simpa only [map_commutator,hQ] using hh

variable {G : Type*} [Group G] [Finite G]

/-- The original nonabelian large-distance source has no Held containing
component in its literal point quotient. -/
theorem binary_three_source_point_not_held
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    (hK : K.IsCComponent)
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (eK : K ≃* Held.He) : False := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let T := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  obtain ⟨hB,⟨eB⟩⟩ := point_centralizer_quotient_local d c.L e b z hLS P hP
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hSL : d.S ≤ normalizer c.L := le_sup_right.trans
    ((normal_subgroupOf_iff_le_normalizer (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp
      b.component_normal)
  have hPB : (P : Subgroup C) ≤ normalizer (c.L.subgroupOf C) := by
    rw [←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact hSL (hP ▸ mem_map_of_mem C.subtype hx)
  have hTB : (T : Subgroup (C ⧸ pCore 2 C)) ≤ normalizer (B : Set _) :=
    (map_mono (f := q) hPB).trans ((c.L.subgroupOf C).le_normalizer_map q)
  obtain ⟨⟨a⟩,_,_,_⟩ := binary_three_containing_held_placement T hB hK hBK hTB eB eK
  exact max5_image_contradiction B a (original_image_derived_identity c.L C
    (le_sup_left.trans hLS) (binary_three_large_distance_original_derived_full_commutation
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
