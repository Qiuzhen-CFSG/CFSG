module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointExactFlags
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointJoinResidual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceNormalizer
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.AdjacentResidualNormalizer

/-!
# The original binary-three point has no PSL5(2) containing component

The actual restricted Sylow join is one of the two adjacent flags, with
B its literal two-residual. Perfectness makes B fix the small block, so
the full 2+3 maximal parabolic normalizes B and has three-rank at least
two. This contradicts the original point normalizer bound of one.
All point kernels and the actual restricted Sylow are retained.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]

/-- The actual original point quotient cannot contain a normal PSL5(2)
subgroup containing the same original image B. -/
theorem binary_three_source_point_not_psl_five
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
    (z : G) (hzH : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1)
    (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 5 2) : False := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  let D := B.subgroupOf K
  obtain ⟨T,hT,a,v,_,hflag⟩ := binary_three_source_five_adjacent_flags
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  obtain ⟨_,T₁,hT₁,hres⟩ := binary_three_point_join_residual d c.L b z hLS P hP K hBK
  have hTT : T₁=T := Sylow.ext (hT₁.trans hT.symm)
  subst T₁
  let J := D ⊔ (T : Subgroup K)
  let B' := D.map a.toMonoidHom
  have hres' : (pResidual 2 (J.map a.toMonoidHom)).map (J.map a.toMonoidHom).subtype=B' := by
    rw [←map_embedded_pResidual,hres]
  let : Group.IsPerfect (c.L.subgroupOf (c.L ⊔ d.S)) := b.component.perfect
  let i := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  let iC := subgroupOfEquivOfLe (show c.L ≤ C from le_sup_left.trans hLS)
  let : Group.IsPerfect (c.L.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := iC.symm.toMonoidHom) iC.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective (c.L.subgroupOf C))
  let iK := subgroupOfEquivOfLe hBK
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := iK.symm.toMonoidHom) iK.symm.surjective
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective (a.toMonoidHom.subgroupMap_surjective D)
  have hmapT : (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
      (T : Subgroup K).map a.toMonoidHom := rfl
  have htwoN : 2 ≤ primeRank 3 (normalizer (B' : Set (LinearGroup 5))) := by
    rcases hflag with hflag | hflag
    · apply BinaryLinear.SevenFlagCore.adjacent_perfect_residual_normalizer_rank v false B'
      change (pResidual 2 (cutStabilizer v ({0,1} : Set (Fin 4)))).map
        (cutStabilizer v ({0,1} : Set (Fin 4))).subtype=B'
      have hj : J.map a.toMonoidHom=cutStabilizer v ({0,1} : Set (Fin 4)) := by
        simpa only [J,D,B,q,C,Subgroup.map_sup,hmapT] using hflag
      exact (congrArg (fun A : Subgroup (LinearGroup 5) => (pResidual 2 A).map A.subtype) hj).symm.trans hres'
    · apply BinaryLinear.SevenFlagCore.adjacent_perfect_residual_normalizer_rank v true B'
      change (pResidual 2 (cutStabilizer v ({2,3} : Set (Fin 4)))).map
        (cutStabilizer v ({2,3} : Set (Fin 4))).subtype=B'
      have hj : J.map a.toMonoidHom=cutStabilizer v ({2,3} : Set (Fin 4)) := by
        simpa only [J,D,B,q,C,Subgroup.map_sup,hmapT] using hflag
      exact (congrArg (fun A : Subgroup (LinearGroup 5) => (pResidual 2 A).map A.subtype) hj).symm.trans hres'
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G)=⊤ := top_unique (fun x _ => hTS x.property)
    rw [ht,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hone := binary_three_source_point_quotient_normalizer_rank
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hzH hz1 hLS P hP g hgT hgS
  have hmapN : (normalizer (D : Set K)).map K.subtype ≤ normalizer (B : Set (C ⧸ pCore 2 C)) := by
    rintro x ⟨k,hk,rfl⟩
    have hh : k ∈ (normalizer (B : Set (C ⧸ pCore 2 C))).subgroupOf K := by
      rw [subgroupOf_normalizer_eq hBK]
      exact hk
    exact hh
  have hrK : primeRank 3 (normalizer (D : Set K)) ≤ 1 := by
    rw [primeRank_equiv 3 ((normalizer (D : Set K)).equivMapOfInjective K.subtype K.subtype_injective)]
    exact (primeRank_mono 3 hmapN).trans hone
  have hrM : primeRank 3 (normalizer (B' : Set (LinearGroup 5))) ≤ 1 := by
    have hh := primeRank_equiv 3 ((normalizer (D : Set K)).equivMapOfInjective a.toMonoidHom a.injective)
    rw [map_equiv_normalizer_eq] at hh
    exact hh ▸ hrK
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
