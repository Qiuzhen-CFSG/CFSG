module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalDisplacement

/-!
# The normalizer index at the original displacement point

In the remaining large-distance branch of original 15.3.23, put F equal
to the third lower commutator of the original core and choose its S-fixed
involution z. The section action of N_G(L) intersect C_G(z) has kernel of
order prime to three, and its image lies in Aut(PSL3(2)), of order 336.
The original L supplies a factor three, so this normalizer has three-part
exactly three. The actual elementary nine in C_G(z) then forces its index
to be divisible by three.

The final theorem applies this calculation at the generator of
[F,O2(LS)], discharging CommonFacts and Earlier from the nonabelian
large-distance hypotheses. It retains the original G, local data, marked
component, full Sylow and involution centralizer. The remaining consumer is
`source_lemma_15_3_23_of_large_distance`, followed by the original 15.3.13
assembly in `SourceRankTwo.BinaryFourAssembly`.

These constraints do not yet exclude the point-centralizer configuration.
The outstanding ambient argument must use the original core and its
T-conjugate to exclude the proper local-component embedding; rank and
normalizer index alone do not supply that argument. No universal MS
classification or original fixed-factor centrality is asserted here.

Source: Aschbacher--Smith 15.3.23, printed pp.1128--1129; the original
intrinsic four comes from MS93 (4.5), printed pp.895--900.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem point_normalizer_nine_not_dvd
    (L : Subgroup G) (e : (L ⧸ pCore 2 L) ≃* PSL(3,ZMod 2)) (z : G)
    (hk : Nat.Coprime 3 (Nat.card
      (Chapter4.sectionCentralizer L ⊓ centralizer ({z} : Set G) : Subgroup G))) :
    ¬ 9 ∣ Nat.card (normalizer (L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  let N := normalizer (L : Set G) ⊓ centralizer ({z} : Set G)
  let f := (ComponentIntersection.InnerSplitting.sectionAction L).comp
    (inclusion (show N ≤ normalizer (L : Set G) from inf_le_left))
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    let j : f.ker →* (Chapter4.sectionCentralizer L ⊓ centralizer ({z} : Set G) : Subgroup G) := {
      toFun x := ⟨((x : N) : G),
        (ComponentIntersection.InnerSplitting.sectionAction_eq_one_iff L _).mp x.property,
        (x : N).property.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    exact hk.coprime_dvd_right (card_dvd_of_injective j (by
      intro x y hh
      exact Subtype.ext (Subtype.ext (congrArg
        (fun w : (Chapter4.sectionCentralizer L ⊓ centralizer ({z} : Set G) : Subgroup G) => (w : G)) hh))))
  have hcard := f.ker.card_mul_index
  rw [index_ker] at hcard
  have hAut : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  intro hdiv
  change 9 ∣ Nat.card N at hdiv
  rw [←hcard] at hdiv
  have h9 : 9 ∣ Nat.card f.range :=
    (hker.pow_left 2).dvd_of_dvd_mul_left hdiv
  have hbad := h9.trans f.range.card_subgroup_dvd_card
  rw [hAut] at hbad
  norm_num at hbad

private theorem three_dvd_index_of_nine
    {C : Type*} [Group C] [Finite C] (N : Subgroup C)
    (hC : 9 ∣ Nat.card C) (hN : ¬ 9 ∣ Nat.card N) : 3 ∣ N.index := by
  by_contra hidx
  have hi := (Nat.prime_three.coprime_iff_not_dvd.mpr hidx).pow_left 2
  rw [←N.card_mul_index] at hC
  exact hN (hi.dvd_of_dvd_mul_right hC)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
include hG hempty hM hu hmany hI htwo hf e b t common earlier

/-- At every nonidentity intrinsic-four point, the original component
normalizer has three-part exactly three, a stronger statement than its
three-rank bound. -/
theorem binary_three_source_point_normalizer_three_part
    (z : G) (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    3 ∣ Nat.card (normalizer (c.L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ∧
      ¬ 9 ∣ Nat.card (normalizer (c.L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  have hk := (binary_three_source_point_normalizer_rank
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1).1
  refine ⟨?_,point_normalizer_nine_not_dvd c.L e z hk⟩
  have hLC : c.L ≤ centralizer ({z} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (((intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.2.trans inf_le_right) hz x hx)
  have h3 : 3 ∣ Nat.card (c.L ⧸ pCore 2 c.L) := by
    rw [Nat.card_congr (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))).toEquiv,
      Matrix.PSL3Two.card_SL]
    decide
  exact (h3.trans (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 c.L))
    (QuotientGroup.mk'_surjective _))).trans
      (card_dvd_of_le (le_inf c.L.le_normalizer hLC))

/-- The actual elementary nine forces a factor three in the index of the
component normalizer inside the same point centralizer. -/
theorem binary_three_source_point_normalizer_index
    (z : G) (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    3 ∣ ((normalizer (c.L : Set G)).subgroupOf (centralizer ({z} : Set G))).index := by
  obtain ⟨a,v,E,_,_,_,_,_,_,_,_,hEC,_,_,_,hcard⟩ :=
    binary_three_source_intrinsic_point_elementary_nine
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  have hC : 9 ∣ Nat.card (centralizer ({z} : Set G)) := hcard ▸ card_dvd_of_le hEC
  let C := centralizer ({z} : Set G)
  let N := (normalizer (c.L : Set G)).subgroupOf C
  let en : N ≃* (normalizer (c.L : Set G) ⊓ C : Subgroup G) :=
    N.equivMapOfInjective C.subtype C.subtype_injective |>.trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype (normalizer (c.L : Set G)) C))
  have hN : ¬ 9 ∣ Nat.card N := by
    rw [Nat.card_congr en.toEquiv]
    exact (binary_three_source_point_normalizer_three_part
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1).2
  exact three_dvd_index_of_nine N hC hN

omit common earlier in
/-- The original large-distance input supplies the displacement involution
and the exact three-part and index constraints on its component normalizer.
All earlier MS path premises are discharged on the unchanged marking. -/
theorem binary_three_large_distance_displacement_normalizer
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ z : G, orderOf z = 2 ∧
      ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ = zpowers z ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      (d.T : Subgroup G) ⊓ centralizer ({z} : Set G) = d.S ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      3 ∣ Nat.card (normalizer (c.L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ∧
      ¬ 9 ∣ Nat.card (normalizer (c.L : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) ∧
      3 ∣ ((normalizer (c.L : Set G)).subgroupOf (centralizer ({z} : Set G))).index ∧
      ∃ P : Sylow 2 (centralizer ({z} : Set G)),
        (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S := by
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  obtain ⟨z,hz2,hline,hLS,hTS,hout,_,P,hP⟩ :=
    binary_three_large_distance_displacement_point hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz2; omega
  have he := (binary_three_source_original_displacement_eq_fixedLine
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier).1
  have hz : z ∈ intrinsicFour c.L := by
    have hzdisp : z ∈ ⁅intrinsicFour c.L, (c.L ⊔ d.S).pCoreIn 2⁆ := hline.symm ▸ mem_zpowers z
    rw [he] at hzdisp
    exact hzdisp.1
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ :=
      top_unique (fun x _ => hTS x.property)
    have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    rw [ht,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨h3,h9⟩ := binary_three_source_point_normalizer_three_part
    hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1
  exact ⟨z,hz2,hline,hLS,hTS,hout,h3,h9,
    binary_three_source_point_normalizer_index
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hz1 g hgT hgS,P,hP⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
