module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The literal original middle core has center Phi and derived order eight

The graph second hat is a central extension of its intersection with the
actual core by the graph Z-layer. Its known center is the first hat, and
its derived subgroup is the natural eight. Intersecting with the actual
core and using the proved whole fixed-factor equality identifies the
center with Phi. The intrinsic core equivalence then transports both
identities to D=C_Q(Phi(Q)) in the original ambient group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {G : Type*} [Group G]

private theorem center_as_intersection (A : Subgroup G) :
    sCenter A = A ⊓ centralizer (A : Set G) := by
  ext x
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,fun y hy => congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx⟩,mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)),rfl⟩

private theorem middle_shape_embedding {E : Type*} [Group E]
    (A : Subgroup G) (f : G →* E) (hf : Function.Injective f) :
    (let Phi := frattiniIn (A.map f)
     let D := A.map f ⊓ centralizer (Phi : Set E)
     sCenter D = Phi ∧ Nat.card (⁅D,D⁆ : Subgroup E) = 8) ↔
    (let Phi := frattiniIn A
     let D := A ⊓ centralizer (Phi : Set G)
     sCenter D = Phi ∧ Nat.card (⁅D,D⁆ : Subgroup G) = 8) := by
  dsimp only
  rw [frattiniIn_map A f hf,map_inf_centralizer_of_injective f hf,
    centerIn_map _ f hf,←map_commutator,card_map_of_injective hf]
  exact and_congr (map_injective hf).eq_iff Iff.rfl

private theorem central_supplement_intersection (A C Z : Subgroup G)
    (hA : A ≤ C ⊔ Z) (hZA : Z ≤ A) (hZC : Z ≤ centralizer (C : Set G)) :
    A = Z ⊔ (C ⊓ A) := by
  apply le_antisymm ?_ (sup_le hZA inf_le_right)
  intro a ha
  have hh : a ∈ (Z : Set G) * (C : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right Z C
      (hZC.trans (Subgroup.centralizer_le_normalizer _)),sup_comm]
    exact hA ha
  obtain ⟨z,hz,c,hc,rfl⟩ := hh
  have hcA : c ∈ A := by
    simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem (hZA hz)) ha
  exact mul_mem_sup hz ⟨hc,hcA⟩

private theorem graph_middle_structure
    {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    {source : LocalSource L R} {geometry : Geometry R}
    (common : CommonFacts R source geometry)
    (earlier : DistanceEight.CoreFactors.Earlier R geometry)
    (hfixed : core R (alpha R) ⊓ centralizer
      (Ltilde R (alpha R) : Set (FreeAmalgam R)) = H R (alpha R)) :
    let Phi := frattiniIn (core R (alpha R))
    let D := core R (alpha R) ⊓ centralizer (Phi : Set (FreeAmalgam R))
    sCenter D = Phi ∧ Nat.card (⁅D,D⁆ : Subgroup (FreeAmalgam R)) = 8 := by
  let C := core R (alpha R)
  let Z₀ := Z R (alpha R)
  let Phi := frattiniIn C
  let D := C ⊓ centralizer (Phi : Set (FreeAmalgam R))
  obtain ⟨p⟩ := DistanceEight.CoreFactors.Early.sourcePath_nonempty source common earlier (alpha R) rfl
  let B := DistanceEight.CoreFactors.hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let A := DistanceEight.CoreFactors.hatV R (alpha R) (p.walk.getVert 6)
  have hD : D = C ⊓ B :=
    DistanceEight.CoreFactors.Center.core_frattini_centralizer_of_fixedFactor common earlier hfixed p
  have hPhi : Phi = C ⊓ A :=
    (DistanceEight.CoreFactors.Center.core_frattini_eq_moving_of_fixedFactor common earlier hfixed).trans
      (DistanceEight.CoreFactors.Center.core_inf_first_eq_moving_of_fixedFactor common earlier hfixed p).symm
  have hAc : B ⊓ centralizer (B : Set (FreeAmalgam R)) = A :=
    DistanceEight.CoreFactors.Center.second_center common earlier p
  have hZA : Z₀ ≤ A := by
    dsimp only [A]
    rw [(DistanceEight.CoreFactors.Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_right
  have hZB : Z₀ ≤ B := hZA.trans (hAc.symm.le.trans inf_le_left)
  have hZC : Z₀ ≤ centralizer (C : Set (FreeAmalgam R)) :=
    DistanceEight.CoreFactors.Higher.Quotients.FirstDirect.Z_centralizes_core common earlier
  have hBD : B = Z₀ ⊔ D := by
    rw [hD]
    exact central_supplement_intersection B C Z₀
      (DistanceEight.CoreFactors.Center.second_le_core_sup_Z common earlier p) hZB hZC
  have hDB : D ≤ B := hD ▸ inf_le_right
  have hZD : Z₀ ≤ centralizer (D : Set (FreeAmalgam R)) :=
    hZC.trans (centralizer_le inf_le_left)
  have hZcent : Z₀ ≤ centralizer (B : Set (FreeAmalgam R)) := hZA.trans (hAc.symm.le.trans inf_le_right)
  have hcenter : sCenter D = Phi := by
    rw [center_as_intersection,hPhi]
    apply le_antisymm
    · rintro x ⟨hx,hxc⟩
      refine ⟨hx.1,hAc.le ⟨hDB hx,?_⟩⟩
      rw [hBD,sup_eq_closure,centralizer_closure]
      intro y hy
      exact hy.elim ((le_centralizer_iff.mp hZD) hx y) (hxc y)
    · rintro x ⟨hxC,hxA⟩
      have hxB := (hAc.symm.le hxA).1
      exact ⟨hD.symm ▸ ⟨hxC,hxB⟩,(centralizer_le hDB) (hAc.symm.le hxA).2⟩
  have hderived : ⁅D,D⁆ = ⁅B,B⁆ := by
    have hh := commutator_eq_of_centralizing_sup hBD.symm hZD D.le_normalizer
    have hh' := commutator_eq_of_centralizing_sup hBD.symm hZcent (hDB.trans B.le_normalizer)
    exact hh.trans ((commutator_comm D B).trans hh')
  have h8 : Nat.card (⁅D,D⁆ : Subgroup (FreeAmalgam R)) = 8 := by
    rw [hderived,DistanceEight.CoreFactors.Center.second_derived_eq_U common earlier p]
    exact common.natural.card
  exact ⟨hcenter,h8⟩

variable [Finite G]

/-- The actual original D=C_Q(Phi) has center Phi and derived subgroup of order eight. -/
theorem binary_three_large_distance_original_middle_structure
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
    (hb : 4 < t.geometry.b t.reduction.radical) :
    let Q := LinearThree.commutatorCore c.L
    let Phi := frattiniIn Q
    let D := Q ⊓ centralizer (Phi : Set G)
    sCenter D = Phi ∧ Nat.card (⁅D,D⁆ : Subgroup G) = 8 := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := top_unique (fun x _ => hTS x.property)
    have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    rw [ht,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
  have hfixed := source_fixedFactor_eq_H_of_original_exchange
    d c.L eSL h hg b t common earlier g hgT hgS
  let J := c.L ⊔ d.S
  let K := core t.reduction.radical (alpha t.reduction.radical)
  let Q := LinearThree.commutatorCore c.L
  let Q₀ := BinaryMS.commutatorCore (c.L.subgroupOf J)
  have hQ : Q₀.map J.subtype = Q := sourceQ_map_subtype
    (show c.L ≤ J from le_sup_left) b.component
  let a : K ≃* Q := t.coreEquiv.trans
    ((Q₀.equivMapOfInjective J.subtype J.subtype_injective).trans (MulEquiv.subgroupCongr hQ))
  let f : K →* G := Q.subtype.comp a.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp a.injective
  have htop₀ : (⊤ : Subgroup K).map K.subtype = K := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  have htop : (⊤ : Subgroup K).map f = Q := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr a.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hgraph := graph_middle_structure common earlier hfixed
  have hbase := (middle_shape_embedding (⊤ : Subgroup K) K.subtype K.subtype_injective).mp
    (htop₀.symm ▸ hgraph)
  have hfinal := (middle_shape_embedding (⊤ : Subgroup K) f hf).mpr hbase
  rwa [htop] at hfinal

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
