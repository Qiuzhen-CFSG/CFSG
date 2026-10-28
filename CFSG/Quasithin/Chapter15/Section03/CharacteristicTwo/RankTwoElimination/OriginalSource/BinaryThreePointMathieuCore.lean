module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSporadicPlacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralEight
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreJoin
public import Theory.SpecificGroups.Alternating.SevenThreeSection
public import Theory.ElementaryAbelian.Injective

/-!
# The original core at an M23 point

The heptad action maps the actual local PSL3(2) section to an order-168
subgroup of A7 with trivial two-core. Hence its entire two-core embeds in
the elementary translation kernel of order sixteen. The original Q image
is therefore elementary of order at most sixteen. Since Q′=Phi(Q), the
whole original Frattini layer lies in O2(C_G(z)), and the original natural
eight has its full C_G(z)-span in the center of that same point kernel.

These are source kernel and action constraints; an M23 exclusion is not
claimed. The literal full Sylow, quotient and containing component remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource LinearThree.CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry

private theorem elementary_core_of_equiv
    {A D : Type*} [Group A] [Group D] (a : A ≃* D)
    (hD : IsElementaryAbelian 2 (pCore 2 D)) (hc : Nat.card (pCore 2 D) ≤ 16) :
    IsElementaryAbelian 2 (pCore 2 A) ∧ Nat.card (pCore 2 A) ≤ 16 := by
  let e := (a.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  let := hD
  exact ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).le.trans hc⟩

private theorem heptad_binary_three_core (A : Subgroup heptadStabilizer)
    (eA : (A ⧸ pCore 2 A) ≃* PSL(3,ZMod 2)) :
    IsElementaryAbelian 2 (pCore 2 A) ∧ Nat.card (pCore 2 A) ≤ 16 := by
  let f := heptadAlternatingAction
  let D := A.map f
  have hk : IsPGroup 2 f.ker := by
    rw [heptadAlternatingAction_ker]
    exact heptadKernel_isTwoGroup
  have hkA : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eD := ((f.subgroupMap A).pCoreQuotientEquiv
    (f.subgroupMap_surjective A) hkA).symm.trans eA
  have hD : pCore 2 D = ⊥ :=
    alternatingGroup.SevenThreeSection.twoCore_eq_bot D (eD.trans Matrix.PSL3Two.equiv.symm)
  have hmap : (A.pCoreIn 2).map f = ⊥ := by
    rw [map_pCoreIn_of_ker_isPGroup f hk]
    change (pCore 2 D).map D.subtype = ⊥
    rw [hD,Subgroup.map_bot]
  have hle : A.pCoreIn 2 ≤ heptadKernel := by
    have hh := (Subgroup.map_eq_bot_iff (A.pCoreIn 2)).mp hmap
    simpa only [f,heptadAlternatingAction_ker] using hh
  let j : pCore 2 A →* heptadKernel := {
    toFun x := ⟨((x:A):heptadStabilizer),hle (mem_map_of_mem A.subtype x.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : heptadKernel => (z : heptadStabilizer)) he))
  let : IsElementaryAbelian 2 heptadKernel := {
    toIsMulCommutative := ⟨⟨heptadKernel_mul_comm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr heptadKernel_sq }
  exact ⟨IsElementaryAbelian.of_injective j hj,
    (Nat.card_le_card_of_injective j hj).trans_eq heptadKernel_card⟩

private theorem fixed_heptad_equiv :
    Nonempty ((MulAction.stabilizer M23 FourNormalizers.fixedSet) ≃* heptadStabilizer) := by
  obtain ⟨g,hg⟩ := exists_smul_omega_eq FourNormalizers.fixedSet_mem
  rw [←hg,MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact ⟨((MulAut.conj g).subgroupMap heptadStabilizer).symm⟩

/-- The actual Sylow-normalized binary-three local subgroup of M23 has an
entire two-core elementary of order at most sixteen. -/
theorem binary_three_m23_local_core
    (S : Sylow 2 M23) (B : Subgroup M23)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSB : (S : Subgroup M23) ≤ normalizer B)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    IsElementaryAbelian 2 (pCore 2 B) ∧ Nat.card (pCore 2 B) ≤ 16 := by
  obtain ⟨g,_,hg⟩ := binary_three_mathieuTwentyThree_heptad_placement S B hB hSB eB
  let C := B.map (MulAut.conj g).toMonoidHom
  let H := MulAction.stabilizer M23 FourNormalizers.fixedSet
  have hCH : C ≤ H := (map_mono B.le_normalizer).trans hg
  obtain ⟨a⟩ := fixed_heptad_equiv
  let A := (C.subgroupOf H).map a.toMonoidHom
  let e : B ≃* A := ((MulAut.conj g).subgroupMap B).trans
    ((subgroupOfEquivOfLe hCH).symm.trans (a.subgroupMap (C.subgroupOf H)))
  let eq := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans eB
  obtain ⟨hA,hc⟩ := heptad_binary_three_core A eq
  exact elementary_core_of_equiv e hA hc

private theorem containing_m23_core
    {X : Type*} [Group X] [Finite X] (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hK : K.IsCComponent)
    (hBK : B ≤ K) (hTB : (T : Subgroup X) ≤ normalizer B)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) (eK : K ≃* M23) :
    IsElementaryAbelian 2 (pCore 2 B) ∧ Nat.card (pCore 2 B) ≤ 16 := by
  obtain ⟨S,_,hl,hn⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_normalizing
    T hB hK.subnormal hBK hTB
  let A := B.subgroupOf K
  let D := A.map eK.toMonoidHom
  let a : B ≃* D := (subgroupOfEquivOfLe hBK).symm.trans (eK.subgroupMap A)
  let eD := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans eB
  let : Group.IsSolvable eK.toMonoidHom.ker := by
    rw [eK.toMonoidHom.ker_eq_bot eK.injective]
    infer_instance
  have hlD := Chapter1.Section02.localCComponents_map_of_solvable_ker hl eK.toMonoidHom
  have hnD := (map_mono (f := eK.toMonoidHom) hn).trans (A.le_normalizer_map eK.toMonoidHom)
  obtain ⟨hD,hc⟩ := binary_three_m23_local_core
    (S.mapSurjective (f := eK.toMonoidHom) eK.surjective) D hlD hnD eD
  exact elementary_core_of_equiv a hD hc

variable {G : Type*} [Group G] [Finite G]

/-- The full original M23 source puts Phi(Q) in the actual point kernel,
and the full conjugate span of the natural eight in its center. -/
theorem binary_three_source_m23_core_kernel
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
    (eK : K ≃* M23) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 C)
    let Q := LinearThree.commutatorCore c.L
    let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
    IsElementaryAbelian 2 ((Q.subgroupOf C).map q) ∧
      Nat.card ((Q.subgroupOf C).map q) ≤ 16 ∧
      frattiniIn Q ≤ N ∧ W ≤ (center N).map N.subtype ∧
      IsElementaryAbelian 2 W := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := LinearThree.commutatorCore c.L
  let B := (c.L.subgroupOf C).map q
  let E := (Q.subgroupOf C).map q
  let T := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hQC : Q ≤ C := ((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)).trans hLC
  obtain ⟨hB,⟨eB⟩⟩ := point_centralizer_quotient_local d c.L e b z hLS P hP
  have hSL : d.S ≤ normalizer c.L := le_sup_right.trans
    ((normal_subgroupOf_iff_le_normalizer (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp
      b.component_normal)
  have hPB : (P : Subgroup C) ≤ normalizer (c.L.subgroupOf C) := by
    rw [←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact hSL (hP ▸ mem_map_of_mem C.subtype hx)
  have hTB : (T : Subgroup (C ⧸ pCore 2 C)) ≤ normalizer B :=
    (map_mono (f := q) hPB).trans ((c.L.subgroupOf C).le_normalizer_map q)
  obtain ⟨hBe,hBc⟩ := containing_m23_core T hB hK hBK hTB eB eK
  let : IsElementaryAbelian 2 (pCore 2 B) := hBe
  let : IsElementaryAbelian 2 (B.pCoreIn 2) := IsElementaryAbelian.map B.subtype
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hE : E = LinearThree.commutatorCore B :=
    binary_three_original_core_image_of_le c.L C hLC q hk
  have hEB : E ≤ B.pCoreIn 2 := hE.le.trans (LinearThree.commutatorCore_le B)
  let hEe : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hEB
  have hEc : Nat.card E ≤ 16 := (card_le_of_le hEB).trans
    ((card_map_of_injective B.subtype_injective).le.trans hBc)
  have hkill : (⁅Q.subgroupOf C,Q.subgroupOf C⁆).map q = ⊥ := by
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hle : ⁅Q.subgroupOf C,Q.subgroupOf C⁆ ≤ pCore 2 C := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hkill
  have hQQN : ⁅Q,Q⁆ ≤ N := by
    have hh := map_mono (f := C.subtype) hle
    change ⁅Q,Q⁆ ≤ (pCore 2 C).map C.subtype
    simpa only [map_commutator,map_subgroupOf_eq_of_le hQC] using hh
  have hroot : _root_.commutator Q = frattini Q :=
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.2.1
  have hPhiN : frattiniIn Q ≤ N := by
    change (frattini Q).map Q.subtype ≤ N
    rw [←hroot]
    simpa only [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hQQN
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  obtain ⟨hVe,_,hVc⟩ := binary_three_source_point_central_eight
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
  have hZPhi : coreCenter c.L ≤ frattiniIn Q := map_mono
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.1
  have hLZ : c.L ≤ normalizer (coreCenter c.L) :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hVN : V ≤ N := (le_normalizer_iff_commutator_le_left.mp hLZ).trans (hZPhi.trans hPhiN)
  have hVcenter : V ≤ (center N).map N.subtype := by
    intro x hx
    refine ⟨⟨x,hVN hx⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hVc hx y y.property)
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hWcenter : W ≤ (center N).map N.subtype := conjugateSpanBy_le hVcenter
    (hCN.trans (normalizer_le_normalizer_characteristic_image N (center N)))
  let : IsElementaryAbelian 2 V := hVe
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp (by
    intro x hx y hy
    obtain ⟨x,hxc,rfl⟩ := hWcenter hx
    have hyN : y ∈ N := map_subtype_le _ (hWcenter hy)
    exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨y,hyN⟩))
  exact ⟨hEe,hEc,hPhiN,hWcenter,conjugateSpanBy_elementary_of_commutative V C⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
