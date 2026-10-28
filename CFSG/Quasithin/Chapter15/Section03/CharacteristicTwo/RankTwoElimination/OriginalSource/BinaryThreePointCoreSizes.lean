module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointExactFlags
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.ResidualRectangles

/-!
# Exact original core image and point-kernel intersection orders

The literal residual of the surviving endpoint or adjacent flag has moving
core equal to its full rectangle. Transport through the original point
quotient gives |q(Q)|=8 or64. The original core has order2^20, hence its
intersection with the same point kernel has order2^17 or2^14. No orientation
relative to the original PSL3 marking is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

private theorem moving_card_transport {X : Type*} [Group X] [Finite X] {m : ℕ}
    (a : X ≃* LinearGroup (m+1)) (D : Subgroup X) (T : Sylow 2 X)
    (hres : (pResidual 2 (D ⊔ (T : Subgroup X) : Subgroup X)).map (D ⊔ (T : Subgroup X)).subtype = D)
    (v : Basis m) (cuts : Set (Fin m))
    (hflag : D.map a.toMonoidHom ⊔
      (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) = cutStabilizer v cuts)
    {k : ℕ}
    (hcard : let R := (pResidual 2 (cutStabilizer v cuts)).map (cutStabilizer v cuts).subtype
      Nat.card (⁅R.pCoreIn 2,R⁆ : Subgroup (LinearGroup (m+1)))=k) :
    Nat.card (LinearThree.commutatorCore D)=k := by
  let J := D ⊔ (T : Subgroup X)
  have hJ : J.map a.toMonoidHom=cutStabilizer v cuts := by
    rw [Subgroup.map_sup]
    exact hflag
  have hr : (pResidual 2 (cutStabilizer v cuts)).map (cutStabilizer v cuts).subtype = D.map a.toMonoidHom := by
    have hh := congrArg (Subgroup.map a.toMonoidHom) hres
    rw [map_embedded_pResidual,hJ] at hh
    exact hh
  have hh := hcard
  dsimp only at hh
  rw [hr,←map_pCoreIn_of_injective 2 D a.toMonoidHom a.injective,←map_commutator,
    card_map_of_injective a.injective] at hh
  exact hh

private theorem image_core_eq {A : Type*} [Group A] [Finite A] (L C : Subgroup A)
    (hLC : L ≤ C) :
    ((LinearThree.commutatorCore L).subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) =
      LinearThree.commutatorCore ((L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))) := by
  let q := QuotientGroup.mk' (pCore 2 C)
  have hQC : LinearThree.commutatorCore L ≤ C :=
    ((LinearThree.commutatorCore_le L).trans (L.pCoreIn_le 2)).trans hLC
  have he : LinearThree.commutatorCore (L.subgroupOf C)=(LinearThree.commutatorCore L).subgroupOf C := by
    apply map_injective C.subtype_injective
    simp only [LinearThree.commutatorCore,map_commutator,
      map_pCoreIn_of_injective 2 _ _ C.subtype_injective,map_subgroupOf_eq_of_le hLC,
      map_subgroupOf_eq_of_le hQC]
  rw [←he]
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  change (LinearThree.commutatorCore (L.subgroupOf C)).map q=
    LinearThree.commutatorCore ((L.subgroupOf C).map q)
  simp only [LinearThree.commutatorCore,map_commutator,map_pCoreIn_of_ker_isPGroup q hk]

private theorem image_card_mul_intersection {A : Type*} [Group A] [Finite A]
    (Q C : Subgroup A) (hQC : Q ≤ C) :
    Nat.card (((Q.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)))) *
      Nat.card (Q ⊓ C.pCoreIn 2 : Subgroup A)=Nat.card Q := by
  let V := Q.subgroupOf C
  let q := QuotientGroup.mk' (pCore 2 C)
  have hh := relIndex_mul_relIndex (⊥ : Subgroup C) (V ⊓ pCore 2 C) V bot_le inf_le_left
  have hi : (V ⊓ pCore 2 C).relIndex V=Nat.card (V.map q) := by
    rw [inf_comm,inf_relIndex_right]
    simpa only [q,QuotientGroup.ker_mk'] using (relIndex_ker V q)
  rw [relIndex_bot_left,relIndex_bot_left,hi] at hh
  have hcardV : Nat.card V=Nat.card Q := Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv
  have hcardI : Nat.card (V ⊓ pCore 2 C : Subgroup C)=Nat.card (Q ⊓ C.pCoreIn 2 : Subgroup A) := by
    rw [←card_map_of_injective (f := C.subtype) C.subtype_injective,
      Subgroup.map_inf _ _ _ C.subtype_injective,map_subgroupOf_eq_of_le hQC]
    rfl
  rw [hcardV,hcardI] at hh
  simpa only [Nat.mul_comm] using hh

universe u
variable {G : Type u} [Group G] [Finite G]

/-- In the actual binary-four carrier the literal original Q image has
order8, with the original point quotient unchanged. -/
theorem binary_three_point_four_core_image_card
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    Nat.card (((LinearThree.commutatorCore L).subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)))=8 := by
  let C := centralizer ({z} : Set G)
  let B := (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))
  let D := B.subgroupOf K
  obtain ⟨T,hT,a,v,hv,hflag⟩ := binary_three_point_four_endpoint_flags d L b z hLS P hP K hBK hm
  obtain ⟨_,T₁,hT₁,hres⟩ := binary_three_point_join_residual d L b z hLS P hP K hBK
  have hTT : T₁=T := Sylow.ext (hT₁.trans hT.symm)
  subst T₁
  have hcD : Nat.card (LinearThree.commutatorCore D)=8 := by
    rcases hflag with hflag | hflag
    · exact moving_card_transport a D T hres v {0} hflag
        (BinaryLinear.SevenFlagCore.endpoint_residual_moving_rectangle v false).2
    · exact moving_card_transport a D T hres v {2} hflag
        (BinaryLinear.SevenFlagCore.endpoint_residual_moving_rectangle v true).2
  have hDmap : D.map K.subtype=B := map_subgroupOf_eq_of_le hBK
  have hmap : (LinearThree.commutatorCore D).map K.subtype=LinearThree.commutatorCore B := by
    simp only [LinearThree.commutatorCore,map_commutator,
      map_pCoreIn_of_injective 2 D _ K.subtype_injective,hDmap]
  have hcB : Nat.card (LinearThree.commutatorCore B)=8 := by
    rw [←hmap,card_map_of_injective K.subtype_injective]
    exact hcD
  change Nat.card (((LinearThree.commutatorCore L).subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)))=8
  rw [image_core_eq L C (le_sup_left.trans hLS)]
  exact hcB

/-- In the actual binary-five carrier the literal original Q image has
order64, with the actual point quotient and full Sylow retained. -/
theorem binary_three_source_five_core_image_card
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
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 5 2) :
    let C := centralizer ({z} : Set G)
    Nat.card (((LinearThree.commutatorCore c.L).subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)))=64 := by
  let C := centralizer ({z} : Set G)
  let B := (c.L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))
  let D := B.subgroupOf K
  obtain ⟨T,hT,a,v,hv,hflag⟩ := binary_three_source_five_adjacent_flags
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  obtain ⟨_,T₁,hT₁,hres⟩ := binary_three_point_join_residual d c.L b z hLS P hP K hBK
  have hTT : T₁=T := Sylow.ext (hT₁.trans hT.symm)
  subst T₁
  have hcD : Nat.card (LinearThree.commutatorCore D)=64 := by
    rcases hflag with hflag | hflag
    · exact moving_card_transport a D T hres v {0,1} hflag
        (BinaryLinear.SevenFlagCore.adjacent_residual_moving_rectangle v false).2
    · exact moving_card_transport a D T hres v {2,3} hflag
        (BinaryLinear.SevenFlagCore.adjacent_residual_moving_rectangle v true).2
  have hDmap : D.map K.subtype=B := map_subgroupOf_eq_of_le hBK
  have hmap : (LinearThree.commutatorCore D).map K.subtype=LinearThree.commutatorCore B := by
    simp only [LinearThree.commutatorCore,map_commutator,
      map_pCoreIn_of_injective 2 D _ K.subtype_injective,hDmap]
  have hcB : Nat.card (LinearThree.commutatorCore B)=64 := by
    rw [←hmap,card_map_of_injective K.subtype_injective]
    exact hcD
  change Nat.card (((LinearThree.commutatorCore c.L).subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)))=64
  rw [image_core_eq c.L C (le_sup_left.trans hLS)]
  exact hcB

/-- Exact image and hidden point-kernel intersection orders for the
original Q. The kernel is the literal O₂(C_G(z)); Q need not be normal in it. -/
theorem binary_three_source_binary_core_sizes
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
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n=4 ∨ n=5) (hm : ClassicalGroup.IsPSL K n 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let Q := LinearThree.commutatorCore c.L
    Nat.card ((Q.subgroupOf C).map q)=2^(3*(n-3)) ∧
      Nat.card (Q ⊓ C.pCoreIn 2 : Subgroup G)=2^(20-3*(n-3)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := LinearThree.commutatorCore c.L
  have hQcard : Nat.card Q=1048576 :=
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.1
  have hQC : Q ≤ C := ((LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)).trans
    (le_sup_left.trans hLS)
  have hmul := image_card_mul_intersection Q C hQC
  rw [hQcard] at hmul
  rcases hn with rfl | rfl
  · have him : Nat.card ((Q.subgroupOf C).map q)=8 :=
      binary_three_point_four_core_image_card d c.L b z hLS P hP K hBK hm
    rw [him] at hmul
    refine ⟨him,?_⟩
    change Nat.card (Q ⊓ C.pCoreIn 2 : Subgroup G)=_
    norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.reducePow]
    omega
  · have him : Nat.card ((Q.subgroupOf C).map q)=64 :=
      binary_three_source_five_core_image_card
        hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
    rw [him] at hmul
    refine ⟨him,?_⟩
    change Nat.card (Q ⊓ C.pCoreIn 2 : Subgroup G)=_
    norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.reducePow]
    omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
