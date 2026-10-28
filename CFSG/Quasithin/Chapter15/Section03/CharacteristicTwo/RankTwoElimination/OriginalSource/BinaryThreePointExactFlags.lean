module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointContainingJoinQuotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointMiddleFlag
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore.ExactQuotientFlags

/-!
# Actual endpoint and adjacent binary point-carrier flags

The original restricted Sylow join retains its own PSL3(2) quotient. The
exact finite quotient-order classification gives endpoint flags for PSL4(2)
and three candidate flags for PSL5(2). The proved original-source middle
exclusion leaves the two adjacent flags. Each conclusion retains the same
restricted Sylow, a concrete model equivalence, and its full-flag basis.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions

private theorem binary_carrier_equiv {X : Type*} [Group X] {n : ℕ} (hn : 0<n)
    (hm : ClassicalGroup.IsPSL X n 2) : Nonempty (X ≃* LinearGroup n) := by
  obtain ⟨F,_,_,hF,⟨a₀⟩⟩ := hm
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact ⟨(a₀.trans (Atlas.fieldEquivPSL n f)).trans (projectiveEquivLinear hn)⟩

private theorem mapped_quotient_card {X : Type*} [Group X] {n : ℕ}
    (a : X ≃* LinearGroup n) (J : Subgroup X)
    (e : (J ⧸ pCore 2 J) ≃* PSL(3,ZMod 2)) :
    Nat.card ((J.map a.toMonoidHom) ⧸ pCore 2 (J.map a.toMonoidHom))=168 := by
  let j := J.equivMapOfInjective a.toMonoidHom a.injective
  rw [←Nat.card_congr (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).toEquiv,
    Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv,Matrix.PSL3Two.card_SL]

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual PSL4(2) carrier has an endpoint flag for the original
restricted Sylow join, with a concrete model and the same full Sylow. -/
theorem binary_three_point_four_endpoint_flags
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
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
    ∃ T : Sylow 2 K, (T : Subgroup K)=(S : Subgroup (C ⧸ pCore 2 C)).subgroupOf K ∧
      ∃ (a : K ≃* LinearGroup 4) (v : Basis 3),
        (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup (LinearGroup 4))=
          cutStabilizer v Set.univ ∧
        ((B.subgroupOf K).map a.toMonoidHom ⊔
            (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
          cutStabilizer v ({0} : Set (Fin 3)) ∨
        (B.subgroupOf K).map a.toMonoidHom ⊔
            (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
          cutStabilizer v ({2} : Set (Fin 3))) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (L.subgroupOf C).map q
  obtain ⟨T,hT,⟨eJ⟩⟩ := binary_three_point_containing_join_core_quotient d L b z hLS P hP K hBK
  obtain ⟨a⟩ := binary_carrier_equiv (by decide : 0<4) hm
  let J := B.subgroupOf K ⊔ (T : Subgroup K)
  let U := T.mapSurjective (f := a.toMonoidHom) a.surjective
  have hmapU : (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
      (T : Subgroup K).map a.toMonoidHom := rfl
  have hUJ : (U : Subgroup _) ≤ J.map a.toMonoidHom := map_mono le_sup_right
  obtain ⟨v,hv,hflags⟩ := BinaryLinear.SevenFlagCore.four_sylow_overgroup_of_quotient_card_168
    U (J.map a.toMonoidHom) hUJ (mapped_quotient_card a J eJ)
  refine ⟨T,hT,a,v,hv,?_⟩
  simpa only [J,B,q,C,Subgroup.map_sup,hmapU] using hflags

/-- The full original source removes the middle flag, leaving an actual
adjacent1|1|3 or3|1|1 join in a basis retaining the restricted full Sylow. -/
theorem binary_three_source_five_adjacent_flags
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
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
    ∃ T : Sylow 2 K, (T : Subgroup K)=(S : Subgroup (C ⧸ pCore 2 C)).subgroupOf K ∧
      ∃ (a : K ≃* LinearGroup 5) (v : Basis 4),
        (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup (LinearGroup 5))=
          cutStabilizer v Set.univ ∧
        ((B.subgroupOf K).map a.toMonoidHom ⊔
            (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
          cutStabilizer v ({0,1} : Set (Fin 4)) ∨
        (B.subgroupOf K).map a.toMonoidHom ⊔
            (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
          cutStabilizer v ({2,3} : Set (Fin 4))) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let B := (c.L.subgroupOf C).map q
  obtain ⟨T,hT,⟨eJ⟩⟩ := binary_three_point_containing_join_core_quotient d c.L b z hLS P hP K hBK
  obtain ⟨T₁,hT₁,hnot⟩ := binary_three_source_five_join_not_middle
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  have hTT : T₁=T := Sylow.ext (hT₁.trans hT.symm)
  subst T₁
  obtain ⟨a⟩ := binary_carrier_equiv (by decide : 0<5) hm
  let J := B.subgroupOf K ⊔ (T : Subgroup K)
  let U := T.mapSurjective (f := a.toMonoidHom) a.surjective
  have hmapU : (T.mapSurjective (f := a.toMonoidHom) a.surjective : Subgroup _) =
      (T : Subgroup K).map a.toMonoidHom := rfl
  have hUJ : (U : Subgroup _) ≤ J.map a.toMonoidHom := map_mono le_sup_right
  obtain ⟨v,hv,hflags⟩ := BinaryLinear.SevenFlagCore.five_sylow_overgroup_of_quotient_card_168
    U (J.map a.toMonoidHom) hUJ (mapped_quotient_card a J eJ)
  refine ⟨T,hT,a,v,hv,?_⟩
  rcases hflags with he | he | he
  · exact Or.inl (by simpa only [J,B,q,C,Subgroup.map_sup,hmapU] using he)
  · exact (hnot a v (by simpa only [J,B,q,C,Subgroup.map_sup,hmapU] using he)).elim
  · exact Or.inr (by simpa only [J,B,q,C,Subgroup.map_sup,hmapU] using he)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
