module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointOriginalFourAction
public import Theory.GroupAction.ElementaryFiveMarkedParabolic

/-!
# The original I induces the full marked 2+3 parabolic

The image of the original core Q is the full radical at the original H.
The original component supplies a nontrivial perfect subgroup, while I
induces all automorphisms of H. Together these recognize the literal image
of I on U as the entire stabilizer of the same marked H.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- The actual original I has the full marked parabolic image on U. -/
theorem binary_three_source_original_marked_parabolic
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
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let H := intrinsicFour c.L
    let U := conjugateSpanBy H (centralizer ({z} : Set G))
    ∃ hIU : I ≤ normalizer (U : Set G),
      I ≤ normalizer (H : Set G) ∧
      ∀ f : MulAut U,
        f ∈ (U.normalizerMonoidHom.comp (inclusion hIU)).range ↔
          ∀ x : U, (f x : G) ∈ H ↔ (x : G) ∈ H := by
  let H := intrinsicFour c.L
  let U := conjugateSpanBy H (centralizer ({z} : Set G))
  let Q := LinearThree.commutatorCore c.L
  obtain ⟨hIU,hIH,hQU,_,hQcard,_,hQrad,_⟩ :=
    binary_three_source_fixed_span_marked_radical
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB hm
  obtain ⟨hIH',hHsurj⟩ := binary_three_source_original_four_action
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  let a : I →* MulAut U := U.normalizerMonoidHom.comp (inclusion hIU)
  let q : Q →* MulAut U := U.normalizerMonoidHom.comp (inclusion hQU)
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hQI : Q ≤ I := hQL.trans (component_le c)
  let l : c.L →* MulAut U := a.comp (inclusion (component_le c))
  let : Group.IsPerfect (c.L.subgroupOf (c.L ⊔ d.S)) := b.component.perfect
  let iL := subgroupOfEquivOfLe (show c.L ≤ c.L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect c.L := Group.IsPerfect.ofSurjective
    (f := iL.toMonoidHom) iL.surjective
  let : Group.IsPerfect l.range := Group.IsPerfect.range l
  have hqa : q.range ≤ a.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion hQI x,rfl⟩
  have hql : q.range ≤ l.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion hQL x,rfl⟩
  have hlne : l.range ≠ ⊥ := by
    intro hh
    have hz : q.range = ⊥ := le_antisymm (hh ▸ hql) bot_le
    have hcard : Nat.card q.range = 64 := hQcard
    rw [hz,card_bot] at hcard
    norm_num at hcard
  have hla : l.range ≤ a.range := by
    rintro _ ⟨x,rfl⟩
    exact ⟨inclusion (component_le c) x,rfl⟩
  have hHU : H ≤ U := le_conjugateSpanBy H _
  let k : H.subgroupOf U ≃* H := subgroupOfEquivOfLe hHU
  let : IsElementaryAbelian 2 U := (binary_three_source_fixed_span_kernel_index
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  have hUcard : Nat.card U = 32 := binary_three_source_four_fixed_span_order
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hHcard : Nat.card (H.subgroupOf U) = 4 :=
    (Nat.card_congr k.toEquiv).trans
      (intrinsicFour_properties_of_MS93 d c.L b t common earlier).2.1
  have hpres : ∀ f ∈ a.range, ∀ x : U,
      f x ∈ H.subgroupOf U ↔ x ∈ H.subgroupOf U := by
    rintro _ ⟨i,rfl⟩ x
    exact (mem_normalizer_iff.mp (hIH i.property) (x : G)).symm
  have hrad : ∀ f : MulAut U,
      (∀ x ∈ H.subgroupOf U, f x = x) →
      (∀ x : U, f x * x⁻¹ ∈ H.subgroupOf U) → f ∈ a.range := by
    intro f hfix hdisp
    exact hqa ((hQrad f).mpr ⟨hfix,hdisp⟩)
  have hres : ∀ f : MulAut (H.subgroupOf U),
      ∃ g ∈ a.range, ∀ x : H.subgroupOf U, g x = (f x : U) := by
    intro f
    let fH : MulAut H := (k.symm.trans f).trans k
    obtain ⟨i,hi⟩ := hHsurj fH
    refine ⟨a i,⟨i,rfl⟩,?_⟩
    intro x
    apply Subtype.ext
    exact congrArg (fun g : MulAut H => (g (k x) : G)) hi
  exact ⟨hIU,hIH,MulAut.elementary_five_marked_parabolic hUcard
    (H.subgroupOf U) hHcard a.range l.range hlne hla hpres hrad hres⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
