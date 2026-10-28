module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointBinaryFaithfulSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralizerAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanFrattiniPairing

/-!
# The full fixed-span centralizer fixes the original natural span

Faithfulness of the original component on U modulo its point line forces
the image of C_G(U) to centralize that component. The source centralizer
action then fixes its whole natural span W. In particular C_G(U) fixes
Phi(Q)=UV, retaining the full centralizer kernel throughout.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The full ambient centralizer of U fixes both the natural span and
the original Frattini subgroup pointwise. -/
theorem binary_three_source_fixed_span_centralizer
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
    let C := centralizer ({z} : Set G)
    let U := conjugateSpanBy (intrinsicFour c.L) C
    let W := conjugateSpanBy ⁅coreCenter c.L,c.L⁆ C
    centralizer (U : Set G) ≤ centralizer (W : Set G) ∧
      centralizer (U : Set G) ≤ centralizer (frattiniIn (LinearThree.commutatorCore c.L) : Set G) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let Z := zpowers z
  let U := conjugateSpanBy (intrinsicFour c.L) C
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  let CU := centralizer (U : Set G)
  let hCU := le_normalizer_conjugateSpanBy (intrinsicFour c.L) C
  let α := U.normalizerMonoidHom.comp (inclusion hCU)
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  obtain ⟨_,_,_,_,_,_,hZ,hel,ρ,hρ,hfaith,_,_⟩ :=
    binary_three_source_binary_faithful_span
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
        K hK hKn hLK eB hrX hrB (Or.inl rfl) hm
  let := hZ
  have hdisj : Disjoint ρ.ker (K.map q) := by
    apply disjoint_def.mpr
    intro x hx hxK
    have he : (⟨x,hxK⟩ : K.map q) = 1 :=
      hfaith (hx.trans (map_one ρ).symm)
    exact congrArg Subtype.val he
  have hker : ρ.ker ≤ centralizer (K.map q : Set (C ⧸ pCore 2 C)) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdisj)
  have hCUC : CU ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx z (le_conjugateSpanBy _ C hzH)).symm
  have hpre : CU ≤ ((centralizer (K.map q : Set (C ⧸ pCore 2 C))).comap q).map C.subtype := by
    intro x hx
    let xC : C := ⟨x,hCUC hx⟩
    refine ⟨xC,hker ?_,rfl⟩
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) v
    have hfix : α xC u = u := by
      apply Subtype.ext
      change x*(u:G)*x⁻¹ = (u:G)
      rw [←hx u u.property,mul_inv_cancel_right]
    change ρ (q xC) (QuotientGroup.mk' (Z.subgroupOf U) u) = _
    rw [hρ xC u (α xC u) rfl,hfix]
    rfl
  have hW : CU ≤ centralizer (W : Set G) := hpre.trans
    (binary_three_source_component_centralizer_fixes_span
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP
        (K.map q) (map_mono (f := q) hLK))
  have hPhi := (binary_three_source_fixed_span_frattini_pairing
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1
  refine ⟨hW,?_⟩
  rw [hPhi]
  exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp (le_refl CU))
    (le_centralizer_iff.mp (hW.trans (centralizer_le (le_conjugateSpanBy V C)))))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
