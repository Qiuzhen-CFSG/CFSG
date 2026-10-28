module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCentralEight
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer

/-!
# The containing-component centralizer fixes the actual central span

The full preimage of C_(C/N)(K) normalizes the original perfect L. It
therefore preserves the original natural eight, and commutes with its
L action because N fixes that eight. Its invertible commutant is trivial
over F2. Normality then gives pointwise fixation of the whole C-span.
The kernel is retained; no faithfulness of C/N on K is asserted.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open LinearThree.Extension.SourceCases
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem natural_aut_trivial
    (f : MulAut (Multiplicative (Fin 3 → ZMod 2)))
    (hf : ∀ (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2),
      (f (Multiplicative.ofAdd (g.val.mulVec v))).toAdd =
        g.val.mulVec (f (Multiplicative.ofAdd v)).toAdd) :
    f = 1 := by
  let a : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) := (AddEquiv.toMultiplicative.symm f).toAddMonoidHom
  obtain ⟨c,hc⟩ := Representation.SL3DoubledNaturalOffenders.natural_centralizer_scalar a hf
  have hne : c ≠ 0 := by
    intro hz
    have hh : a (fun _ => 1) = a 0 := by rw [hc,hc,hz]; simp
    have hh' := (AddEquiv.toMultiplicative.symm f).injective hh
    have he := congrArg (fun v : Fin 3 → ZMod 2 => v 0) hh'
    exact one_ne_zero he
  have hc1 : c = 1 := ((show ∀ c : ZMod 2, c=0 ∨ c=1 from by decide) c).resolve_left hne
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  change a v.toAdd = v.toAdd
  rw [hc,hc1,one_smul]

private theorem modeled_natural_aut_trivial
    {G : Type*} [Group G] (L V : Subgroup G)
    (a : L →* SpecialLinearGroup (Fin 3) (ZMod 2)) (ha : Function.Surjective a)
    (h : HasSectionModel L V ⊥ a (Representation.specialLinearNatural (k := ZMod 2) 3))
    (f : MulAut V)
    (hf : ∀ (l : L) (v w : V), (w : G) = l * (v : G) * (l : G)⁻¹ →
      (f w : G) = l * (f v : G) * (l : G)⁻¹) : f = 1 := by
  obtain ⟨_,hLV,_,hn,e,he⟩ := h
  let := hn
  have hker : (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf V)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk',bot_subgroupOf]
  let E : V ≃* Multiplicative (Fin 3 → ZMod 2) :=
    (MulEquiv.ofBijective (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf V))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp hker,QuotientGroup.mk'_surjective _⟩).trans e
  let c (l : L) : MulAut V := V.normalizerMonoidHom ⟨l,hLV l.property⟩
  have hc (l : L) (v : V) : (c l v : G) = l * (v : G) * (l : G)⁻¹ := rfl
  have hE (l : L) (v : V) : E (c l v) =
      Multiplicative.ofAdd ((a l).val.mulVec (E v).toAdd) := by
    apply Multiplicative.toAdd.injective
    exact he l v (c l v) rfl
  have hfc (l : L) (v : V) : f (c l v) = c l (f v) :=
    Subtype.ext (hf l v (c l v) rfl)
  have hzero : MulAut.congr E f = 1 := by
    apply natural_aut_trivial
    intro s v
    obtain ⟨l,rfl⟩ := ha s
    have hh := hE l (E.symm (Multiplicative.ofAdd v))
    rw [E.apply_symm_apply] at hh
    change E ((c l) (E.symm (Multiplicative.ofAdd v))) = Multiplicative.ofAdd ((a l).val.mulVec v) at hh
    change (E (f (E.symm (Multiplicative.ofAdd ((a l).val.mulVec v))))).toAdd = _
    rw [←hh,E.symm_apply_apply,hfc]
    exact congrArg Multiplicative.toAdd (hE l (f (E.symm (Multiplicative.ofAdd v))))
  exact (MulAut.congr E).injective (hzero.trans (map_one _).symm)

private theorem original_natural_section
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical) :
    ∃ a : L →* SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective a ∧
      HasSectionModel L (⁅coreCenter L,L⁆) ⊥ a
        (Representation.specialLinearNatural (k := ZMod 2) 3) := by
  let J := L ⊔ d.S
  let Q₀ := BinaryMS.commutatorCore (L.subgroupOf J)
  have hmap : Q₀.map J.subtype = LinearThree.commutatorCore L :=
    sourceQ_map_subtype (show L ≤ J from le_sup_left) b.component
  have hms : msQ (L.subgroupOf J) (d.S.subgroupOf J) = Q₀ := by
    have hp : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
    rw [msQ,b.sup_eq_top,hp]
  have hs := (t.center_source_sections common hb).2.2.2
  change HasSectionModel (L.subgroupOf J)
    (⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (msQ (L.subgroupOf J) (d.S.subgroupOf J)),L.subgroupOf J⁆) ⊥ _ _ at hs
  rw [hms] at hs
  let V₀ := ⁅CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q₀,L.subgroupOf J⁆
  let V := ⁅coreCenter L,L⁆
  have hm : V₀.map J.subtype = V := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)]
    change ⁅((center Q₀).map Q₀.subtype).map J.subtype,L⁆ = _
    rw [map_subgroup_center_eq _ J.subtype_injective,hmap]
    rfl
  have hVJ : V ≤ J := hm ▸ map_subtype_le _
  have hVsub : V₀ = V.subgroupOf J := by
    rw [←hm]
    exact (comap_map_eq_self_of_injective J.subtype_injective V₀).symm
  let i := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let π := linearThreeActor (b.quotientEquiv.trans common.natural.marking)
  let a := π.comp i.symm.toMonoidHom
  have ha : Function.Surjective a :=
    (b.quotientEquiv.trans common.natural.marking).surjective.comp
      ((QuotientGroup.mk'_surjective _).comp i.symm.surjective)
  have hi : π = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg π (i.symm_apply_apply x).symm
  change HasSectionModel (L.subgroupOf J) V₀ ⊥ π _ at hs
  rw [hVsub,hi] at hs
  exact ⟨a,ha,HasSectionModel.of_subgroupOf (J := J) le_sup_left hVJ bot_le a _
    (by simpa only [bot_subgroupOf] using hs)⟩

/-- The actual kernel of conjugation on the containing simple component
fixes the entire C-span of the original natural eight. -/
theorem binary_three_source_component_centralizer_fixes_span
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
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    : let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let V := ⁅coreCenter c.L,c.L⁆
      let W := conjugateSpanBy V C
      ((centralizer (K : Set (C ⧸ pCore 2 C))).comap q).map C.subtype ≤
        centralizer (W : Set G) := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let J := c.L ⊔ d.S
  let LC := c.L.subgroupOf C
  let V := ⁅coreCenter c.L,c.L⁆
  let T := (centralizer (K : Set (C ⧸ pCore 2 C))).comap q
  let A := T.map C.subtype
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hJL : J ≤ normalizer c.L :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hqn : q.ker ≤ normalizer LC := by
    rw [QuotientGroup.ker_mk',←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact (hNS.trans (le_sup_right.trans hJL)) (mem_map_of_mem C.subtype hx)
  have hq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let : Group.IsPerfect (c.L.subgroupOf J) := b.component.perfect
  let ec : (c.L.subgroupOf J) ≃* LC :=
    (subgroupOfEquivOfLe (show c.L ≤ J from le_sup_left)).trans
      (subgroupOfEquivOfLe hLC).symm
  let : Group.IsPerfect LC := Group.IsPerfect.ofSurjective (f := ec.toMonoidHom) ec.surjective
  have hp : IsPPerfect 2 LC := by
    intro M hM htwoM
    let := hM
    have hs : Subsingleton (LC ⧸ M) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (LC ⧸ M) htwoM.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have hpre := comap_normalizer_map_of_pPerfect q LC hp hq hqn
  have hTL : T ≤ (normalizer c.L).subgroupOf C := by
    rw [subgroupOf_normalizer_eq hLC,←hpre]
    exact comap_mono ((centralizer_le hBK).trans (Subgroup.centralizer_le_normalizer _))
  have hAL : A ≤ normalizer c.L := by
    rintro x ⟨y,hy,rfl⟩
    exact hTL hy
  have hAV : A ≤ normalizer V := coreNatural_normalized A hAL
  have hNV : N ≤ centralizer (V : Set G) := le_centralizer_iff.mp
    (binary_three_source_point_central_eight
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP).2.2
  obtain ⟨common⟩ := t.commonFacts hc
  obtain ⟨a,ha,hmodel⟩ := original_natural_section d c.L b t common hb
  have hAVfix : A ≤ centralizer (V : Set G) := by
    rintro x ⟨y,hy,rfl⟩
    have hyA : (y : G) ∈ A := mem_map_of_mem C.subtype hy
    let f : MulAut V := V.normalizerMonoidHom ⟨y,hAV hyA⟩
    have hf1 : f = 1 := by
      apply modeled_natural_aut_trivial c.L V a ha hmodel f
      intro l v w hw
      let lc : C := ⟨l,hLC l.property⟩
      have he : q lc * q y = q y * q lc := hy (q lc) (hBK (mem_map_of_mem q l.property))
      have hk0 : q (y * lc * y⁻¹ * lc⁻¹) = 1 := by
        simp only [map_mul,map_inv]
        rw [←he]
        group
      have hk : (y : G) * l * (y : G)⁻¹ * (l : G)⁻¹ ∈ N :=
        mem_map_of_mem C.subtype ((QuotientGroup.eq_one_iff _).mp hk0)
      have hu : (l : G) * (f v : G) * (l : G)⁻¹ ∈ V :=
        (hmodel.2.1 l.property (f v)).mp (f v).property
      have hec := (hNV hk _ hu).symm
      change (y : G) * (w : G) * (y : G)⁻¹ =
        (l : G) * ((y : G) * (v : G) * (y : G)⁻¹) * (l : G)⁻¹
      calc
        _ = ((y : G) * l * (y : G)⁻¹ * (l : G)⁻¹) *
            ((l : G) * (f v : G) * (l : G)⁻¹) *
            ((y : G) * l * (y : G)⁻¹ * (l : G)⁻¹)⁻¹ := by
          rw [hw]
          have hfv : (f v : G) = (y : G) * (v : G) * (y : G)⁻¹ := rfl
          rw [hfv]
          group
        _ = _ := by rw [hec,mul_inv_cancel_right]; rfl
    intro v hv
    have hh := congrArg Subtype.val (DFunLike.congr_fun hf1 (⟨v,hv⟩ : V))
    change (y : G) * v * (y : G)⁻¹ = v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hCT : C ≤ normalizer A := by
    let : T.Normal := inferInstance
    intro x hx
    exact T.le_normalizer_map C.subtype (mem_map_of_mem C.subtype
      (show (⟨x,hx⟩ : C) ∈ normalizer T from by rw [normalizer_eq_top]; trivial))
  exact le_centralizer_iff.mp (conjugateSpanBy_le (le_centralizer_iff.mp hAVfix)
    (hCT.trans (normalizer_le_normalizer_centralizer A)))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
