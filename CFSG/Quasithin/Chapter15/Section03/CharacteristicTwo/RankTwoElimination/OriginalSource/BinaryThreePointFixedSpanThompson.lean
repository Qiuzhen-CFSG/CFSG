module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFixedSpanOvergroup
public import Theory.GroupTheory.ElementaryThompsonSylowOvergroup
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# The containing component lies in the original normalizer's Thompson subgroup

The original I and fixed-span normalizer have the same full Sylow S, and
I lies in the normalizer. Their elementary Thompson subgroups are therefore
monotone. Every containing C-component meets the normalizer's Thompson
subgroup in the original nonsolvable L, forcing the entire component into
it. The relative C-component property is transported to the literal ambient
Thompson subgroup, without assuming characteristic two of the normalizer.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- Every actual containing component in the fixed-span normalizer is a
component of its elementary Thompson subgroup, with the same ambient image. -/
theorem binary_three_source_fixed_span_thompson
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
    let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
    let NU := normalizer (U : Set G)
    Stellmacher.elementaryAbelianMaxJ I ≤ Stellmacher.elementaryAbelianMaxJ NU ∧
      ∀ D : Subgroup NU, D.IsCComponent → c.L.subgroupOf NU ≤ D →
        D.map NU.subtype ≤ Stellmacher.elementaryAbelianMaxJ NU ∧
        ((D.map NU.subtype).subgroupOf (Stellmacher.elementaryAbelianMaxJ NU)).IsCComponent := by
  let U := conjugateSpanBy (intrinsicFour c.L) (centralizer ({z} : Set G))
  let NU := normalizer (U : Set G)
  let J := Stellmacher.elementaryAbelianMaxJ NU
  have hINU : I ≤ NU := (binary_three_source_fixed_span_strict_overgroup
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).1.le
  have hLS := (binary_three_source_fixed_span_outside
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      K hK hKn hLK eB hrX hrB hm).2.2.2.1
  obtain ⟨S,hS⟩ := hLS
  have hJI : Stellmacher.elementaryAbelianMaxJ I ≤ J :=
    Stellmacher.elementaryAbelianMaxJ_mono_of_contains_sylow I NU hINU S
      (hS ▸ le_sup_right.trans hI.1.2)
  refine ⟨hJI,?_⟩
  intro D hD hLD
  have hLNU : c.L ≤ NU := (component_le c).trans hINU
  have hJNU : J ≤ NU := sSup_le fun A hA => hA.1
  let JN := J.subgroupOf NU
  let : JN.Normal := LocalData.thompson_subgroupOf_normal NU
  have hLns : ¬ Group.IsSolvable (c.L.subgroupOf NU) := by
    intro hs
    let := hs
    let f : (c.L.subgroupOf I) ≃* (c.L.subgroupOf NU) :=
      (subgroupOfEquivOfLe (component_le c)).trans (subgroupOfEquivOfLe hLNU).symm
    exact (LocalData.thompson_component_in c.le_thompson c.component).not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
  have hLJ : c.L.subgroupOf NU ≤ JN := comap_mono (c.le_thompson.trans hJI)
  have hDJ : D ≤ JN := hD.le_normal_of_nonsolvable_subgroup hLns hLD hLJ
  have hDambient : D.map NU.subtype ≤ J := by
    rintro _ ⟨x,hx,rfl⟩
    exact hDJ hx
  refine ⟨hDambient,?_⟩
  let f : JN ≃* J := subgroupOfEquivOfLe hJNU
  have he : (D.subgroupOf JN).map f.toMonoidHom = (D.map NU.subtype).subgroupOf J := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.val,hy,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨⟨y,hDJ hy⟩,hy,Subtype.ext he⟩
  rw [←he]
  exact (hD.subgroupOf hDJ).map_equiv f

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
