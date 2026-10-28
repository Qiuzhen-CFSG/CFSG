module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveNormalAction
public import Theory.Representation.BinaryAlternatingFiveBorel.PointNormalizedTwoSubgroup
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddConjugation
public import Theory.GroupTheory.PGroup.NormalSupplementCore

/-!
# Excluding normal alternating-five blocks in the escaping-plane case

The marked Borel normalizes QI. Its actual five-point image forces the
two-group image of QI to be even. On the whole four-dimensional block module,
the odd-core offender theorem therefore makes J(QI) act trivially. The
two-group action kernel and the proved centralizer-core bound then contradict
the original Thompson-normalizer control.

Normality of X is the singleton branch hypothesis. The general constituent
argument, including exchanged orbits, is in AlternatingFive/Action.lean. The earlier Kc orbit alternative retains its
geometry and small-parabolic producers and final discharge by
qt-e-152-plane-characteristic-two; no action or marking callback remains.

Source: Aschbacher--Smith preliminary15.2.23, printed p.1115,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

theorem a5_normal_block_action_even
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) [X.Normal]
    (hb : ChapterC.IsAlternatingBlock X 5)
    (q : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))
    (f : I →* Equiv.Perm (Fin 5))
    (hf : ∀ x : X, f x = (q (QuotientGroup.mk' (pCore 2 X) x)).val) :
    ((planeParabolicCore T H ZS).subgroupOf I).map f ≤ alternatingGroup (Fin 5) := by
  obtain ⟨hCJ,P,_e,_j,hP,hJN,_⟩ := d.a5_block_borel_marking_of_source horbit hI hfit hX hb
  let a := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have ha : Function.Surjective a := q.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective ha
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  let B := (normalizer (P : Set X)).map X.subtype
  have hBimage : B.map f = alternatingGroup (Fin 5) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 5)) i := by
    have he : f.comp X.subtype = (alternatingGroup (Fin 5)).subtype.comp a :=
      MonoidHom.ext hf
    rw [map_map,he,←map_map,P.normalizer_map_surjective a ha]
    change (normalizer (R : Set (alternatingGroup (Fin 5)))).map _ = _
    rw [hi]
    ext x
    exact ⟨fun ⟨y,hy,he⟩ => he ▸ ⟨y.property,hy⟩,fun ⟨hy,hf⟩ => ⟨⟨x,hy⟩,hf,rfl⟩⟩
  let Q := planeParabolicCore T H ZS
  have hPI := (d.residual_sup_planeSylow_le hI).trans inf_le_right
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans hPI
  have hBQ : B ≤ normalizer (Q.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hQI]
    rintro b ⟨x,hx,rfl⟩
    have hxC : (x : G) ∈ X.map I.subtype ⊓ centralizer (ZS : Set G) := by
      refine ⟨mem_map_of_mem I.subtype x.property,?_⟩
      have hc : x ∈ (centralizer (ZS : Set G)).comap (I.subtype.comp X.subtype) := by
        rw [hCJ,hJN]
        exact hx
      exact hc
    exact ((d.a5_block_centralizer_le_parabolic horbit hI hfit hX hb).trans
      (((pResidual 2 H).map H.subtype ⊔ planeSylow T ZS).le_normalizer.trans
        (normalizer_le_normalizer_intrinsicCore _))) hxC
  apply BinaryPermutation.AlternatingFiveBorel.even_point_stabilizer_normalizes_twoSubgroup
    _ ((isPGroup_pCoreIn 2 _).comap_subtype.map f) i
  rw [←hBimage]
  exact (map_mono hBQ).trans (le_normalizer_map f)

theorem a5_normal_block_false
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) [X.Normal]
    (hb : ChapterC.IsAlternatingBlock X 5) : False := by
  obtain ⟨q,E,f,hf,hE,_himage,hker,hC⟩ := hb.five_normal_action X
  have heven := d.a5_normal_block_action_even horbit hI hfit hX hb q f hf
  let W := (ChapterC.blockU X).map X.subtype
  let : W.Normal := inferInstance
  let : IsElementaryAbelian 2 (ChapterC.blockU X) := hb.2.1.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  let j : ChapterC.blockU X ≃* W :=
    (ChapterC.blockU X).equivMapOfInjective X.subtype X.subtype_injective
  let F : W ≃* Multiplicative (BinaryPermutation.core (Fin 5)) := j.symm.trans E
  have hF (g : I) (w : W) : (F (MulAut.conjNormal g w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (f g) (F w).toAdd := by
    have hh : j.symm (MulAut.conjNormal g w) =
        MulAut.characteristic (ChapterC.blockU X) (MulAut.conjNormal g) (j.symm w) := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      change g * (w : I) * g⁻¹ = g * (((j.symm w : ChapterC.blockU X) : X) : I) * g⁻¹
      congr 2
      exact (congrArg Subtype.val (j.apply_symm_apply w)).symm
    change (E (j.symm _)).toAdd = _
    rw [hh]
    exact hE g (j.symm w)
  let Q := planeParabolicCore T H ZS
  let Q' := Q.subgroupOf I
  have hPI := (d.residual_sup_planeSylow_le hI).trans inf_le_right
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans hPI
  have hQcore : I.pCoreIn 2 ≤ Q := by
    have hle : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS :=
      (d.core_le_plane hI).trans le_sup_right
    simpa only [inf_eq_right.mpr hle] using inf_pCoreIn_le_of_le 2 hPI
  have hWQ : W ≤ Q' := by
    intro w hw
    have hWcore := (map_mono (f := X.subtype) (ChapterC.blockU_le_core (L := X))).trans
      (pCoreIn_le_of_subnormal 2 hX.subnormal)
    exact hQcore (mem_map_of_mem I.subtype (hWcore hw))
  have hJ := ChapterB.Offenders.thompson_le_kernel_of_even_core_action (Or.inl rfl) W Q' hWQ f
    hC F hF heven
  have hk : IsPGroup 2 (f.comp X.subtype).ker := by
    rw [hker]
    exact pCore_isPGroup
  have hJcore : elementaryAbelianMaxJ Q' ≤ (X ⊔ Q').pCoreIn 2 :=
    (le_inf ((sSup_le fun _ hA => hA.1).trans le_sup_right) hJ).trans
      (inf_ker_le_core_of_two_supplement f X Q' le_normalizer_of_normal
        (isPGroup_pCoreIn 2 _).comap_subtype hk)
  have hm := map_mono (f := I.subtype) hJcore
  rw [←elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
    map_subgroupOf_eq_of_le hQI,map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le hQI] at hm
  have hn : I ≤ normalizer (X.map I.subtype : Set G) := by
    have hh := X.le_normalizer_map I.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  exact d.planeParabolicCore_thompson_not_le_core hI
    (d.alternating_block_not_le_partner horbit hI hfit hX (Or.inl rfl) hb)
    (d.plane_span_extension_core_le_of_marking hI (map_subtype_le _) hn
      (d.a5_block_centralizer_le_parabolic horbit hI hfit hX hb)) hm

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
