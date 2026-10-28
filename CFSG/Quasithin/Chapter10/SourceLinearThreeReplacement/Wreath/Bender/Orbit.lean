module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Orbits
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Component
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.GroupTheory.GeneralizedFitting.SylowComponentOrbit
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Identifying the component orbit with the centralizer span

The local SQTK component theorem makes the T-orbit of I normal in G_z.
The two-perfectness of X puts it in that orbit once X lies in I T.
After recognition of the wreath quotient, the solvable radical is its
two-core. Thus the nontrivial two-perfect seed generates a nonsolvable
normal subgroup of I T. Component conjugacy forces this subgroup to
contain I, identifying its centralizer span with the original T-orbit.

These arguments prove the orbit conclusion from the quotient and the
literal nontrivial seed placement; they assume no orbit normalization.
Source: Aschbacher--Smith 1.2.1(3), 10.2.3(3), and 10.3.3,
printed pp.744--745,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
open Chapter3.Section02
open Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

theorem orbit_normalized (d : CentralizerData T D s) {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G))) :
    centralizer ({d.first * d.second} : Set G) ≤
      normalizer (componentOrbit I (T : Subgroup G) : Set G) := by
  let C := centralizer ({d.first * d.second} : Set G)
  let S := T.subtype d.sylow_le_centralizer
  let A := I.subgroupOf C
  have hC : C ∈ Chapter1.H G := Chapter1.mem_H_of_isTwoLocal
    (isTwoLocal_involution_centralizer d.order)
  have hidx := Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hC) hI.2
  have hn := componentOrbit_normal_of_normal_or_index_two A S (hidx.imp_right And.left)
  have he : (componentOrbit A (S : Subgroup C)).map C.subtype =
      componentOrbit I (T : Subgroup G) := by
    rw [map_componentOrbit]
    change componentOrbit ((I.subgroupOf C).map C.subtype)
      (((T : Subgroup G).subgroupOf C).map C.subtype) = _
    rw [map_subgroupOf_eq_of_le (show I ≤ C from hI.1),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ C from d.sylow_le_centralizer)]
  have hh := (normal_subgroupOf_iff_le_normalizer
    (map_subtype_le (componentOrbit A (S : Subgroup C)))).mp
      (show (((componentOrbit A (S : Subgroup C)).map C.subtype).subgroupOf C).Normal by
        simpa only [subgroupOf, comap_map_eq_self_of_injective C.subtype_injective] using hn)
  rwa [he] at hh

private theorem seed_le_orbit {I : Subgroup G} (z : G)
    (hX : centralizerSeed T L z ≤ I ⊔ (T : Subgroup G)) :
    centralizerSeed T L z ≤ componentOrbit I (T : Subgroup G) := by
  let Y := I ⊔ (T : Subgroup G)
  let O := componentOrbit I (T : Subgroup G)
  let X := centralizerSeed T L z
  let : (O.subgroupOf Y).Normal := componentOrbit_normal_subgroupOf_sup I T
  have hgen : O.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤ := by
    rw [← subgroupOf_sup (componentOrbit_le_sup I T) le_sup_right, componentOrbit_sup]
    exact subgroupOf_self Y
  have hq := isPGroup_quotient_of_sup_eq_top (O.subgroupOf Y)
    ((T : Subgroup G).subgroupOf Y) T.isPGroup'.comap_subtype hgen
  have hp : IsPPerfect 2 (X.subgroupOf Y) :=
    (isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hX).symm.toMonoidHom (subgroupOfEquivOfLe hX).symm.surjective
  have hle : X.subgroupOf Y ≤ O.subgroupOf Y :=
    (le_pResidual_of_isPPerfect _ hp).trans (sInf_le ⟨inferInstance,hq⟩)
  intro x hx
  exact hle (show (⟨x,hX hx⟩ : Y) ∈ X.subgroupOf Y from hx)

theorem orbit_eq_span_of_recognized_join (d : CentralizerData T D s) {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)))
    (e : ((I ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)) ≃* W)
    (hX : centralizerSeed T L (d.first * d.second) ≤ I ⊔ (T : Subgroup G))
    (hne : centralizerSeed T L (d.first * d.second) ≠ ⊥) :
    componentOrbit I (T : Subgroup G) = componentSpan T L (d.first * d.second) := by
  let z := d.first * d.second
  let X := centralizerSeed T L z
  let C := centralizer ({z} : Set G)
  let O := componentOrbit I (T : Subgroup G)
  let Y := I ⊔ (T : Subgroup G)
  let N := componentSpan T L z
  have hYC : Y ≤ C := sup_le hI.1 d.sylow_le_centralizer
  have hNO : N ≤ O := conjugateSpanBy_le
    (seed_le_orbit z hX) (orbit_normalized d hI)
  have hNY : N ≤ Y := hNO.trans (componentOrbit_le_sup I T)
  have hYN : Y ≤ normalizer (N : Set G) := hYC.trans (le_normalizer_conjugateSpanBy X C)
  let A := N.subgroupOf Y
  let : A.Normal := normal_subgroupOf_of_le_normalizer hYN
  have hXY : X ≤ Y := (le_conjugateSpanBy X C).trans hNY
  have hns : ¬ Group.IsSolvable A := by
    intro hsol
    have hrad : A ≤ solvableRadical Y := le_solvableRadical A inferInstance hsol
    rw [wreath_quotient_radical e] at hrad
    have hXcore : X ≤ (pCore 2 Y).map Y.subtype := by
      intro x hx
      exact mem_map.mpr ⟨⟨x,hXY hx⟩,
        hrad (show (⟨x,hXY hx⟩ : Y) ∈ A from le_conjugateSpanBy X C hx),rfl⟩
    have hpX : IsPGroup 2 X := (pCore_isPGroup (p := 2) (G := Y)).map Y.subtype |>.to_le hXcore
    have hperfect : IsPPerfect 2 X := isPPerfect_embedded_pResidual 2 _
    have hbot : (⊥ : Subgroup X) = ⊤ :=
      hperfect ⊥ inferInstance (hpX.of_equiv QuotientGroup.quotientBot.symm)
    apply hne
    apply bot_unique
    intro x hx
    have hxbot : (⟨x,hx⟩ : X) ∈ (⊥ : Subgroup X) := hbot.symm ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hxbot)
  obtain ⟨B,hB⟩ := exists_isCComponent_of_not_isSolvable hns
  let K := B.map A.subtype
  have hK : K.IsCComponent := hB.map_subtype (inferInstance : A.Normal).isSubnormal
  have hKN : K ≤ N.subgroupOf Y := map_subtype_le B
  have hIY : (I.subgroupOf Y).IsCComponent := hI.2.subgroupOf_of_le le_sup_left hYC
  have hgen : I.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤ := by
    rw [← subgroupOf_sup (show I ≤ Y from le_sup_left) (show (T : Subgroup G) ≤ Y from le_sup_right)]
    exact subgroupOf_self Y
  obtain ⟨t,ht⟩ := hIY.conjugate_of_pGroup_generated hK
    (T.isPGroup'.comap_subtype (K := Y)) hgen
  have hIN : I ≤ N := by
    intro i hi
    have htG : (t : Y).val ∈ (T : Subgroup G) := t.property
    have hc : (MulAut.conj (t : Y))
        (⟨i,(show I ≤ Y from le_sup_left) hi⟩ : Y) ∈ K := by
      rw [ht]
      exact mem_map_of_mem _ hi
    exact (mem_normalizer_iff.mp
      (hYN ((show (T : Subgroup G) ≤ Y from le_sup_right) htG)) i).mpr (hKN hc)
  exact le_antisymm
    (iSup_conjugates_le_of_le_normalizer I T N hIN (le_sup_right.trans hYN)) hNO

theorem recognition_of_join (d : CentralizerData T D s) {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)))
    (e : ((I ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (I ⊔ (T : Subgroup G) : Subgroup G)) ≃* W)
    (hX : centralizerSeed T L (d.first * d.second) ≤ I ⊔ (T : Subgroup G))
    (hne : centralizerSeed T L (d.first * d.second) ≠ ⊥) :
    Nonempty ((componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃* W) ∧
    componentOrbit I (T : Subgroup G) = componentSpan T L (d.first * d.second) := by
  have ho := orbit_eq_span_of_recognized_join d hI e hX hne
  have hY : componentJoin T L (d.first * d.second) = I ⊔ (T : Subgroup G) := by
    rw [componentJoin, ← ho, componentOrbit_sup]
  exact ⟨hY.symm ▸ ⟨e⟩,ho⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
