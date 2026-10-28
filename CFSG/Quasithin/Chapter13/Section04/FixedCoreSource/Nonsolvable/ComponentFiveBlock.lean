module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFiveBaumann
public import CFSG.Quasithin.ChapterB.Section02.AlternatingFiveChief
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Recognition

/-!
# Recognizing the selected A₅ block from the original augmentation module

In the ordinary original A₆ row, the augmentation alternative makes L short.
Its point residual has at most two noncentral two-chief factors. The reciprocal
point residual is the same literal subgroup inside K. Transporting that budget
to the marked A₅ point centralizer forces [O₂(K), K] to equal the whole moved
module, and the ordinary block recognition theorem then identifies K as an
A₅ block.

The large-distance input remains explicit, with producer
qt-e-ms-small-a6-exhaustion-large-distance. The final source assembly belongs to
qt-d-1341-nonsolvable-source and qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.10(1), printed p.908, using 13.2.2(7).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

private theorem component_sylow_in_original
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
  let X := K ⊔ (T : Subgroup G)
  let N := K.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup N).map e.toMonoidHom).map K.subtype ≤ _
  have he : ((Q : Subgroup N).map e.toMonoidHom).map K.subtype =
      ((Q : Subgroup N).map N.subtype).map X.subtype := by
    rw [map_map,map_map]
    rfl
  rw [he,hQ]
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])


/-- The actual selected A₅ component is a block, with its commutator layer
identified with the original moved orbit. -/
theorem ordinary_five_block_of_largeDistance
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ChapterC.IsAlternatingBlock K 5 ∧
      (ChapterC.blockU K).map K.subtype =
        ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ := by

  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hshort := ordinary_five_short_of_largeDistance hl h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨DK,qK,e,he⟩ := component_five_marking h₀ h structural D m h1332 modules
    hzT hz1 hKz hHN hKM hfK eK
  have hUK : U ≤ K := DK.le_component
  let Ui := U.subgroupOf K
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer DK.normalizes
  let := DK.elementary
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.comap_of_injective K.subtype K.subtype_injective U
  let eu : Ui ≃* U := subgroupOfEquivOfLe hUK
  let ei := eu.trans e
  let q := qK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := qK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ qK.injective,QuotientGroup.ker_mk']
  have hei (k : K) (v : Ui) : (ei (MulAut.conjNormal k v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q k).val (ei v).toAdd := by
    exact he k (eu v)
  obtain ⟨w,hw,hTw,hX⟩ := component_fixed_generator_point_overgroup h₀ h structural m
    hzT hz1 hKz hTK hKM
  let wi := eu.symm w
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg eu hh)
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  have hSw : (S : Subgroup K) ≤ centralizer ({wi.val} : Set K) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTw (hS (mem_map_of_mem K.subtype hx))))
  let C := centralizer ({wi.val} : Set K)
  have hCm : C.map K.subtype = K ⊓ centralizer ({m.constant.val} : Set G) := by
    ext k
    constructor
    · rintro ⟨a,ha,rfl⟩
      have hc : a.val ∈ centralizer ({w.val} : Set G) :=
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))
      exact ⟨a.property,(hX.ge ⟨mem_sup_left a.property,hc⟩).2⟩
    · rintro ⟨hk,hc⟩
      have hwc := (hX.le ⟨mem_sup_left hk,hc⟩).2
      exact ⟨⟨k,hk⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hwc)),rfl⟩
  have hres := (ordinary_five_component_residuals h₀ h structural D m h1332 modules
    eL z hzT hzL hKz hHN hKM hfK eK).2.1
  let R := (primeToResidual 3 C).map C.subtype
  have hRm : R.map K.subtype = Solvable.firstCentralizerResidual L z.val := by
    change ((primeToResidual 3 C).map C.subtype).map K.subtype = _
    rw [map_embedded_primeToResidual_of_hom,hCm,←Solvable.firstCentralizerResidual_eq,hres]
  let er : primeToResidual 3 C ≃* Solvable.firstCentralizerResidual L z.val :=
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).trans
      ((R.equivMapOfInjective K.subtype K.subtype_injective).trans (MulEquiv.subgroupCongr hRm))
  have hcount : ∀ s : ChiefSeries (primeToResidual 3 C),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ 2 := by
    intro s hs0 hs1
    have hc := s.mapActor_complete er hs0 hs1
    have hh := core_firstResidual_chief_count_le_two D m hshort eL z hzL
      (s.mapActor er) hc.1 hc.2
    rwa [s.mapActor_noncentralTwoCount] at hh
  have hU : ⁅Ui,(⊤ : Subgroup K)⁆ = Ui := by
    apply map_injective K.subtype_injective
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hUK]
    exact component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hf := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK
  have hb : ChapterC.blockU K = Ui :=
    ChapterB.AlternatingFivePoint.core_commutator_of_point_chief_budget Ui q hq hk ei hei
      hf.2.1.2.1 hU wi hwi S hSw hcount
  have hbmap : (ChapterC.blockU K).map K.subtype = U := by
    rw [hb,map_subgroupOf_eq_of_le hUK]
  refine ⟨?_,hbmap⟩
  let eb := (MulEquiv.subgroupCongr hb).trans ei
  apply Section03.Noncentrality.OrdinaryBlockRecognition.alternatingBlock_of_layer qK eb ?_
    hf.2.1.2.1 hf.2.1.2.2
  intro k v
  exact hei k ((MulEquiv.subgroupCongr hb) v)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
