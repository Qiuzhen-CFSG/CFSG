module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourJankoCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourComponents
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpOrdinary


/-!
# Residual escape on the original Hermitian nine-space

If an involution-centralizer residual in a containing J₄ cover lies in
N_G(L), source E.6.1 makes it normalize the unchanged original module.
The field-four tensor marking gives that module order 512, contrary to
the native J₄ centralizer obstruction. Odd covering centers and central
two-kernels are retained; in the ordinary branch the original residual's
fixed-free action proves that the module embeds in the central quotient.

The proof-only import reuses the existing internal transport for that
original pushing-up residual, preserving its public boundary.
Source: Aschbacher--Smith 4.4.3, printed pp.622--623, and E.6.1,
as applied in 8.2.7, printed p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
private theorem original_hermitian_centralizer_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (H : Subgroup G) (K : Subgroup H)
    (hVK : V ≤ K.map H.subtype)
    (z : K) (hzV : ((z : H) : G) ∈ V) (hz : orderOf z = 2)
    (hRM : ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map
        (H.subtype.comp K.subtype) ≤ normalizer (L : Set G)) :
    let k := (H.subtype.comp K.subtype).comp
      (centralizer ({z} : Set K)).subtype
    ∃ W : Subgroup (centralizer ({z} : Set K)), IsElementaryAbelian 2 W ∧
      W.map k = V ∧ Nat.card W = Nat.card V ∧
      solvableResidual (centralizer ({z} : Set K)) ≤ normalizer (W : Set _) ∧
      (⟨z,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({z} : Set K)) ∈ W := by
  let := D.elementary
  let zG : G := ((z : H) : G)
  let Ck := centralizer ({z} : Set K)
  let j := H.subtype.comp K.subtype
  let k := j.comp Ck.subtype
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hki : Function.Injective k := hj.comp Ck.subtype_injective
  have hVr : V ≤ k.range := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := hVK hv
    let w : K := ⟨u,hu⟩
    have hw : w ∈ Ck := by
      apply mem_centralizer_singleton_iff.mpr
      apply hj
      exact setLike_mul_comm hv hzV
    exact ⟨⟨w,hw⟩,rfl⟩
  let W := V.comap k
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (k.subgroupComap V) (fun x y he => Subtype.ext (hki (congrArg (fun v : V => (v : G)) he)))
  have hWcard : Nat.card W = Nat.card V := by
    let d := (W.equivMapOfInjective k hki).trans (MulEquiv.subgroupCongr (map_comap_eq_self hVr))
    exact Nat.card_congr d.toEquiv
  have hzG : orderOf zG = 2 := (orderOf_coe (z : H)).trans
    ((orderOf_coe z).trans hz)
  have hzne : zG ≠ 1 := by intro he; rw [he,orderOf_one] at hzG; omega
  have hZne : zpowers zG ≠ ⊥ := by
    intro he
    exact hzne (mem_bot.mp (he ▸ mem_zpowers zG))
  have hNV : normalizer (L : Set G) ⊓ centralizer ({zG} : Set G) ≤ normalizer (V : Set G) := by
    have hh := (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer hZne (zpowers_le.mpr (hV ▸ hzV))
    simpa only [zpowers_eq_closure,centralizer_closure,hV] using hh
  have hn : solvableResidual Ck ≤ normalizer (W : Set Ck) := by
    apply le_trans _ (V.le_normalizer_comap k)
    intro r hr
    apply hNV
    refine ⟨?_,?_⟩
    · exact hRM (mem_map_of_mem j (mem_map_of_mem Ck.subtype hr))
    · exact mem_centralizer_singleton_iff.mpr
        (congrArg j (mem_centralizer_singleton_iff.mp r.property))
  exact ⟨W,inferInstance,map_comap_eq_self hVr,hWcard,hn,hzV⟩

private theorem hermitian_card_nine
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) : Nat.card D.sourceOrbit = 512 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
  change Nat.card D.sourceOrbit = _ at hc
  rw [Nat.card_zmod,(D.hermitianOrbitCoordinates 1 d).finrank_eq,finrank_binary] at hc
  exact hc

private theorem original_janko_residual_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (H : Subgroup G) (K : Subgroup H)
    (hVK : V ≤ K.map H.subtype)
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (hkernel : Nat.Coprime 2 (Nat.card (center K)) ∨
      (IsPGroup 2 (center K) ∧ V ⊓ centralizer (K.map H.subtype : Set G) = ⊥))
    (z : K) (hzV : ((z : H) : G) ∈ V) (hz : orderOf z = 2) :
    ¬ ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype) ≤
        normalizer (L : Set G) := by
  intro hRM
  obtain ⟨W,hW,hmap,hcard,hn,hzW⟩ :=
    D.original_hermitian_centralizer_module h hmany hV hnon H K hVK z hzV hz hRM
  let := hW
  have hcard' : Nat.card W = 512 := hcard.trans (by simpa only [hV] using D.hermitian_card_nine d)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  rcases hkernel with ho | ⟨hp,hfix⟩
  · exact janko_no_nine_residual_odd_cover f hf (hk.symm ▸ ho) z hz W hcard' hn
  · let c := f.elementCentralizerMap z
    have hi : Function.Injective (c.comp W.subtype) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro w hw
      have hfz : f ((w : centralizer ({z} : Set K)) : K) = 1 :=
        congrArg (fun u : centralizer ({f z} : Set Janko4.Model) => (u : Janko4.Model)) hw
      have hcent : ((w : centralizer ({z} : Set K)) : K) ∈ center K := hk ▸ hfz
      let j := H.subtype.comp K.subtype
      have hv : j ((w : centralizer ({z} : Set K)) : K) ∈ V :=
        hmap ▸ mem_map_of_mem _ w.property
      have hc : j ((w : centralizer ({z} : Set K)) : K) ∈
          centralizer (K.map H.subtype : Set G) := by
        rintro _ ⟨y,hy,rfl⟩
        exact congrArg j (mem_center_iff.mp hcent ⟨y,hy⟩)
      have hw1 : j ((w : centralizer ({z} : Set K)) : K) = 1 :=
        mem_bot.mp (hfix ▸ (show _ ∈ V ⊓ centralizer (K.map H.subtype : Set G) from ⟨hv,hc⟩))
      exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext hw1)))
    have hz' : orderOf (f z) = 2 := by
      have hh := orderOf_injective (c.comp W.subtype) hi (⟨⟨z,mem_centralizer_singleton_iff.mpr rfl⟩,hzW⟩ : W)
      exact (orderOf_coe (c ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩)).trans
        (hh.trans (by simpa only [Subgroup.orderOf_mk] using hz))
    exact janko_no_nine_residual_two_cover f hf hk.le (hk.symm ▸ hp) z hz' W hi hcard' hn
/-- Every involution of the original nine-space in the normal J₄ branch
has its actual full component-centralizer residual escaping N_G(L). -/
theorem sourceOrbit_hermitian_normal_janko_residual_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (hVK : D.sourceOrbit ≤ K.map (normalizer (A : Set G)).subtype)
    (hcent : centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)))
    (e : (K ⧸ center K) ≃* Janko4.Model)
    (z : K) (hzV : ((z : normalizer (A : Set G)) : G) ∈ D.sourceOrbit)
    (hz : orderOf z = 2) :
    ¬ ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map
        ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G) := by
  have hZ : (center K).map K.subtype ≤ pPrimeCore 2 (normalizer (A : Set G)) := by
    rw [←hcent]
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hx ⟨y,hy⟩)
  have ho := (pPrimeCore_coprime_card (p := 2) (G := normalizer (A : Set G))).of_dvd_right
    (card_dvd_of_le hZ)
  rw [card_map_of_injective K.subtype_injective] at ho
  exact D.original_janko_residual_escape h hmany hV hnon d _ K
    (by simpa only [hV] using hVK) e (.inl ho) z (by simpa only [hV] using hzV) hz

/-- The same residual escape holds for each actual ordinary pushing-up
component. Its central two-kernel is retained and the original module embeds
because the original covering residual has no fixed points. -/
theorem sourceOrbit_hermitian_ordinary_janko_residual_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (z : K) (hzV : ((z : H) : G) ∈ D.sourceOrbit) (hz : orderOf z = 2) :
    ¬ ((solvableResidual (centralizer ({z} : Set K))).map
      (centralizer ({z} : Set K)).subtype).map (H.subtype.comp K.subtype) ≤
        normalizer (L : Set G) := by
  obtain ⟨e⟩ := D.sourceOrbit_hermitian_field_four_ordinary_janko h hmany hV hnon d B eQ hfield hw K hK
  obtain ⟨hn,hcore,hfix,he⟩ := D.sourceOrbit_pushingUp_residual_data h hmany hV hnon hw
  obtain ⟨_,_,_,_,_,_,hc,_,_,_,hVF,_⟩ := hw
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFK : F ≤ K.map H.subtype := by
    intro x hx
    exact ⟨⟨x,hc.component_le.trans hc.local_le hx⟩,
      hc.ordinary_component_contains_original K hK hx,rfl⟩
  let := hK.2
  have hzcore : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)
  have hp : IsPGroup 2 (center K) := hzcore.symm ▸ pCore_isPGroup
  have hfixK : V ⊓ centralizer (K.map H.subtype : Set G) = ⊥ := by
    rw [hV]
    exact bot_unique ((inf_le_inf_left _ (centralizer_le hFK)).trans hfix.le)
  exact D.original_janko_residual_escape h hmany hV hnon d H K
    (by simpa only [hV] using hVF.trans hFK) e (.inr ⟨hp,hfixK⟩)
    z (by simpa only [hV] using hzV) hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
