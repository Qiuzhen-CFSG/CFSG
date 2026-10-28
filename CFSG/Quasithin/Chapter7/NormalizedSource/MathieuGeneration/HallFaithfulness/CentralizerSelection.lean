module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicAmbient
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.CentralizerSelection
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleOverlap

/-!
# The original J₄ component in an involution centralizer

Reselect the maximal two-local through a core involution without replacing
the original full J₄ covering component. The original perfect intersection
residual lies in both components; quasisimple overlap and equality of the
central quotient orders identify them. The original component is therefore
normal in the reselected two-local and is an ordinary component of the
involution centralizer. Its placed cubic residual is an ordinary normal
component of the actual simultaneous centralizer, with every original
inclusion and quotient map retained.

The literal Hall obstruction supplies this configuration without extra
premises. Promotion to the full cubic centralizer, the final pushing-up
contradiction, and the M₂₄ comparison remain separate mathematical steps.

Source: Aschbacher--Smith 4.2.13, printed p.612, used by 4.4.14,
printed pp.623--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

theorem sourceOrbit_mathieu_fitting_escape_of_witness
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    {A J H W : Subgroup G} (hw : Witness L V A J H W) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H := by
  intro hf
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hn,hcommV,hVL,⟨e,he⟩,hrest⟩
  let M := normalizer (L : Set G)
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let := h.quasisimple
  let : IsQuasisimple (F ⧸ pCore 2 F) := IsQuasisimple.of_mulEquiv e.symm
  have hne : H ≠ M := fun he => hstrict.ne (by rw [he,inf_idem])
  have hs := h.simpleQTKE.twoLocal_sqtk hM.1.1
  have hd := reciprocal_setup hH hM.1 hs hne hf
  have hF : F = L := residual_eq_of_fitting_contained L.le_normalizer le_rfl
    hH hM.1 hs hne hcover hf
  obtain ⟨hcomp,hnorm,hi⟩ := index_two_of_fitting_contained hc hn hstrict hd.1 hf
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hLH : L ≤ H := hF ▸ hFH
  have hcompL : (L.subgroupOf H).IsCComponent := hF ▸ hcomp
  have hnormL : normalizer (L.subgroupOf H : Set H) = M.subgroupOf H := hF ▸ hnorm
  let a : (L.subgroupOf H) ≃* L := subgroupOfEquivOfLe hLH
  let q : ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q.symm
  let z := (centerQuotientCongr q).trans (D.orbitCentralQuotientEquiv h)
  have hm' : HasMathieuCentralQuotient ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) := by
    rcases hm with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact Or.inl ⟨z.trans f⟩
    · exact Or.inr (Or.inl ⟨z.trans f⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨z.trans f⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨z.trans f⟩))
  let : (L.subgroupOf H).Normal := normal_of_mathieu_central_core_quotient
    hc.sqtk hcompL hm'
  rw [normalizer_eq_top] at hnormL
  rw [←hnormL,index_top] at hi
  norm_num at hi

theorem sourceOrbit_mathieu_ordinary_component_of_witness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
      Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  have hc := hw.2.2.2.2.2.2.1
  have hf := D.sourceOrbit_mathieu_fitting_escape_of_witness h.toHypothesis1221 hm hw
  have hf' : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hh => hf (hh.trans (comap_mono inf_le_right))
  obtain ⟨K,hK,hq,hout,hn,hcases⟩ := hc.ordinary_or_constrained_escape hf'
  rcases hcases with hKo | hcon
  · exact ⟨K,hKo,hc.ordinary_component_normal K hKo,
      hc.ordinary_component_contains_original K hKo,
      D.sourceOrbit_mathieu_pushingUp_ordinary_janko h hmany hV hm hnon hw K hKo⟩
  · exact (D.sourceOrbit_mathieu_no_constrained_pushingUp h.toHypothesis1221 hm hw
      K hK hq hout hcon).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_pushingUp_component_in_involution_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : IsComponent H K)
    (hFK : ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K)
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    ∃ (J₀ : Subgroup G) (r : H.pCoreIn 2) (H₁ W₁ : Subgroup G),
      Witness L V A J₀ H W ∧ Witness L V A J₀ H₁ W₁ ∧
      J₀ ≤ J ∧ J₀ ⊓ L = J ⊓ L ∧ J₀.pCoreIn 2 = J.pCoreIn 2 ∧
      orderOf r = 2 ∧ J₀ ≤ centralizer ({(r : G)} : Set G) ∧
      centralizer ({(r : G)} : Set G) ≤ H₁ ∧
      IsComponentIn (K.map H.subtype) H₁ ∧ ((K.map H.subtype).subgroupOf H₁).Normal ∧
      IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) := by
  obtain ⟨J₀,r,hw₀,hJ₀J,hsame,hcore,hr,hKr,hJr,H₁,hH₁,hCH,hJH₁,hKH₁,hout₁⟩ :=
    sourceOrbit_pushingUp_centralizer_arrangement h.toHypothesis1221 hw K hK hFK hout
  obtain ⟨W₁,hw₁⟩ := D.sourceOrbit_witness_reselect_overgroup h.toHypothesis1221 hw₀
    hH₁ hJH₁ hout₁
  obtain ⟨K₁,hK₁,hn₁,hF₁K₁,⟨e₁⟩⟩ :=
    D.sourceOrbit_mathieu_ordinary_component_of_witness h hmany hV hm hnon hw₁
  let Kg := K.map H.subtype
  let Kb := Kg.subgroupOf H₁
  let eb : Kb ≃* K := (subgroupOfEquivOfLe hKH₁).trans
    (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let := hK.2
  let := hK₁.2
  let := hn₁
  let : IsQuasisimple Kb := IsQuasisimple.of_mulEquiv eb.symm
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hFH : F ≤ H := (map_subtype_le _).trans inf_le_right
  have hFL : F ≤ L := (map_subtype_le _).trans inf_le_left
  have hFKg : F ≤ Kg := by
    have hh := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hFH] at hh
  have hFH₁ : F ≤ H₁ := hFKg.trans hKH₁
  let : Group.IsPerfect F := Group.IsPerfect.map _
  let Fb := F.subgroupOf H₁
  let : Group.IsPerfect Fb := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFH₁).symm.toMonoidHom) (subgroupOfEquivOfLe hFH₁).symm.surjective
  have hneF : F ≠ ⊥ := fun he => D.ne_bot (bot_unique (he ▸ hw.2.2.2.2.2.2.2.2.2.2.1))
  have hneFb : Fb ≠ ⊥ := by
    intro he
    have hh := congrArg (map H₁.subtype) he
    exact hneF (by simpa only [Fb,map_subgroupOf_eq_of_le hFH₁,Subgroup.map_bot] using hh)
  have hFK₁ : Fb ≤ K₁ := by
    have hF₁ := le_map_solvableResidual_of_isPerfect F (L ⊓ H₁) (le_inf hFL hFH₁)
    intro x hx
    exact hF₁K₁ (hF₁ hx)
  have hKbK₁ : Kb ≤ K₁ := quasisimple_le_normal_of_nonabelian_overlap Kb K₁ Fb
    (subgroupOf_mono H₁ hFKg) hFK₁ (by rwa [commutator_eq_self])
  let X := Kb.subgroupOf K₁
  let ex : X ≃* K := (subgroupOfEquivOfLe hKbK₁).trans eb
  let : IsQuasisimple X := IsQuasisimple.of_mulEquiv ex.symm
  have hX : X = ⊤ := quasisimple_subgroup_eq_top_of_central_quotient_card X (by
    rw [Nat.card_congr ((centerQuotientCongr ex).trans e).toEquiv,
      Nat.card_congr e₁.toEquiv])
  have hKb : Kb = K₁ := le_antisymm hKbK₁ (subgroupOf_eq_top.mp hX)
  have hrel : IsComponentIn Kg H₁ := ⟨hKH₁,by change IsComponent H₁ Kb; rw [hKb]; exact hK₁⟩
  exact ⟨J₀,r,H₁,W₁,hw₀,hw₁,hJ₀J,hsame,hcore,hr,hJr,hCH,hrel,
    (by change Kb.Normal; rw [hKb]; exact hn₁),hrel.restrict hKr hCH⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem cubicResidualImage_component_in_simultaneous
    (H : Subgroup G) (K : Subgroup H) (x : K)
    [IsQuasisimple (solvableResidual (centralizer ({x} : Set K)))]
    (r : G) (H₁ : Subgroup G)
    (hKH₁ : K.map H.subtype ≤ H₁)
    (hn : ((K.map H.subtype).subgroupOf H₁).Normal)
    (hKr : K.map H.subtype ≤ centralizer ({r} : Set G))
    (hCH : centralizer ({r} : Set G) ≤ H₁) :
    let C := centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({r} : Set G)
    IsComponentIn (cubicResidualImage H K x) C ∧
      ((cubicResidualImage H K x).subgroupOf C).Normal := by
  let C := centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({r} : Set G)
  let S := cubicResidualImage H K x
  let f := H.subtype.comp K.subtype
  have hi : Function.Injective f := H.subtype_injective.comp K.subtype_injective
  have hrange : f.range = K.map H.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  have hN : H₁ ≤ normalizer (K.map H.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH₁).mp hn
  have hn0 := centralizer_residual_image_normalized f hi x
  rw [hrange,←map_map] at hn0
  have hnorm : C ≤ normalizer (S : Set G) :=
    (le_inf (inf_le_right.trans (hCH.trans hN)) inf_le_left).trans hn0
  have hSC : S ≤ C := by
    rintro y ⟨d,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨mem_centralizer_singleton_iff.mpr
      (congrArg f (mem_centralizer_singleton_iff.mp s.property)),
      hKr ⟨s.val.val,s.val.property,rfl⟩⟩
  let eS : (solvableResidual (centralizer ({x} : Set K))) ≃* S :=
    ((solvableResidual (centralizer ({x} : Set K))).equivMapOfInjective
      (centralizer ({x} : Set K)).subtype
      (centralizer ({x} : Set K)).subtype_injective).trans
      (((solvableResidual (centralizer ({x} : Set K))).map
        (centralizer ({x} : Set K)).subtype).equivMapOfInjective f hi)
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS
  let hnS := normal_subgroupOf_of_le_normalizer hnorm
  exact ⟨⟨hSC,hnS.isSubnormal,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hSC).symm⟩,hnS⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Subgroup Theory.GroupTheory
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Sporadic.Mathieu Janko4.InvolutionCentralizers

/-- The original cubic and full cover, now ordinary components in the actual
involution centralizer and simultaneous centralizer. -/
@[expose] def MathieuPushingUpCentralizedCubicCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Arrange the source involution centralizer without changing the original
J₄ cover, cubic, placed conjugate, residual or quotient maps. -/
theorem sourceOrbit_mathieu_pushingUp_centralized_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A : Subgroup G} (hc : MathieuPushingUpAmbientCubicCase L V A) :
    MathieuPushingUpCentralizedCubicCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,e,x,hx,hqx,hmem,he,hquasi,heq,
    ⟨g,hg,hqy,hey,hdata,huy⟩,hux⟩ := hc
  obtain ⟨J₀,r,H₁,W₁,hw₀,hw₁,hJ₀J,hsame,hcore,hr,hJr,hCH,hrel,hn₁,hKr⟩ :=
    D.sourceOrbit_pushingUp_component_in_involution_centralizer
      h hmany hV hm hnon hw K hK hFK hout e
  let := hqy
  have hs := cubicResidualImage_component_in_simultaneous H K (g * (x : K) * g⁻¹)
    (r : G) H₁ hrel.1 hn₁ hKr.1 hCH
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,huy⟩,hux⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction supplies an actual involution-centralizer
component on the original full J₄ cover, and the original placed residual
is a normal ordinary component of the simultaneous centralizer. -/
theorem sourceOrbit_mathieu_hall_centralized_cubic_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpCentralizedCubicCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_ambient_cubic_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp (D.sourceOrbit_mathieu_pushingUp_centralized_cubic h hmany hV hm hnon) id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
