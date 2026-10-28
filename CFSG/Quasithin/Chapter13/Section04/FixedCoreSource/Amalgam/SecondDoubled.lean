module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondModels
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSix
public import Theory.Representation.BinaryPermutation.SixNaturalSylowFixed
public import Theory.Representation.OmegaSeedFixedSpace

/-!
# The actual second omega module is doubled natural

Thompson movement places the second component in the offender group.
The completed FF classification, applied to the same reduced omega span,
leaves a chosen module or two natural SL₃(2) summands. The original
fixed-free chosen-module classification excludes the former: a natural
three-space has order eight, smaller than the constructed cubic orbit,
while the natural A₆ module has at most two Sylow-fixed vectors and the
original seed has four.

Thus the original second join has a component with an actual SL₃(2)
quotient and a doubled-natural action equivalence on its omega span,
which has order 64. The theorem retains the original vertex residuals,
ordinary J(T), both action kernels, and the literal component quotient.
It assumes no chosen module, model selection, or movement callback.

The earlier Chapter12/13.3 inputs remain explicit. The Baumann/short-block
chief-factor contradiction is still needed to exclude the original first
solvable join and assemble the restricted plane theorem.
Source: Aschbacher--Smith B.5.1 and 13.4.7(3), printed pp.99,903--904.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {C U : Subgroup G}

/-- Thompson movement and the actual two remaining component quotients make
this very reduced module chosen or a doubled natural three-space. -/
theorem chosen_or_double
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hUH : U ≤ C ⊔ (T : Subgroup G))
    (hred : IsPReduced 2 (U.subgroupOf (C ⊔ (T : Subgroup G))))
    (hK : (C.subgroupOf (C ⊔ (T : Subgroup G))).IsCComponent)
    (hqC : IsQuasisimple (C ⧸ pCore 2 C))
    (hSQ : IsSQTK KnownSimple.IsKnownSimple (C ⊔ (T : Subgroup G) : Subgroup G))
    (hgen : ⁅C,elementaryAbelianMaxJ (T : Subgroup G)⁆ = C)
    (hmove : ⁅U,C⁆ = U) (hne : U ≠ ⊥)
    (hmodels : Nonempty ((C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6))) :
    Nonempty (ChosenModule T C U) ∨
    ∃ q : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
      ∃ e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector),
        let hCU := le_normalizer_of_normal_subgroupOf hUH (hK := hred.normal)
        ∀ (c : C) (v : U),
          (e (U.normalizerMonoidHom ⟨c.val,hCU (mem_sup_left c.property)⟩ v)).toAdd =
            (BinaryLinearThree.W.prod BinaryLinearThree.W)
              (q (QuotientGroup.mk' (pCore 2 C) c)) (e v).toAdd := by
  let H := C ⊔ (T : Subgroup G)
  let K := C.subgroupOf H
  let W := U.subgroupOf H
  have hCH : C ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hnC : H ≤ normalizer (C : Set G) := sup_le C.le_normalizer hTC
  let : K.Normal := normal_subgroupOf_of_le_normalizer hnC
  let : W.Normal := hred.normal
  let : IsElementaryAbelian 2 W := hred.elementary
  have hUn : H ≤ normalizer (U : Set G) := le_normalizer_of_normal_subgroupOf hUH
  let S := T.subtype hTH
  let a : K ≃* C := subgroupOfEquivOfLe hCH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hqK : IsQuasisimple (K ⧸ pCore 2 K) := by
    let := hqC
    exact IsQuasisimple.of_mulEquiv aq.symm
  have hsup : K ⊔ (S : Subgroup H) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hCH hTH,subgroupOf_self]
  have hgenK : ⁅K,elementaryAbelianMaxJ (S : Subgroup H)⁆ = K := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hCH,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    change ⁅C,elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf H).map H.subtype)⁆ = C
    rw [map_subgroupOf_eq_of_le hTH]
    exact hgen
  have hmoveW : ⁅W,K⁆ = W := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hCH,map_subgroupOf_eq_of_le hUH]
    exact hmove
  have hneW : W ≠ ⊥ := by
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact hne hh
  have chosen (hmin : ∀ B : Subgroup H, B ≤ W → K ≤ normalizer (B : Set H) →
      B = W ∨ B ≤ centralizer (K : Set H)) : Nonempty (ChosenModule T C U) := by
    apply Section03.PlaneNoncentralitySource.exists_chosenModuleOfMinimal
      hred hUH hTC hUn hmove hne
    intro B hBU hn
    have hBn : K ≤ normalizer (B.subgroupOf H : Set H) := by
      apply le_normalizer_iff.mpr
      intro k hk b hb
      exact (mem_normalizer_iff.mp (hn hk) b.val).mp hb
    rcases hmin (B.subgroupOf H) (comap_mono hBU) hBn with he | hc
    · left
      have hh := congrArg (map H.subtype) he
      rwa [map_subgroupOf_eq_of_le (hBU.trans hUH),map_subgroupOf_eq_of_le hUH] at hh
    · right
      intro b hb k hk
      exact congrArg Subtype.val (hc (show (⟨b,(hBU.trans hUH) hb⟩ : H) ∈ B.subgroupOf H from hb)
        ⟨k,hCH hk⟩ hk)
  rcases hmodels with hlin | halt
  · obtain ⟨q⟩ := hlin
    have hcard : Nat.card (K ⧸ pCore 2 K) = 168 := by
      rw [Nat.card_congr (aq.trans q).toEquiv,
        Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
      norm_num
    rcases Nonsolvable.linear_reduced_component_minimal_or_double S K W hSQ hred hK
        hqK hcard hsup hgenK hmoveW hneW with hmin | ⟨qK,e,he⟩
    · exact Or.inl (chosen hmin)
    · let w : W ≃* U := subgroupOfEquivOfLe hUH
      refine Or.inr ⟨aq.symm.trans qK,w.symm.trans e,?_⟩
      dsimp only
      intro c v
      exact he (a.symm c) (w.symm v)
  · obtain ⟨q⟩ := halt
    exact Or.inl (chosen (Nonsolvable.full_six_reduced_component_minimal S K W hSQ hred
      hK hqK (aq.trans q) hgenK hmoveW hneW))

/-- A four-element central seed and an orbit of at least sixteen elements
exclude every chosen module in the remaining component catalogue. -/
theorem not_chosen_of_seed
    {L : Subgroup G} (h₀ : Hypothesis1331 T L)
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hf : C ∈ MainForward.faithfulLocalComponents T)
    (hstar : C ∈ Chapter1.LStar G T)
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hZU : omegaOneCenterAmbient (T : Subgroup G) ≤ U)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hcard : 16 ≤ Nat.card U)
    (hfix : U ⊓ centralizer (C : Set G) = ⊥)
    (hmodels : Nonempty ((C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6))) :
    ¬ Nonempty (ChosenModule T C U) := by
  rintro ⟨DU⟩
  have hqC := Nonsolvable.component_quotient_quasisimple h1332 hf
  have hC12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T C).mp hf |>.2⟩ hqC
  have hmod := modules C _ hC12 DU
  rcases hmodels with hlin | halt
  · obtain ⟨q⟩ := hlin
    obtain ⟨_,e,_⟩ := Nonsolvable.linear_three_natural_coordinates DU q hfix hmod
    have hc : Nat.card U = 8 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card BinaryLinearThree.Vector = 8
      simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    omega
  · obtain ⟨q⟩ := halt
    obtain ⟨q,e,he⟩ := Nonsolvable.ordinary_six_natural_coordinates DU q hfix hmod
    let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
    obtain ⟨S,_,hb⟩ := omega_card_le_fixed T C U hTC DU.normalizes hZU f
      (q.surjective.comp (QuotientGroup.mk'_surjective _))
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) e he
    have hh := BinaryPermutation.six_natural_sylow_fixed_card_le_two S
    rw [hZcard] at hb
    omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- Select the doubled-natural configuration in the original second join,
including the precise action map and order of the whole omega span. -/
theorem exists_original_plane_second_doubled
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let P := firstFlagNormalizer T L V
    let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
    let U := conjugateSpanBy Z Y
    ∃ K : Subgroup Y, K.IsCComponent ∧ K.Normal ∧
      K.map Y.subtype ∈ MainForward.faithfulLocalComponents T ∧
      K.map Y.subtype ∈ Chapter1.LStar G T ∧
      (T : Subgroup G) ≤ normalizer (K.map Y.subtype : Set G) ∧
      ⁅U,K.map Y.subtype⁆ ≠ ⊥ ∧
      (∃ q : ((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) ≃*
          BinaryLinearThree.Group,
        ∃ e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector),
          ∀ (k : K.map Y.subtype) (v : U),
            (e (U.normalizerMonoidHom ⟨k.val,
              (map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z Y) k.property⟩ v)).toAdd =
              (BinaryLinearThree.W.prod BinaryLinearThree.W)
                (q (QuotientGroup.mk' (pCore 2 (K.map Y.subtype)) k)) (e v).toAdd) ∧
      K ⊓ centralizer (U.subgroupOf Y : Set Y) = K.pCoreIn 2 ∧
      pResidual 2 Y = K ∧ Y = K.map Y.subtype ⊔ (T : Subgroup G) ∧
      (pResidual 2 P).map P.subtype ≤ K.map Y.subtype ∧
      Y₂ ≤ K.map Y.subtype ∧
      ⁅K.map Y.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K.map Y.subtype ∧
      ⁅U,K.map Y.subtype⁆ = U ∧ Nat.card U = 64 ∧
      U ⊓ centralizer (K.map Y.subtype : Set G) = ⊥ := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
  let U := conjugateSpanBy Z Y
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right.trans le_sup_right
  have hUY : U ≤ Y := conjugateSpanBy_le (fun z hz =>
    hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  obtain ⟨K,hK,hn,hf,hstar,hTK,hm,hmodels,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩ :=
    exists_original_plane_second_models h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM
      h1332 fixed covered h13316
  let C := K.map Y.subtype
  have hY : Y = C ⊔ (T : Subgroup G) := hgen
  have hred := (original_plane_second_amalgam h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane).2.2.2.2.2.2.2.2.1
  have hred' : IsPReduced 2 (U.subgroupOf (C ⊔ (T : Subgroup G))) := by
    rw [←hY]
    exact hred
  have hUH : U ≤ C ⊔ (T : Subgroup G) := hUY.trans_eq hY
  have hneU : U ≠ ⊥ := by
    intro he
    change 16 ≤ Nat.card U at hcard
    rw [he,Nat.card_unique] at hcard
    omega
  have hqC := Nonsolvable.component_quotient_quasisimple h1332 hf
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hf.1
  have hZcard := (original_pair_source_seed h structural D m hTA hTB eA eB hne
    hindexL hindexA hindexB hcentral).2.2.1
  have hnot := SecondGeneration.not_chosen_of_seed h₀ h1332 modules hf hstar hTK
    (le_conjugateSpanBy Z Y) hZcard hcard hfix hmodels
  obtain ⟨q,e,he⟩ := (SecondGeneration.chosen_or_double hTK hUH hred' hf.1.1
    hqC hSQ hJ hmove hneU hmodels).resolve_left hnot
  have h64 : Nat.card U = 64 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (BinaryLinearThree.Vector × BinaryLinearThree.Vector) = 64
    simp [BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  exact ⟨K,hK,hn,hf,hstar,hTK,hm,⟨q,e,he⟩,hker,hr,hgen,hP,hY₂,hJ,hmove,h64,hfix⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
