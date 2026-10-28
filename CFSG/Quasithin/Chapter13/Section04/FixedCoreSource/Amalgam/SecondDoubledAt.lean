module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondDoubled
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondModelsAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSix
public import Theory.Representation.BinaryPermutation.SixNaturalSylowFixed
public import Theory.Representation.OmegaSeedFixedSpace

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

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
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- Select the doubled-natural configuration in the original second join,
including the precise action map and order of the whole omega span. -/
theorem exists_original_plane_second_doubled_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    exists_original_plane_second_models_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM
      h1332 fixed covered h13316
  let C := K.map Y.subtype
  have hY : Y = C ⊔ (T : Subgroup G) := hgen
  have hred := (original_plane_second_amalgam_at h₀ h structural D m
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
  have hZcard := (original_pair_source_seed_at h structural D m hTA hTB eA eB hne
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
