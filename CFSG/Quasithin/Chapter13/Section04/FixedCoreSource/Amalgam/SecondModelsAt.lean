module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondModels
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGenerationAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CoveredSelection

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# The two remaining quotients of the actual second component

The exact action kernel on the second omega span is also the kernel on
R₂(Y). Since Y=K_Y T, a cubic-center detector in that reduced module
constructs a genuine chosen constituent. The fixed and fixed-free clauses
of original 13.3.2 exclude the triple-cover quotient. Original 13.3.16
excludes the unitary quotient. Thus the same component has an actual
SL₃(2) or A₆ quotient, retaining both original vertex residuals, the full
omega span, Thompson movement and both action-kernel identifications.

The earlier source premises remain explicit for the fixed-core assembly.
No model selection or chosen-constituent witness is supplied by the caller.
Source: Aschbacher--Smith 13.4.5(4), 13.4.7(3), printed pp.898,903.
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

theorem exists_original_plane_second_models_at
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
      (Nonempty (((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) ≃*
        BinaryLinearThree.Group) ∨
        Nonempty (((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) ≃*
          alternatingGroup (Fin 6))) ∧
      K ⊓ centralizer (U.subgroupOf Y : Set Y) = K.pCoreIn 2 ∧
      pResidual 2 Y = K ∧ Y = K.map Y.subtype ⊔ (T : Subgroup G) ∧
      (pResidual 2 P).map P.subtype ≤ K.map Y.subtype ∧
      Y₂ ≤ K.map Y.subtype ∧
      ⁅K.map Y.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K.map Y.subtype ∧
      ⁅U,K.map Y.subtype⁆ = U ∧ 16 ≤ Nat.card U ∧
      U ⊓ centralizer (K.map Y.subtype : Set G) = ⊥ := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Y := P ⊔ (Y₂ ⊔ (T : Subgroup G))
  let U := conjugateSpanBy Z Y
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right.trans le_sup_right
  obtain ⟨K,hK,hn,hf,hstar,hTK,hm,hmodels,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩ :=
    exists_original_plane_second_generation_at h₀ h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral hs hcomm Wplane hWplane hTplane hBplane hM h1332
  refine ⟨K,hK,hn,hf,hstar,hTK,hm,?_,hker,hr,hgen,hP,hY₂,hJ,hmove,hcard,hfix⟩
  rcases hmodels with hl | ha | hc | hu
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hl
    let := Fintype.ofFinite F
    let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    exact Or.inl ⟨(e.trans (Atlas.fieldEquivPSL 3 a)).trans
      Matrix.PSL3Two.equiv.symm⟩
  · exact Or.inr ha
  · have hUY : U ≤ Y := conjugateSpanBy_le (fun z hz =>
      hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
    have hkG := congrArg (Subgroup.map Y.subtype) hker
    rw [←map_inf_centralizer_of_injective Y.subtype Y.subtype_injective,
      map_subgroupOf_eq_of_le hUY,map_pCoreIn_of_injective 2 _ _ Y.subtype_injective] at hkG
    have hnG : ((K.map Y.subtype).subgroupOf Y).Normal := by
      have hh : (K.map Y.subtype).subgroupOf Y = K :=
        comap_map_eq_self_of_injective Y.subtype_injective K
      exact hh.symm ▸ hn
    have hred := (original_plane_second_amalgam_at h₀ h structural D m
      hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
      Wplane hWplane hTplane hBplane).2.2.2.2.2.2.2.2.1
    have hkR := SecondGeneration.reduced_kernel (map_subtype_le K) hUY hnG hred hkG
    let C := K.map Y.subtype
    change (centralizer ((ReducedModule Y).map Y.subtype : Set G)).subgroupOf C = pCore 2 C at hkR
    have hY : Y = C ⊔ (T : Subgroup G) := hgen
    rw [hY] at hkR
    exact (SecondGeneration.not_covered_of_reduced_kernel h₀ hf hTK fixed covered hkR hc).elim
  · exact (Nonsolvable.selected_unitary_excluded h₀ h13316 hf hu).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
