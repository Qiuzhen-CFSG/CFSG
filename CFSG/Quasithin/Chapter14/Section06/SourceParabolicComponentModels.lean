module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCentralPoint
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualSymplectic
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThreeResidual
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Paired
public import Theory.GroupTheory.GeneralizedFitting.Solvable

/-!
# The surviving component models in the original parabolic branch

The central involution from 14.6.7 survives the actual solvable parabolic
core. Its cyclic line is normal in the chosen Sylow and is centralized by
the marked maximal subgroup. Thus it supplies the residual-centralization
inputs to the E.2.17 symplectic and degree-three restrictions. For a normal
source component, the symplectic field cannot exceed two, and a positive
degree-three field exponent is one. For an exchanged component, the paired
catalogue and Bender exclusion leave only odd linear-two groups. Thus only
the odd-characteristic, binary linear-three, and binary derived symplectic
rows remain. The final source consumer constructs the marked parabolic and
generating component from the original IMin choice.

Source: Aschbacher--Smith 14.6.9, printed pp.1027--1028, using E.2.17.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

section Marked
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hmax : ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I)
    (hF : generalizedFitting I ≠ pCore 2 I)

include hG hempty hM hunique hmany hcard e hab H hH hu hI hS hmax hF

private theorem source_parabolic_residual_line :
    ¬ Group.IsSolvable I ∧ ∃ V : Subgroup I,
      IsElementaryAbelian 2 V ∧ V ≤ (S : Subgroup I) ∧
      (V.subgroupOf (S : Subgroup I)).Normal ∧
      ¬ V ≤ ChapterB.minimalParabolicCore S hP ∧
      (pResidual 2 (ChapterB.minimalParabolicMax S hP)).map
        (ChapterB.minimalParabolicMax S hP).subtype ≤ centralizer (V : Set I) := by
  obtain ⟨z,hz,hzS,hzJ,hcentral⟩ := source_parabolic_central_point hG T hempty hM
    hunique hmany hcard e hab H hH u hu I hI S hS hP hmax hF
  have hodd := (source_lemma_14_6_7_initial hG T hempty hM hunique hmany
    hcard e hab H hH u hu I hI S hS).2.2
  have hs : ¬ Group.IsSolvable I := by
    intro hs
    let := hs
    apply hF
    rw [generalizedFitting_eq_fitting_of_solvable I, Fitting_eq_pcore I 2 hodd]
  let V := zpowers z
  let hV : IsElementaryAbelian 2 V := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hz ▸ pow_orderOf_eq_one z)
  have hVT : V ≤ (S : Subgroup I) := zpowers_le.mpr hzS
  have hMC : ChapterB.minimalParabolicMax S hP ≤ centralizer (V : Set I) := by
    simpa only [V,zpowers_eq_closure,centralizer_closure] using hcentral
  have hVN : (V.subgroupOf (S : Subgroup I)).Normal :=
    normal_subgroupOf_of_le_normalizer (((ChapterB.minimalParabolicMax_spec S hP).2.trans hMC).trans
      (Subgroup.centralizer_le_normalizer _))
  exact ⟨hs,V,hV,hVT,hVN,(fun hv => hzJ (hv (mem_zpowers z))),
    (map_subtype_le _).trans hMC⟩

/-- The source marked central line excludes every nonbinary symplectic image
of a normal generating C-component. -/
theorem source_parabolic_nonbinary_symplectic_exclusion
    (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup I) = ⊤) {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))) 2 (2^n)) : False := by
  obtain ⟨hs,V,hV,hVT,hVN,hout,hres⟩ := source_parabolic_residual_line hG T hempty hM
    hunique hmany hcard e hab H hH u hu I hI S hS hP hmax hF
  let := hV
  exact ChapterE.Witnesses.source_not_nonbinary_symplectic_of_residual_centralizes
    S hP hs K hK hgen hn hm V hVT hVN hout hres

/-- The positive degree-three field exponent of a normal generating source
component is one. All central-line premises are discharged at the source. -/
theorem source_parabolic_linear_three_parameter_eq_one
    (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup I) = ⊤) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))) 3 (2^n)) : n = 1 := by
  obtain ⟨hs,V,hV,hVT,hVN,hout,hres⟩ := source_parabolic_residual_line hG T hempty hM
    hunique hmany hcard e hab H hH u hu I hI S hS hP hmax hF
  let := hV
  exact ChapterE.Witnesses.source_linear_three_parameter_eq_one_of_residual_centralizes
    S hP hs K hK hgen hn hm V hVT hVN hout hres

/-- The source star image is odd-characteristic, binary linear-three, or
binary derived symplectic. The exchanged case is handled by its actual paired
catalogue, and the normal case by the same surviving central line. -/
theorem source_parabolic_component_models
    (K : Subgroup I) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup I) = ⊤) :
    let D := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))
    ChapterA.Section02.IsTheoremCOddModel D ∨ ClassicalGroup.IsPSL D 3 2 ∨
      Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  have hs := (source_parabolic_residual_line hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI S hS hP hmax hF).1
  have hsq := Chapter3.sqtk_of_mem_H hG hI.1
  have hnB := source_parabolic_bender_exclusion hG T hempty hM hunique hmany hcard e hab
    H hH u hu I hI S hS hP hmax hF K hK hgen
  by_cases hn : K.Normal
  · let := hn
    rcases ChapterE.Structure.source_component_classical_star_models
      ChapterA.Section02.theoremA_knownSimple (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      hsq S hP hs K hK hgen with hm | hm | ⟨f,hf,hm⟩ | ⟨f,hf,hm⟩ | hm
    · exact Or.inl hm
    · exact (hnB hm).elim
    · have he := source_parabolic_linear_three_parameter_eq_one hG T hempty hM hunique
        hmany hcard e hab H hH u hu I hI S hS hP hmax hF K hK hgen (by omega) hm
      exact Or.inr (Or.inl (by simpa only [he,pow_one] using hm))
    · exact (source_parabolic_nonbinary_symplectic_exclusion hG T hempty hM hunique hmany
        hcard e hab H hH u hu I hI S hS hP hmax hF K hK hgen (by omega) hm).elim
    · exact Or.inr (Or.inr hm)
  · rcases ChapterE.Structure.source_original_paired_models
      ChapterA.Section02.theoremA_knownSimple (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      hsq S hP hs K hK hgen hn with ⟨f,hf,hm⟩ | ⟨m,hm,he⟩ | ⟨p,hp,ho,hm⟩
    · exact (hnB (.linear f hf hm)).elim
    · exact (hnB (.suzuki m hm he)).elim
    · exact Or.inl (.linear_two p 1 hp ho (by omega) (by simpa only [pow_one] using hm))

end Marked

open scoped Pointwise

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


/-- The original non-characteristic-two IMin branch has either the two
factorizations or a constructed generating component with only the odd,
binary linear-three and binary symplectic source rows remaining. -/
theorem source_noncharacteristic_component_models_or_factorization
    (I : Subgroup G) (hF : generalizedFitting I ≠ pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I ∧
      ∃ hP : ChapterB.IsMinimalParabolicOver S ⊤,
      ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I ∧
      ∃ K : Subgroup I, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        K ⊔ (S : Subgroup I) = ⊤ ∧
        IsComponent (I ⧸ pCore 2 I) (K.map (QuotientGroup.mk' (pCore 2 I))) ∧
        (let D := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hP))
         ChapterA.Section02.IsTheoremCOddModel D ∨ ClassicalGroup.IsPSL D 3 2 ∨
           Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))) ∨
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_noncharacteristic_component_or_factorization hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hF hI with
    ⟨S,hS,hP,hmax,K,hK,hquasi,hgen,himage,_⟩ | hf
  · exact Or.inl ⟨S,hS,hP,hmax,K,hK,hquasi,hgen,himage,
      source_parabolic_component_models hG T hempty hM hunique hmany hcard e hab
        H hH u hu I hI.1.1 S hS hP hmax hF K hK hgen⟩
  · exact Or.inr hf

end CFSG.Quasithin.Chapter14.Section06
