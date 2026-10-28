module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ChiefFactors
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.FullSeed

/-!
# The chief-factor and fixed-space clauses on the original amalgam

The original-R₁ local product selects the ordinary A₆ quotient. With the
actual inner second-parabolic marking, ChiefFactors constructs its A₄
residual quotient and proves three noncentral binary chief factors.
Adjoining the original Sylow gives the S₃ quotient and identifies the
literal O²(L₂T) with L₂. Together with FullSeed and OriginalAmalgam,
this supplies the two S₃ quotients, distinctness, both index-two clauses,
and the conditional relative-centralizer clauses of13.4.7(a–c), while
retaining the exclusion of the product alternative.

The Notation13.2.1 parabolic alignment remains explicit, with its source
connection retained by qt-d-1341-solvable-source. The earlier13.3.9 and
13.4.2–3 inputs,13.4.7 alternatives and final earlier-source discharge
remain with qt-d-1341-fixed-core-source. Structural1222 is genuinely
universal here; a local At instance cannot discharge it. H₀'s L₃(2)
quotient, the marked C₃ chamber and ambient fusion remain with
qt-d-1341-solvable-source.
The result does not assert H₀ is two-local before the amalgam theorem.
Source: Aschbacher–Smith13.4.7 and13.4.9, printed pp.899,906.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem original_R1_amalgam_conditions
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (J : Subgroup G) (hJL : J ≤ L)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      Theory.SpecificGroups.SymmetricSix.synthemeStabilizer ⊓ alternatingGroup (Fin 6))
    (L₂ : Subgroup G) (hL₂res : L₂ = (pResidual 2 J).map J.subtype)
    (hmax₂ : IsCoatom ((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))))
    (hgenerate : (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
      (L₂ ⊔ (T : Subgroup G)) = L ⊔ (T : Subgroup G))
    (hfixed₂ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L₂ : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G))
    (hsupp : normalizer (L : Set G) =
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G))) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let B := L₂ ⊔ (T : Subgroup G)
    let H₀ := P ⊔ B
    let K₁ := (pResidual 2 P).map P.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let C₁ := H₀ ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
    let C₂ := H₀ ⊓ centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G)
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      (pResidual 2 B).map B.subtype = L₂ ∧
      (∀ s : NoncentralChiefRefinement.ChiefSeries L₂,
        s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount) ∧
      (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 ∧
      (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 ∧ P ≠ B ∧
      normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      ¬ ⁅K₁,L₂⁆ ≤ K₁.pCoreIn 2 ∧
      (H₀ ∈ Chapter1.H G →
        H₀ ⊓ normalizer (L : Set G) = B ∧ H₀ ⊓ H = P ∧
        C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (L₂.subgroupOf C₂).Normal ∧
        (primeToResidual 3 C₁).map C₁.subtype = K₁) := by
  obtain ⟨⟨eL⟩,_,hP,_⟩ := original_R1_line_parabolics h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342
  have hL₂ : L₂ ≤ L := hL₂res ▸ (map_subtype_le _).trans hJL
  have hTL₂ : (T : Subgroup G) ≤ normalizer (L₂ : Set G) := by
    rw [hL₂res]
    exact hTJ.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J))
  have hres₂ : (pResidual 2 (L₂ ⊔ (T : Subgroup G) : Subgroup G)).map
      (L₂ ⊔ (T : Subgroup G)).subtype = L₂ :=
    embedded_pResidual_join_pGroup L₂ (T : Subgroup G)
      (hL₂res ▸ isPPerfect_embedded_pResidual 2 J) T.isPGroup' hTL₂
  have hB : L₂ ⊔ (T : Subgroup G) = J ⊔ (T : Subgroup G) := by
    rw [hL₂res]
    exact le_antisymm (sup_le_sup_right (map_subtype_le _) _)
      (sup_le (le_embedded_pResidual_sup_sylow_of_normalizes T J hTJ) le_sup_right)
  have hquot := second_parabolic_full_core_quotient D m eL J hJL hTJ himage
  rw [←hB] at hquot
  have hchief : ∀ s : NoncentralChiefRefinement.ChiefSeries L₂,
      s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount := by
    subst L₂
    exact second_parabolic_residual_three_chief_factors D m eL J hJL hTJ himage
  obtain ⟨_,_,_,_,hidxP⟩ := original_R1_full_seed
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  obtain ⟨_,_,_,_,_,hidxB,hne⟩ := original_R1_amalgam_fixed_data
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342 L₂ hfixed₂
  have hrest := original_solvable_amalgam_inputs h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 L₂ hL₂ hmax₂ hres₂ hgenerate hfixed₂ hsupp
  exact ⟨hP,hquot,hres₂,hchief,hidxP,hidxB,hne,hrest⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
