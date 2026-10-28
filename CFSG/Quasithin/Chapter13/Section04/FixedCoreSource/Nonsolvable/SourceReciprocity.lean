module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedReciprocity
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ProductMixed

/-!
# Source assembly of mixed reciprocity

Select and recognize a component of the original nonsolvable escaping
centralizer. Its geometry gives the ordinary A₆ quotient for L, the full
central seed in V, and the actual pair H₂,L₂T. The established pair theorem
supplies both literal centralizer intersections, relative normality and
cubic residual identities, and the chief-count premise of plane amalgam
13.4.7. Applying its product or linear alternative now proves 13.4.15 in
both cases, for the same pair and original conjugator.

The linear alternative also supplies reciprocal commutation for 13.4.16.
In the product alternative, a nontrivial reciprocal commutator returns the
conjugator to M, centralizes V, and equals the original fixed line. The
remaining weak-closure exclusion and both vertex types of the coset graph
remain with this source proof, followed by the terminal offender argument.

Only nonsolvability at this chosen point is used here. Universal escaping
nonsolvability and existence remain essential to the separate uniqueness
and rank theorem; they are not inferred here. All genuine earlier-source
inputs, the separate general pair amalgam needed for uniqueness, and the
independent LargeDistanceInput retain their existing producers.
Source: Aschbacher–Smith 13.4.15 and the first paragraph of13.4.16,
printed pp.912–913, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Construct the original source pair and prove mixed reciprocity in both
amalgam alternatives. Product reciprocity retains its exact remaining case. -/
theorem escaping_original_mixed_reciprocity
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (¬ K ≤ normalizer (L : Set G)) ∧
      (Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) ∧
      ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
        Module.finrank (ZMod 2) W = 2 ∧
        (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
        ∃ P : Subgroup G,
          P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
          P ⋖ centralizer ({z.val} : Set G) ∧
          Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
          let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
          let X := P ⊔ B
          let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
          Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
          X ∈ Chapter1.HOver G (T : Set G) ∧
          X ⊓ normalizer (L : Set G) = B ∧
          X ⊓ centralizer ({z.val} : Set G) = P ∧
          (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
            ⁅V,U.conjBy g⁆ = ⊥) ∧
          ((⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
              ((pResidual 2 P).map P.subtype).pCoreIn 2 ∧
            m.weight z = 4 ∧ ⁅U,B.pCoreIn 2⁆ ≤ V ⊓ centralizer (L : Set G) ∧
            (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
              ⁅U,U.conjBy g⁆ ≠ ⊥ →
              g ∈ normalizer (L : Set G) ∧ ⁅V,U⁆ = ⊥ ∧
                ⁅U,U.conjBy g⁆ = V ⊓ centralizer (L : Set G))) ∨
            (Solvable.LinearAmalgamConclusion T X ∧
              (∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → U ≤ (B.pCoreIn 2).conjBy g →
                ⁅U,U.conjBy g⁆ = ⊥))) := by
  have hzL : z.val ∉ centralizer (L : Set G) := by
    intro hz
    exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hz⟩
      (fun he => hz1 (Subtype.ext he))).le
  obtain ⟨K,hK,hfK,_,hHN,_,hKM,_⟩ := exists_escaping_component h₀ h structural m
    h1332 h1338 hzT (fun he => hz1 (Subtype.ext he)) hzout hnonsolv
  have model := selected_component_ordinary_or_linear hl h₀ h structural D m h1332
    fixed five covered h13316 hindex z hzT hzL hK hHN hKM hfK
  have hgeom : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ≤ V := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · obtain ⟨_,_,hL,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry
        hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
      exact ⟨hL,hZ.le.trans inf_le_left⟩
    · obtain ⟨_,_,_,hL,_,_,hZ,_⟩ := ordinary_six_component_geometry
        h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
      exact ⟨hL,hZ.le.trans inf_le_left⟩
  obtain ⟨⟨eL⟩,hZV⟩ := hgeom
  obtain ⟨W,hW,hTW,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,hfixed,hcentral⟩ :=
    small_component_original_pair hl h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK model
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hTW
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hout : ¬ X ≤ normalizer (L : Set G) := fun hx => hP.1.2 (le_sup_left.trans hx)
  have hBlocal : B ∈ Chapter1.HOver G (T : Set G) := by
    have hVB : V ≤ B.pCoreIn 2 := by
      let := D.elementary
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
        (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module h structural D m))
    refine ⟨?_,hTB⟩
    intro he
    have hv : V = ⊥ := bot_unique (he ▸ hVB)
    have hc := m.card_module
    rw [hv,card_bot] at hc
    omega
  have hcentral' :
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂) := by
    dsimp only
    intro hx
    obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral X hx.1 le_sup_left le_sup_right
    exact ⟨h₁,h₂,Or.inl hr⟩
  have hfixedB : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (L : Set G) := by
    rw [←Amalgam.omega_fixed_twoResidual B hTB]
    exact hfixed
  have hc := h1347 W hW hTW P hP.1.1 hBlocal ⟨eP⟩ ⟨eB⟩ hne
    (Solvable.original_second_flag_residual_eq_inner D m W hTW)
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB hcentral'
  obtain ⟨hXM,hXH,_⟩ := hcentral X hlocal.1 le_sup_left le_sup_right
  refine ⟨K,hK,hfK,hHN,hKM,model,W,hW,hTW,P,hP,hPH,⟨eP⟩,⟨eB⟩,hlocal,hXM,hXH,?_⟩
  rcases hc.2 with hc | hc
  · refine ⟨original_product_pair_mixed_commute h₀ D m h structural hindex P B
      hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc hBM hfixedB hfusion,Or.inl ⟨hc,?_,?_,?_⟩⟩
    · exact original_product_weight_four h structural D m W hW hTW P hP z hzL hPH.le hc
    · rw [←hfixedB]
      exact original_product_radical_movement h₀ D m h structural hindex P B
        hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc
    · exact original_product_pair_reciprocal_reduction h₀ D m h structural hindex P B
        hP.1.1.2 hTB hout eP eB hne hiP hiB hcentral' hc hBM hfixedB hfusion
  · refine ⟨?_,Or.inr ⟨hc,?_⟩⟩
    · exact original_linear_pair_mixed_commute hl h₀ h structural modules D m
        hP.1.1.2 hTB eP eB hne hout hindex hiP hiB (hcentral' hlocal).2.2
        h1332 fixed five covered h13316 h1338 hc eL hM hZV W hW hTW rfl
        hfusion z hzT hzL hPH.le hnonsolv
    · obtain ⟨_,_,_,hr⟩ := original_linear_pair_module_nonFF h₀ h structural D m
        hP.1.1.2 hTB eP eB hne hout hindex hiP hiB (hcentral' hlocal).2.2 h1332 hc
      intro g h₁ h₂
      have hR : B.pCoreIn 2 ≤ X := (pCoreIn_le 2 B).trans le_sup_right
      exact hr g (h₁.trans hR) (h₂.trans (map_mono hR))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
