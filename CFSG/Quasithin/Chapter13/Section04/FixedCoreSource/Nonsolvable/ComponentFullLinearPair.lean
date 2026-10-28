module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixQuotient
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullLinear
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalPlaneExistence
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLines

/-!
# The original pair for a linear-three centralizer

The full centralizer quotient and its two-parabolic lattice give the actual
outside parabolic. Its action on the original central four-group excludes
a normal Sylow subgroup, identifying its quotient as S₃. Combine it with
the original invariant plane to verify the chief-factor, fixed-line and
relative residual-centralizer premises of 13.4.7.

The full five-dimensional marking and the literal L/centralCore L map
are retained. Earlier Chapter12/13.3 inputs, M=LT and LargeDistanceInput
remain explicit with their existing producers. This discharges the linear
row's applicability premises, not the remaining module-weight or graph
arguments. Source: Aschbacher–Smith 13.4.10(8), printed pp.909–910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem coatom_of_cover {P H : Subgroup G} (h : P ⋖ H) :
    IsCoatom (P.subgroupOf H) := by
  have hm : (P.subgroupOf H).map H.subtype = P := map_subgroupOf_eq_of_le h.le
  have ht : (⊤ : Subgroup H).map H.subtype = H := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  refine ⟨?_,?_⟩
  · intro he
    exact h.ne (hm.symm.trans ((congrArg (map H.subtype) he).trans ht))
  · intro Y hY
    have hPY : P ≤ Y.map H.subtype := hm ▸ map_mono hY.le
    have he : Y.map H.subtype = H := (h.eq_or_eq hPY (map_subtype_le Y)).resolve_left (by
      intro he
      exact hY.ne ((map_injective H.subtype_injective) (hm.trans he.symm)))
    exact (map_injective H.subtype_injective) (he.trans ht.symm)

variable {T : Sylow 2 G} {L K V : Subgroup G}

/-- Construct the original H₂,L₂T pair in the linear-three branch and
verify the local join and literal applicability clauses of 13.4.7. -/
theorem linear_original_pair
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ centralizer ({z.val} : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        let Z := omegaOneCenterAmbient (T : Subgroup G)
        let K₂ := (pResidual 2 P).map P.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
        B = L₂ ⊔ (T : Subgroup G) ∧ X ∈ Chapter1.HOver G (T : Set G) ∧
        L₂ ≤ L ∧
        (∀ s : NoncentralChiefRefinement.ChiefSeries L₂,
          s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount) ∧
        (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 ∧
        (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 ∧
        Z ⊓ centralizer (L₂ : Set G) = V ⊓ centralizer (L : Set G) ∧
        (∀ Y : Subgroup G, Y ∈ Chapter1.H G → P ≤ Y → B ≤ Y →
          let C₁ := Y ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
          let C₂ := Y ⊓ centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G)
          Y ⊓ normalizer (L : Set G) = B ∧
          Y ⊓ centralizer ({z.val} : Set G) = P ∧
          C₁ = P ∧ C₂ = B ∧ (K₂.subgroupOf C₁).Normal ∧ (L₂.subgroupOf C₂).Normal ∧
          (primeToResidual 3 C₁).map C₁.subtype = K₂) := by
  obtain ⟨W,hW,hT⟩ := Solvable.exists_original_invariant_plane h structural D m
  obtain ⟨P,hP,hPH,_,_,_,_,_⟩ := linear_full_centralizer_parabolic
    hl h₀ h structural modules D m h1332 fixed hindex hM z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨_,_,⟨eL⟩,_,_,_,_,_,_,hZ,hcard,_⟩ := linear_component_geometry
    hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨_,_,_,hq⟩ := linear_full_centralizer
    hl h₀ h structural modules D m h1332 fixed hindex hM z hzT hzL hKz hHN hKM hfK eK
  have model : Nonempty ((centralizer ({z.val} : Set G) ⧸
      pCore 2 (centralizer ({z.val} : Set G))) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
      pCore 2 (centralizer ({z.val} : Set G))) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
      pCore 2 (centralizer ({z.val} : Set G))) ≃* Equiv.Perm (Fin 6)) := Or.inl hq
  have hTP' : (T : Subgroup G) < P := lt_of_le_of_ne hP.1.1.2 (by
    intro he
    exact hP.1.2 (he ▸ D.sylow_normalizes_component))
  have hcover := small_quotient_parabolic_maximal _ P hTP' hPH model
  have hidxP := small_quotient_parabolic_index _ P hTP' hPH model
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hresidxP := escaping_residual_fixed_index h structural m z
    (fun he => hz1 (congrArg Subtype.val he)) hzT P hP hPH.le
  rw [←hZ] at hresidxP
  obtain ⟨eP⟩ := parabolic_quotient_of_four_fixed_line T P hTP'.le z.val hzT hz1
    hPH.le hcard hidxP hresidxP
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let K₂ := (pResidual 2 P).map P.subtype
  let L₂ := (pResidual 2 B).map B.subtype
  have hTP := hP.1.1.2
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  obtain ⟨⟨eB⟩,hL₂,_,hchief⟩ := Solvable.original_second_flag_chief_factors D m eL W hW hT
  have hB : B = L₂ ⊔ (T : Subgroup G) := le_antisymm
    (le_embedded_pResidual_sup_sylow_of_normalizes T B (hTB.trans B.le_normalizer))
    (sup_le (map_subtype_le _) hTB)
  have hZV : Z ≤ V := hZ.le.trans inf_le_left
  have hfixedV := Solvable.original_second_flag_fixed D m W hW hT
  have hfixedZ : Z ⊓ centralizer (L₂ : Set G) = Z ⊓ centralizer (L : Set G) := by
    rw [←inf_eq_left.mpr hZV,inf_assoc,hfixedV,←inf_assoc,inf_eq_left.mpr hZV]
  have hfixedB : Z ⊓ centralizer (B : Set G) = Z ⊓ centralizer (L : Set G) := by
    rw [←Amalgam.omega_fixed_twoResidual B hTB]
    exact hfixedZ
  have hiP : (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 := by
    rw [Amalgam.omega_fixed_twoResidual P hTP] at hresidxP
    exact hresidxP
  have hiB : (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 := by
    rw [hfixedB]
    exact hindex
  have hlocal := Amalgam.original_pair_local D m hTP hTB eP eB hne hiP hiB
  have hZL : Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) :=
    le_antisymm (le_inf (inf_le_left.trans hZV) inf_le_right)
      (le_inf (Solvable.fixed_le_original_omegaCenter h structural D m) inf_le_right)
  have hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [inf_comm,hM]
    exact (ordinary_augmentation_point_parabolic D m eL z hzT hzL).symm
  have hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G) := by
    rw [hinter,hM]
    exact (Solvable.original_inside_parabolics_generate h structural D m eL z hzT hzL
      hinter W hW hT).2
  have hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))) := by
    rw [hM]
    exact Solvable.original_second_flag_coatom D m W hW hT
  have hcentral : centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G) =
      normalizer (L : Set G) := by
    rw [hfixedZ,hZL]
    exact fixed_centralizer_eq_normalizer h structural D m
  refine ⟨W,hW,hT,P,hP,hcover,⟨eP⟩,⟨eB⟩,hB,hlocal,hL₂,hchief,hiP,hiB,
    hfixedZ.trans hZL,?_⟩
  intro Y hY hPY hBY
  exact Solvable.amalgam_residual_centralizers h structural z.val hzT P B Y
    hTP hcover.le (coatom_of_cover hcover) hP.1.2 eP hBM hBmax hgen hcentral hY hPY hBY

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
