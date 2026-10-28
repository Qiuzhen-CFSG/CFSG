module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLines

/-!
# The original selected-six pair with guarded earlier inputs

Construct the marked invariant plane and the unique outside parabolic of
C_G(z). Their join is local, their full omega-center fixed subgroups have
index two, and the literal second residual has at least three noncentral
binary chief factors. In each local overgroup, maximality of the original
parabolics identifies their relative fixed-subgroup centralizers, proves
relative normality, and identifies the prime-to-three residual.

Thus all applicability clauses of 13.4.7 hold on the actual H₂,L₂T pair in
the ordinary selected-six branch, using structural facts only at G,T. The
normalizer supplement, full centralizer and plane are constructed here;
the original five-dimensional module and all quotient maps are retained.
The 13.4.7 alternatives and remaining rows still require guarded assembly.
The earlier Chapter 12/13.3 producers retain their original obligations.
Source: Aschbacher--Smith 13.4.7 and 13.4.10(8), printed pp.899,909--910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
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

/-- Construct the original H₂,L₂T pair in the ordinary A₆ branch and
verify the local join and literal applicability clauses of 13.4.7. -/
theorem ordinary_six_original_pair_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
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
  have hM := (six_component_normalizer_supplement_at h₀ h structural modules D m h1332
    fixed hindex z hzT hzL hK hHN hKM hfK eK).2.2.1
  obtain ⟨W,hW,hT⟩ := exists_original_invariant_plane_at h structural D m
  obtain ⟨P,hP,hcover,_,_,_,hidxP,⟨eP⟩,hZ,_,hfixP,_,hresidxP,_⟩ :=
    ordinary_six_full_centralizer_parabolic_at h₀ h structural modules D m h1332 fixed
      hindex z hzT hzL hK hHN hKM hfK eK
  obtain ⟨_,_,_,⟨eL⟩,_,_,_,_,_,_⟩ := ordinary_six_component_geometry_at
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
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
      (le_inf (fixed_le_original_omegaCenter_at h structural D m) inf_le_right)
  have hinter : centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G) =
      Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G) := by
    rw [inf_comm,hM]
    exact (ordinary_augmentation_point_parabolic D m eL z hzT hzL).symm
  have hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G) := by
    rw [hinter,hM]
    exact (original_inside_parabolics_generate_at h structural D m eL z hzT hzL
      hinter W hW hT).2
  have hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))) := by
    rw [hM]
    exact Solvable.original_second_flag_coatom D m W hW hT
  have hcentral : centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G) =
      normalizer (L : Set G) := by
    rw [hfixedZ,hZL]
    exact fixed_centralizer_eq_normalizer_at h structural D m
  refine ⟨W,hW,hT,P,hP,hcover,⟨eP⟩,⟨eB⟩,hB,hlocal,hL₂,hchief,hiP,hiB,
    hfixedZ.trans hZL,?_⟩
  intro Y hY hPY hBY
  exact amalgam_residual_centralizers_at h structural z.val hzT P B Y
    hTP hcover.le (coatom_of_cover hcover) hP.1.2 eP hBM hBmax hgen hcentral hY hPY hBY


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
