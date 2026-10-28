module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSixGeometryAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SelectedOutside

/-!
# The normalizer supplement in the guarded selected-six branch

The actual selected module and full omega center make the original
normalizer residual fix a nonzero point of the selected component. Apply
13.3.8 at that component with outside overgroup N_G(L). Its {2,3}-image
bound and the original ordinary action kernel make the residual a two-group;
two-perfectness then makes it trivial. Thus N_G(L)=LT, and N_G(V)=LT too.

The original-module application constructs both module markings, the omega
index and the original ordinary quotient. A nonzero selected fixed space
also constructs the ordinary selected quotient, excluding the cover. This
connects the guarded 13.4.10 component geometry to the normalizer premise
of recognition without an outside-action or normalizer callback. The
other selected rows and final ambient recognition still require assembly.
Source: Aschbacher--Smith 13.3.8, 13.4.6(4), 13.4.10(7),
printed pp.886--887,898,909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The selected ordinary-six geometry kills the literal original normalizer
residual and proves its supplement, using only structural facts at G,T. -/
theorem six_component_normalizer_supplement_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
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
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizerActionResidual L V = ⊥ ∧
      normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      normalizer (V : Set G) = L ⊔ (T : Subgroup G) := by
  obtain ⟨DK,⟨mark⟩,_,⟨eL⟩,_,_,hZ,_⟩ := ordinary_six_component_geometry_at
    h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  have hu := h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have huK := hK12.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  let M := normalizer (L : Set G)
  let R := normalizerActionResidual L V
  have hRM : R ≤ M := (map_subtype_le _).trans inf_le_left
  obtain ⟨hM,hnR,hRC,hpR,hRz⟩ := normalizer_action_residual_at h structural D m
  have hRN : R ≤ normalizer (K : Set G) := (hRz z.val z.property).trans hHN
  have houtside : M ∈ Chapter1.HOutside G (T : Set G)
      (normalizer (K : Set G) : Set G) := by
    refine ⟨⟨Chapter1.mem_H_of_isTwoLocal hu.1.1,D.sylow_normalizes_component⟩,?_⟩
    intro hMN
    have he := hu.2 _ huK.1 (sup_le (L.le_normalizer.trans hMN) (h1332 K hfK).1)
    exact hKM (K.le_normalizer.trans he.le)
  have h23 := selected_six_outside_twoThree_at hK12 structural DK mark eK
    houtside hRM hnR hpR hRN (hRC.trans (centralizer_le (hZ.le.trans inf_le_left)))
  have hR : R ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G) := map_subtype_le _
  have h3 : ¬ 3 ∣ Nat.card R := by
    intro hd
    exact ordinary_normalizer_kernel_three_free_at h structural D m eL
      (hd.trans (card_dvd_of_le hR))
  have hid := hpR.hom_eq_one_of_isPGroup (isPGroup_two_of_isPiGroup_twoThree h23 h3)
    (MonoidHom.id R)
  have hb : normalizerActionResidual L V = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact mem_bot.mpr (congrArg (fun a : R => a.val)
      (DFunLike.congr_fun hid ⟨x,hx⟩))
  have hs : normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
    simpa only [hb,sup_bot_eq] using hM
  exact ⟨⟨eL⟩,hb,hs,(normalizer_component_eq_module_at h structural D m).symm.trans hs⟩

/-- Source application on the original five-dimensional fixed module: the
selected ordinary quotient, or a selected fixed vector, yields both literal
normalizer equalities with the normalizer residual trivial. -/
theorem original_six_component_normalizers_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hrow : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
      (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
        Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizerActionResidual L V = ⊥ ∧
      normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      normalizer (V : Set G) = L ⊔ (T : Subgroup G) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  have heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
    rcases hrow with heK | hfixedK
    · exact heK
    · exact ordinary_component_of_source_fixed_at h₀ h structural D m h1332 fixed
        hindex z hzT hzL hK hHN hKM hfK hfixedK
  obtain ⟨eK⟩ := heK
  exact six_component_normalizer_supplement_at h₀ h structural modules D m h1332
    fixed hindex z hzT hzL hK hHN hKM hfK eK

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
