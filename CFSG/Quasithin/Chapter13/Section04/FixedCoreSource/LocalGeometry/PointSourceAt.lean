module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredPointAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryPointSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FixedModuleAt

/-!
# Original augmentation 13.3.9 from facts at G,T

For every outside overgroup H, a relatively normal two-perfect subgroup Y
centralizing a nonfixed point of V₁ is either trivial or the literal source
residual. The ordinary point action and index-three theorem give L₁; the
covered kernel and cubic-closure argument give L₁,+. Both alternatives
preserve the actual barred action on V.

The final application constructs the Hypothesis1223 guard and five-dimensional
marking from the original chosen module with nonzero fixed part. The retained
13.3.2 inputs still need their existing producers; this supplies 13.3.9 for
the original augmentation branch, not the entire 13.4.1 recognition theorem.
Source: Aschbacher--Smith 13.3.9, p.887, and its use in 13.4.4(2), p.897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V Y H : Subgroup G}

/-- The literal ordinary 13.3.9 clause at either nonfixed Sylow-central weight. -/
theorem ordinary_outside_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3) := by
  have hYL := ordinary_outside_le_component_at h structural D m eL
    H hH
    Y hYH hnY hp hYM
  let Cpoint := centralizer ({z.val} : Set G)
  let C := L ⊓ Cpoint
  have hYC : Y ≤ C := le_inf hYL hYz
  have hTH : (T : Subgroup G) ≤ Cpoint := original_sylow_le_centralizer hz
  have hnC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf D.sylow_normalizes_component (hTH.trans Cpoint.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let J := C ⊔ (T : Subgroup G)
  let A := C.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hnC)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal A
  let e := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hST : ∀ s ∈ (S : Subgroup C), s.val ∈ (T : Subgroup G) := by
    rintro s ⟨a,ha,rfl⟩
    rw [hP] at ha
    exact ha
  have hcore : IsPGroup 2 (centralCore L) := by
    rw [centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup
  obtain ⟨eC⟩ := component_centralizer_quotient D m hcore z hzL
  have hi : (S : Subgroup C).index = 3 := SymmetricThreeTwoCore.sylow_index_three eC S
  have hp' : IsPPerfect 2 (Y.subgroupOf C) := hp.of_surjective
    (subgroupOfEquivOfLe hYC).symm.toMonoidHom (subgroupOfEquivOfLe hYC).symm.surjective
  have hn : (S : Subgroup C) ≤ normalizer (Y.subgroupOf C : Set C) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hnY (hH.1.2 (hST s hs))) y.val
  rcases eq_bot_or_residual_of_index_three (S : Subgroup C) (Y.subgroupOf C)
    S.isPGroup' hi hp' hn with hb | hr
  · left
    have hh := congrArg (map C.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hYC,Subgroup.map_bot] using hh
  · have he : Y = firstCentralizerResidual L z.val := by
      have hh := congrArg (map C.subtype) hr
      rw [map_subgroupOf_eq_of_le hYC,
        twoResidual_eq_primeToResidual_three (component_centralizer_twoThree D m eL z hzL)] at hh
      exact hh.trans (firstCentralizerResidual_eq L z.val).symm
    right
    refine ⟨?_,?_⟩
    · simpa only [selectedFirstResidual,if_pos (show Nonempty ((L ⧸ pCore 2 L) ≃*
        alternatingGroup (Fin 6)) from ⟨eL⟩)] using he
    · rw [he]
      exact firstCentralizerResidual_core_quotient_card D m hcore z hzL

open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.SolvableExclusion.Residual

/-- Every ordinary 13.3.9 clause, with the literal L₁ and barred action,
for any outside overgroup and relatively normal source subgroup. -/
theorem ordinary_outside_source_conclusion_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Conclusion1339 L
      (one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (normalizer (L : Set G)) V Y := by
  rcases ordinary_outside_residual_at h structural D m eL z hz hzL hH hYH hnY hYz hYM hp with
    hb | ⟨he,_⟩
  · exact Or.inl hb
  · have hf := ordinary_firstFlagNormalizer_residual_at h structural D m eL z hz hzL
    have he' : Y = one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) := by
      rw [hf]
      simpa only [selectedFirstResidual,if_pos (show Nonempty ((L ⧸ pCore 2 L) ≃*
        alternatingGroup (Fin 6)) from ⟨eL⟩)] using he
    refine Or.inr ⟨le_inf hYM (hYM.trans (normalizer_component_le_module_at h structural D m)),
      he' ▸ rfl,fun _ => he',?_⟩
    intro hc
    have hh := Nat.card_congr (centerCongr eL).toEquiv
    rw [hc.2.1,alternatingGroup.center_eq_bot (by simp),card_bot] at hh
    omega

/-- The literal 13.3.9 statement for an ordinary or covered augmentation
module. Its proof constructs the quotient row and the exact selected residual;
all hypotheses refer to the original G,T. -/
theorem augmentation_source1339_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    Source1339 L
      (one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (T : Subgroup G) (normalizer (L : Set G)) V
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) := by
  rcases original_quotient_rows D m h.quasisimple with he | hc
  · obtain ⟨eL⟩ := he
    intro _ H Y hH hYH hp hn hv
    obtain ⟨v,hv,hvL,hYv⟩ := hv
    exact ordinary_outside_source_conclusion_at h structural D m eL ⟨v,hv.1⟩ hv.2
      (fun hc => hvL ⟨hv.1,hc⟩) hH hYH
      ((normal_subgroupOf_iff_le_normalizer hYH).mp hn)
      (hYv.trans inf_le_right) (hYv.trans inf_le_left) hp
  · exact covered_source1339_at h structural D m hc.2.1

/-- Discharge the literal selected-residual premise used by the original
R₁ centralizer argument, in both quotient rows and at either nonfixed weight. -/
theorem augmentation_point_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3) := by
  rcases original_quotient_rows D m h.quasisimple with he | hc
  · obtain ⟨eL⟩ := he
    exact ordinary_point_residual_at h structural D m eL z hz hzL hout hYH hnY hYM hp
  · exact covered_point_residual_at h structural D m hc.2.1 z hz hzL hout hYH hnY hYM hp

open Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource

/-- Apply the full augmentation 13.3.9 theorem to the original nonzero fixed
chosen module. Applicability and its five-dimensional marking are constructed
from the retained earlier 13.3.2 source inputs. -/
theorem original_fixed_module_source1339_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L) :
    Source1339 L
      (one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (T : Subgroup G) (normalizer (L : Set G)) V
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  exact augmentation_source1339_at h structural D m

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
