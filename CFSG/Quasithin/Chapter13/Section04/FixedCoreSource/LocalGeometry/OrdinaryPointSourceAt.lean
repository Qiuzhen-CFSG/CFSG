module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredSelection
public import Theory.GroupTheory.PResidual.IndexThreeNormalized
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryOutsideAt

/-!
# The ordinary point residual before the normalizer supplement

The full-normalizer 13.3.8 argument first places the actual two-perfect
normal subgroup in L. Its centralization of the original escaping point
then places it in C_L(z), whose Sylow two-subgroup has index three.
The normalized residual theorem identifies it with the literal selected
first residual and gives its intrinsic quotient order three.

This discharges the ordinary 13.3.9 clause without M=LT; all normality is
relative to C_G(z), and both nonconstant weights are retained.
Source: Aschbacher--Smith 13.3.8--9 and 13.4.4(2), pp.886--887,897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V Y : Subgroup G}

/-- The literal ordinary 13.3.9 clause at either nonfixed Sylow-central weight. -/
theorem ordinary_point_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3) := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hYL := ordinary_outside_le_component_at h structural D m eL
    (centralizer ({z.val} : Set G)) ⟨centralizer_mem_HOver hz hz1,hout⟩
    Y hYH hnY hp hYM
  let H := centralizer ({z.val} : Set G)
  let C := L ⊓ H
  have hYC : Y ≤ C := le_inf hYL hYH
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hnC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf D.sylow_normalizes_component (hTH.trans H.le_normalizer)).trans
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
    exact mem_normalizer_iff.mp (hnY (hTH (hST s hs))) y.val
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

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
