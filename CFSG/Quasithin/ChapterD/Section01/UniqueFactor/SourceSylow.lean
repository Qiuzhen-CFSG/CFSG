module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceDualOffender
public import CFSG.Quasithin.ChapterB.Section06To07.NormalActor

/-!
# The genuine solvable Sylow conclusion of D.1.4

When Q centralizes V, the common-normal hypothesis excludes R≤R₂ and
makes the actual G₂ a minimal parabolic. The B.6.8 actor theorem proves
O²(G₂)=[O²(G₂),R]. The checked three-subgroups calculation gives
[R₂,O²(G₂)]≤R, and B.6.8(2) supplies the odd residual modulo R₂.
Thus R is Sylow in O²(G₂)R. Combining this with the constructed dual
actor proves the original dual-FF-or-Sylow alternative for every solvable
G₂. No characteristic-two or extra classification premise is needed here.
The separate Thompson, reduced-FF and A₃-block clauses are not asserted.
Source: Aschbacher–Smith, D.1.4, printed p.176, and 15.4.2(4), p.1156.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem intrinsic_minimalParabolic_of_coreClosure_centralizes
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G))
    (S : Sylow 2 G₂) (hS : (S : Subgroup G₂).map G₂.subtype = T) :
    ChapterB.IsMinimalParabolicOver S ⊤ := by
  have hRnot := left_core_not_le_right_core d hne (intersection_normalized_of_centralizes d hc)
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨M,⟨hMc,hTM⟩,hu⟩ := d.unique_maximal
    have hSM : (S : Subgroup G₂) ≤ M := by
      intro s hs
      obtain ⟨m,hm,he⟩ := hTM (hS ▸ mem_map_of_mem G₂.subtype hs)
      exact G₂.subtype_injective he ▸ hm
    refine ⟨M,⟨hMc,hSM⟩,?_⟩
    intro N hN
    apply hu N
    refine ⟨hN.1,?_⟩
    rw [← hS]
    exact map_mono hN.2
  · intro hn
    have hSc : (S : Subgroup G₂) ≤ pCore 2 G₂ := le_sSup ⟨hn,S.isPGroup'⟩
    have hTc : T ≤ twoCoreIn G₂ := by rw [← hS]; exact map_mono hSc
    exact hRnot ((left_core_le_sylow d).trans hTc)

theorem source_residual_eq_commutator_of_coreClosure_centralizes
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    (pResidual 2 G₂).map G₂.subtype =
      ⁅(pResidual 2 G₂).map G₂.subtype,twoCoreIn G₁⁆ := by
  let := d.finite_right
  let R := twoCoreIn G₁
  let R0 := R.subgroupOf G₂
  have hRG₂ : R ≤ G₂ := (left_core_le_sylow d).trans (sylow_le_right d)
  obtain ⟨S,hS⟩ := d.sylow_right
  have hP := intrinsic_minimalParabolic_of_coreClosure_centralizes d hne hc S hS
  have hRS : R0 ≤ S := by
    intro r hr
    have hrt : (r : G) ∈ T := (left_core_le_sylow d) hr
    rw [← hS] at hrt
    obtain ⟨s,hs,he⟩ := hrt
    exact G₂.subtype_injective he ▸ hs
  have hSR : (S : Subgroup G₂) ≤ normalizer (R0 : Set G₂) := by
    apply le_normalizer_iff.mpr
    intro s hs r hr
    exact le_normalizer_iff.mp (twoCore_normalized G₁)
      s ((sylow_le_left d) (hS ▸ mem_map_of_mem G₂.subtype hs)) r hr
  have hRnot : ¬ R0 ≤ pCore 2 G₂ := by
    intro h
    apply left_core_not_le_right_core d hne (intersection_normalized_of_centralizes d hc)
    have hm := map_mono (f := G₂.subtype) h
    rwa [map_subgroupOf_eq_of_le hRG₂] at hm
  have he := ChapterB.minimalParabolic_residual_commutator_of_normalized_two_actor S hP R0 hRS hSR hRnot
  have hm := congrArg (map G₂.subtype) he
  simpa only [R0, R, map_commutator,map_subgroupOf_eq_of_le hRG₂] using hm

theorem source_sylow_of_coreClosure_centralizes
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G))
    (hs : Group.IsSolvable G₂) :
    let H := (pResidual 2 G₂).map G₂.subtype ⊔ twoCoreIn G₁
    ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = twoCoreIn G₁ := by
  let := d.finite_right
  obtain ⟨S,hS⟩ := d.sylow_right
  have hP := intrinsic_minimalParabolic_of_coreClosure_centralizes d hne hc S hS
  exact exists_sylow_residual_sup_of_centralizes d hc
    (source_residual_eq_commutator_of_coreClosure_centralizes d hne hc)
    (ChapterB.minimalParabolic_solvable_quotient_residual_odd S hP hs)

theorem source_dualFF_or_sylow
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) (hs : Group.IsSolvable G₂) :
    DualFF d ∨
      (let H := (pResidual 2 G₂).map G₂.subtype ⊔ twoCoreIn G₁
      ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = twoCoreIn G₁) := by
  rcases source_dualFF_or_coreClosure_centralizes d hV hu with hf | hc
  · exact Or.inl hf
  · exact Or.inr (source_sylow_of_coreClosure_centralizes d (module_ne_bot hu) hc hs)
end CFSG.Quasithin.ChapterD.UniqueFactor
