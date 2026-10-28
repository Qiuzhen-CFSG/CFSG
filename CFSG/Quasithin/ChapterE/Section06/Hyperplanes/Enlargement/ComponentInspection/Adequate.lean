module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Adequate
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection

/-!
# E.6.22 component lifting from the proved model fields

The original component-enlargement proof uses only the models, action bounds,
and Borel or parabolic data. The two unestablished kernel equalities in the
old E.6.8 output are not used. Each family is inspected on the literal fixed
subgroup by the already proved Borel, symplectic, alternating and odd model
calculations, with original balance and odd-core inputs retained.
Source: Aschbacher–Smith, E.6.22, printed p.254.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open ComponentBalance Components Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

/-- All intrinsic E.6.22 component inspections use only the proved adequate fields. -/
theorem component_lift_of_adequate_models
    [IsElementaryAbelian 2 V] (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (hbalance : EarlierBalance K) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) : ComponentLiftAlternative M V := by
  let _ := h.elementary
  let _ := h15
  intro U _ hU L hL A hA hAU hc
  obtain ⟨X, hLX, hX⟩ := exists_containing_component h hbalance ho hA hU.1 hAU hL
  let _ : IsQuasisimple X := (show IsComponentIn X (centralizer (A : Set G)) from hX).quasisimple
  refine ⟨X, hLX, hX, ?_⟩
  have equal (hi : NoCentralInvolutionComponent X) : L = X :=
    component_eq_of_inspection h hU hAU hc hA hL hLX hX hi
  rcases h68 A hA X hX with hb | hs | hl | ha | hod
  · obtain ⟨n, hn⟩ := hb
    exact Or.inl (equal (borel_noCentralInvolutionComponent X inferInstance (hn.bound.trans hc) hn.model))
  · obtain ⟨n, hn⟩ := hs
    have hdim : actionCorank V X ≤ 2 := hn.bound.trans hc
    rcases hn.local_structure with ⟨_, hcase⟩ | ⟨_, _, hd⟩
    · rcases hcase with ⟨hd, _⟩ | ⟨hm, _⟩
      · exact Or.inl (equal (symplectic_noCentralInvolutionComponent X n (by omega) hn.model))
      · exact Or.inl (equal (alternating_six_noCentralInvolutionComponent hm))
    · exact Or.inl (equal (symplectic_noCentralInvolutionComponent X n (by omega) hn.model))
  · exact Or.inl (equal (linear_four_noCentralInvolutionComponent hl.1))
  · rcases ha.model with hmseven | hcover | hcover
    · rcases component_eq_or_five_of_inspection h hU hAU hc hA hL hLX hX
        (alternating_seven_centralInvolutionFive hmseven) with he | hfive
      · exact Or.inl he
      · exact Or.inr ⟨hfive, Or.inl hmseven⟩
    · exact (not_three_cover ho hA.1 hA.2.1 hX 6 hcover).elim
    · exact (not_three_cover ho hA.1 hA.2.1 hX 7 hcover).elim
  · rcases hod.1 with hp | hthree | he
    · exact Or.inl (equal (oddLinear_noCentralInvolutionComponent X inferInstance (Or.inl hp)))
    · exact Or.inl (equal (oddLinear_noCentralInvolutionComponent X inferInstance (Or.inr hthree)))
    · exact Or.inl (equal (mathieu_eleven_noCentralInvolutionComponent he.some))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
