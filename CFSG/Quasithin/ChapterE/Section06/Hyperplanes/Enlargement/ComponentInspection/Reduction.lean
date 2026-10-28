module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Setup

/-!
# Reduction of component enlargement to intrinsic model calculations

I.3.1 supplies the containing component using the actual central Sylow action.
E.6.8 then reduces the nonalternating cases to the small characteristic-two
models and the odd-model list. The alternating-six and alternating-seven
involution calculations are kept separate. E.6.21 eliminates the perfect
central three-covers before the latter calculation is applied.

The model-specific centralizer inspections are explicit inputs to this
reduction; `ComponentInspection` supplies their proofs in its final assembly. The earlier
I.3.1 and E.6.8 source results and E.6.21 are explicit inputs. The standing
E.6.15 hypothesis is retained at this assembly boundary.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed p.254
(PDF p.265), the first paragraph of the proof of E.6.22.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open ComponentBalance Components Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}

/-- Assembly retaining the exact earlier E.6.8 output and exposing only the
remaining intrinsic, group-specific centralizer calculations. -/
theorem component_lift_of_inspections
    [IsElementaryAbelian 2 V] (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (hbalance : EarlierBalance K) (ho : OddCoreFree V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      ¬ X ≤ M ∧ ComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X)
    (hborel : ∀ (X : Subgroup G), IsQuasisimple X → ∀ n : ℕ, n ≤ 2 →
      BorelComponentModel X n → NoCentralInvolutionComponent X)
    (hsymplectic : ∀ (X : Subgroup G), IsQuasisimple X → ∀ n : ℕ, n ≤ 2 →
      SymplecticDerivedModel X n → NoCentralInvolutionComponent X)
    (hlinear : ∀ (X : Subgroup G), IsQuasisimple X →
      ClassicalGroup.IsPSL X 4 2 → NoCentralInvolutionComponent X)
    (hsix : ∀ (X : Subgroup G), IsQuasisimple X →
      IsAlternating X 6 → NoCentralInvolutionComponent X)
    (hseven : ∀ (X : Subgroup G), IsQuasisimple X →
      IsAlternating X 7 → CentralInvolutionFive X)
    (hodd : ∀ (X : Subgroup G), IsQuasisimple X →
      ((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL X 2 p) ∨
        ClassicalGroup.IsPSL X 3 3 ∨ Nonempty (X ≃* Sporadic.Mathieu.M11)) →
      NoCentralInvolutionComponent X) : ComponentLiftAlternative M V := by
  let _ := h.elementary
  let _ := h15
  intro U _ hU L hL A hA hAU hc
  obtain ⟨X, hLX, hX⟩ := exists_containing_component h hbalance ho hA hU.1 hAU hL
  let _ : IsQuasisimple X := (show IsComponentIn X (centralizer (A : Set G)) from hX).quasisimple
  refine ⟨X, hLX, hX, ?_⟩
  have equal (hi : NoCentralInvolutionComponent X) : L = X :=
    component_eq_of_inspection h hU hAU hc hA hL hLX hX hi
  rcases (h68 A hA X hX).2 with hb | hs | hl | ha | hod
  · obtain ⟨n, hn⟩ := hb
    exact Or.inl (equal (hborel X inferInstance n (hn.bound.trans hc) hn.model))
  · obtain ⟨n, hn⟩ := hs
    have hdim : actionCorank V X ≤ 2 := hn.bound.trans hc
    rcases hn.local_structure with ⟨_, hcase⟩ | ⟨_, _, hd⟩
    · rcases hcase with ⟨hd, _⟩ | ⟨hm, _⟩
      · exact Or.inl (equal (hsymplectic X inferInstance n (by omega) hn.model))
      · exact Or.inl (equal (hsix X inferInstance hm))
    · exact Or.inl (equal (hsymplectic X inferInstance n (by omega) hn.model))
  · exact Or.inl (equal (hlinear X inferInstance hl.model))
  · rcases ha.model with hmseven | hcover | hcover
    · rcases component_eq_or_five_of_inspection h hU hAU hc hA hL hLX hX
        (hseven X inferInstance hmseven) with he | hfive
      · exact Or.inl he
      · exact Or.inr ⟨hfive, Or.inl hmseven⟩
    · exact (not_three_cover ho hA.1 hA.2.1 hX 6 hcover).elim
    · exact (not_three_cover ho hA.1 hA.2.1 hX 7 hcover).elim
  · exact Or.inl (equal (hodd X inferInstance hod.model))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
