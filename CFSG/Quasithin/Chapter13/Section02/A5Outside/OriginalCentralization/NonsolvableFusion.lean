module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCenters
public import Theory.GroupTheory.CentralFourSylowAction
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# The original four-group omega-center and its fusion

The original omega splitting supplies a component-fixed line whenever
J(T) moves the chosen natural module and the Sylow omega-center has order
four. A Sylow normalizer contained in N_G(L) preserves this line, so its
action on the four-group is trivial. Burnside fusion then separates all
elements of the omega-center, including the fixed summand.

This is a necessary constraint used by the original nonsolvable outside
branch. It does not assert that the outside group centralizes the center.
Source: Aschbacher--Smith 13.2.4(2b), 13.2.8(1), printed pp.879--880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterB ChapterC
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The fixed line in the original omega splitting is preserved by the
Sylow normalizer. Its action on the full four-group is therefore trivial. -/
theorem normalizer_centralizes_omega_of_four
    (d : Context T L V V₁ V₂ V₃)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hNL : normalizer ((T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hsmall : Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (L : Set G) : Subgroup G) ≤ 2)
    (hfour : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    normalizer ((T : Subgroup G) : Set G) ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let C := Z ⊓ centralizer (L : Set G)
  have hNZ : normalizer ((T : Subgroup G) : Set G) ≤ normalizer (Z : Set G) := by
    intro n hn
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (omegaOneCenterAmbient (T : Subgroup G)).map (MulAut.conj n).toMonoidHom = _
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj n).injective]
    exact congrArg omegaOneCenterAmbient (mem_normalizer_iff_map_conj_eq.mp hn)
  have hCne : C ≠ ⊥ := by
    intro hh
    have he := omega_decomposition_of_thompson_moves d hJ
    change Z = V₁ ⊔ C at he
    rw [hh,sup_bot_eq] at he
    have hc := congrArg (fun A : Subgroup G => Nat.card A) he
    change Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = Nat.card V₁ at hc
    rw [hfour,d.flag.one_card] at hc
    omega
  have hC : Nat.card C = 2 := by
    have hp := C.one_lt_card_iff_ne_bot.mpr hCne
    change Nat.card C ≤ 2 at hsmall
    omega
  have hNC : normalizer ((T : Subgroup G) : Set G) ≤ normalizer (C : Set G) :=
    (le_inf hNZ (hNL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  exact T.centralizes_four_of_preserves_line _ Z C (T : Subgroup G).le_normalizer hNZ
    (le_centralizer_iff.mp (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2))
    inf_le_left hC hfour hNC

/-- Burnside fusion now separates every two distinct elements of the full
original Sylow omega-center, including its component-fixed line. -/
theorem omega_isConj_iff_eq_of_normalizer_centralizes
    (hn : normalizer ((T : Subgroup G) : Set G) ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    {x y : G} (hx : x ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hy : y ∈ omegaOneCenterAmbient (T : Subgroup G)) : IsConj x y ↔ x = y := by
  constructor
  · intro hxy
    have hweak (g : G) (hg : (T : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ T) :
        g ∈ normalizer ((T : Subgroup G) : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      exact eq_of_le_of_card_ge hg (by rw [card_map_of_injective (MulAut.conj g).injective])
    obtain ⟨n,hnN,he⟩ := T.weakly_closed_normalizer_controls_centralizer_fusion
      (T : Subgroup G) le_rfl hweak
      ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2
      ((mem_omegaOneCenterAmbient_iff _ _).mp hy).2.2 hxy
    exact (mul_inv_eq_iff_eq_mul.mpr (hn hnN x hx).symm).symm.trans he
  · rintro rfl
    exact IsConj.refl _
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
