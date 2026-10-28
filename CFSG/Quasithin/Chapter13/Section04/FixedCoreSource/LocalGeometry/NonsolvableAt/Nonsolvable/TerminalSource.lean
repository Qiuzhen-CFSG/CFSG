module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.OffenderIntersection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.Rank
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.TerminalSource
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Terminal
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.CentralSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank
public import Theory.Representation.BinaryConjugationCoordinates
public import Theory.GroupAction.ElementaryEightActionRank

/-!
# Discharging the terminal natural-action and image-order premises: structure at the original group

The literal conjugation kernel identifies the actor image with A/C_A(W).
The terminal corank bound makes that image have order at least eight. For
W of order eight, GL₃(2) gives the contradictory upper bound four. For the
natural A₆ module, normalization of K extends its original quotient marking
to an S₆ action; elementary two-rank bounds then force image order eight.
The common-fixed-space contradiction applies to this constructed action.
Finally K=[K,A] and W=[W,K] supply movement, so it is not an extra premise.

The component module classification, graph construction, unique escaping
weight, and returning conjugate that generates K remain with
qt-d-1341-nonsolvable-source. The fixed-point-free premise in the final
consumer is exactly the natural-row conclusion of 13.4.17(3), still to be
proved there. Earlier structural, fusion and fixed-line kernel inputs retain
final discharge with qt-d-1341-fixed-core-source. These terminal consumers
do not assert completion of the nonsolvable branch. Universal nonsolvability
at both original weight choices remains required for the earlier uniqueness.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/TerminalSource` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
variable {G : Type*} [Group G]
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G]
open Chapter12.Section02
variable [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked terminal contradiction without an assumed image order. -/
theorem false_of_marked_natural_terminal_without_image_order_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (W : Subgroup G) (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hmove : ¬ W ≤ centralizer (V.conjBy y : Set G))
    (φ : V.conjBy y →* Equiv.Perm (Fin 6))
    (e : W ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (a : V.conjBy y) (w : W),
      (e (W.normalizerMonoidHom ⟨a.val, hAW a.property⟩ w)).toAdd =
        naturalRepresentation (Fin 6) (φ a) (e w).toAdd) : False := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy y) := IsElementaryAbelian.map _
  have hr := m.three_le_globalR_of_unique_escape_at h structural z hz1 hzT hzout hunique
  have hu := m.terminal_intersection_centralizes_at h structural hfusion hkernel W hpoints y hAW
  have hf := CoreMarking.terminal_corank_and_fixed_subgroups hr W y hu hmove
  have hcard := natural_action_card_eq_eight_of_corank (V.conjBy y) W hAW φ e he hf.1
  exact false_of_natural_image_and_fixed_subgroups (V.conjBy y) W hAW φ e he hcard
    (fun B hB hcor => (hf.2 B hB hcor).trans inf_le_right)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable


namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Subgroup Theory.GroupTheory Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem moves_of_component_generation_at (K A W : Subgroup G)
    (hKW : K ≤ normalizer (W : Set G)) (hgen : ⁅K,A⁆ = K)
    (hfull : W = ⁅W,K⁆) (hne : W ≠ ⊥) : ¬ W ≤ centralizer (A : Set G) := by
  intro hc
  have hKN : K ≤ normalizer (centralizer (W : Set G) : Set G) :=
    hKW.trans (normalizer_le_normalizer_centralizer W)
  have hKC : K ≤ centralizer (W : Set G) := by
    rw [←hgen]
    exact (commutator_mono le_rfl (le_centralizer_iff.mp hc)).trans
      (le_normalizer_iff_commutator_le_right.mp hKN)
  exact hne (hfull.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hKC)))

/-- The natural-three row contradicts the actual terminal corank bound. -/
theorem false_of_terminal_eight_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hmove : ¬ W ≤ centralizer (V.conjBy y : Set G))
    (hW : Nat.card W = 8) : False := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.conjBy y) := IsElementaryAbelian.map _
  have hr := m.three_le_globalR_of_unique_escape_at h structural z hz1 hzT hzout hunique
  have hu := m.terminal_intersection_centralizes_at h structural hfusion hkernel W hpoints y hAW
  have hf := CoreMarking.terminal_corank_and_fixed_subgroups hr W y hu hmove
  have hi := elementary_eight_centralizer_index_le_four (V.conjBy y) W hAW hW
  have hh : ChapterE.subgroupCorank (V.conjBy y)
      (V.conjBy y ⊓ centralizer (W : Set G)) ≤ 2 :=
    (Nat.log_mono_right hi).trans (by decide)
  omega

/-- The natural-six component supplies its ambient action, its image size, and its movement; no separate witnesses are assumed. -/
theorem false_of_terminal_natural_six_component_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (K W : Subgroup G) (DK : ChosenModule T K W)
    (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAK : V.conjBy y ≤ normalizer (K : Set G))
    (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hgen : ⁅K,V.conjBy y⁆ = K)
    (q : K →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (e : W ≃* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (he : ∀ (k : K) (w : W),
      (e (W.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ w)).toAdd =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (q k) (e w).toAdd) : False := by
  obtain ⟨φ,hφ⟩ := exists_natural_six_actor (V.conjBy y) K W hAK hAW DK.normalizes q hq e he
  exact false_of_marked_natural_terminal_without_image_order_at h structural D m z hz1 hzT hzout
    hunique hfusion hkernel W hpoints y hAW
    (moves_of_component_generation_at K (V.conjBy y) W DK.normalizes hgen DK.eq_commutator DK.ne_bot)
    φ e hφ
/-- The actual 13.4.10 component marking feeds the terminal proof once the
13.4.17 graph argument has excluded the fixed core row. -/
theorem false_of_terminal_component_fixed_free_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1) (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hkernel : ∀ B : Subgroup G, B ≤ normalizer (V : Set G) →
      ⁅V, B⁆ ≤ V ⊓ centralizer (L : Set G) → ⁅V, B⁆ = ⊥)
    (K W : Subgroup G) (DK : ChosenModule T K W)
    (hpoints : ∀ w ∈ W, w ≠ 1 → IsConj m.constant.val w)
    (y : G) (hAK : V.conjBy y ≤ normalizer (K : Set G))
    (hAW : V.conjBy y ≤ normalizer (W : Set G))
    (hgen : ⁅K,V.conjBy y⁆ = K)
    (marking : ComponentModuleAt DK z.val)
    (hfixed : W ⊓ centralizer (K : Set G) = ⊥) : False := by
  cases marking with
  | linearThree _ e _ =>
    let := DK.elementary
    have hc : Nat.card W = 8 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 3 → ZMod 2) = 8
      simp
    exact false_of_terminal_eight_at h structural D m z hz1 hzT hzout hunique hfusion hkernel
      W hpoints y hAW
      (moves_of_component_generation_at K (V.conjBy y) W DK.normalizes hgen DK.eq_commutator DK.ne_bot) hc
  | naturalSix q e he =>
    exact false_of_terminal_natural_six_component_at h structural D m z hz1 hzT hzout
      hunique hfusion hkernel K W DK hpoints y hAK hAW hgen
      (q.toMonoidHom.comp (QuotientGroup.mk' (Section08.TransvectionRecognition.Component.ModelExtension.centralCore K)))
      (q.surjective.comp (QuotientGroup.mk'_surjective _)) e he
  | coreSix mK _ => exact mK.fixed_ne_bot hfixed

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
