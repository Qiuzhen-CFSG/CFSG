module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Recognition

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerFusion

/-!
# Applying the terminal13.4.9 recognition to the original fixed line: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Recognition` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open SolvableCentralizerC3 Quasithin.I5
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The ambient source implication, with all distinguished-line hypotheses
proved from the original marked module. -/
theorem isPSp_of_geometry_and_fusion_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G)
    (S : DSystem .C3 (generated (normalizer (L : Set G)) z H₀))
    (hf : ∀ a ∈ generated (normalizer (L : Set G)) z H₀,
      ∀ b ∈ generated (normalizer (L : Set G)) z H₀,
      BenderSuzuki.PFAppendixIII.IsInvolution a → IsConj a b →
        ∃ c ∈ generated (normalizer (L : Set G)) z H₀, MulAut.conj c a = b)
    (hp : ∀ d ∈ V ⊓ centralizer (L : Set G), d ≠ 1 →
      ∀ e ∈ generated (normalizer (L : Set G)) z H₀,
        IsConj d e → Commute d e → e ≠ d →
          centralizer ({d * e} : Set G) ≤ generated (normalizer (L : Set G)) z H₀) :
    ClassicalGroup.IsPSp G 3 2 := by
  obtain ⟨d, hd1⟩ := ne_bot_iff_exists_ne_one.mp m.fixed_ne_bot
  have hd : (d : G) ≠ 1 := fun he => hd1 (Subtype.ext he)
  let := D.elementary
  have hd2 : (d : G) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian d.val d.property.1
  let e := ambient_equiv_sp6_of_fusion (normalizer (L : Set G)) H₀ z d.val S T
    h₀.qtke.simple h₀.qtke.nonabelian D.sylow_normalizes_component ⟨hd, hd2⟩
    (D.sylow_normalizes_component (D.le_sylow d.property.1))
    (fixed_generator_centralizer_at h structural D m d.property hd).le hf
    (hp d.val d.property hd)
  exact ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨e.trans Theory.SpecificGroups.SymplecticSix.EvenProjective.equiv⟩⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
