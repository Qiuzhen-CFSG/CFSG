module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.ChosenFlag
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
public import CFSG.Quasithin.Chapter4.Section02.Unitary.RudvalisEscape

/-!
# The original chosen flag excludes a marked Rudvalis pushing-up row

The original section-Sylow comparison identifies the full six-space and
preserves its flag stabilizer inside L. Uniqueness of the invariant
three-space therefore identifies the source Rudvalis three-space with the
transported original flag. Its original ambient centralizer bound now
contradicts the quaternion escape, using the actual component embedding.

The last theorem applies this argument to the literal odd-actor residual
and the C.2.8 counterexample it constructs. It retains precisely the source
Rudvalis-row geometry as an input. In particular, neither C.4.8 recognition,
the three-space inclusion in the Ru₂ subgroup, nor the fixed-intersection
bound is asserted here. The chosen/full-module identification and the
centralizer and flag compatibility are proved rather than supplied.

Source: Aschbacher–Smith, 4.2.12–13(5) and 4.4.5–6, pp.610–612,620.
-/

public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup
open ChapterJ ChapterJ.Fusion
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The remaining concrete geometry of the source Rudvalis row. The full
module, original flag, component embedding and cubic actor are all literal.
This is an input to the row exclusion, not a classification theorem. -/
structure RudvalisFlagData (L U W : Subgroup G) where
  full_card : Nat.card W ≤ 64
  actor : Subgroup G
  actor_le : actor ≤ L
  original_invariant : actor ≤ normalizer (U : Set G)
  three : Subgroup G
  unique_three : ∀ X : Subgroup G, X ≤ W → Nat.card X = 8 →
    actor ≤ normalizer (X : Set G) → X = three
  component : Subgroup G
  setup : LocalSetup component
  cubic : Sylow 3 setup.toTypeRuSetup.L₁
  three_le : three ≤ setup.toTypeRuSetup.U.map component.subtype
  fixed_intersection :
    Nat.card ((HB setup.toTypeRuSetup cubic).map component.subtype ⊓
      normalizer (L : Set G) : Subgroup G) ≤ 4

/-- The literal original chosen flag rules out the source Rudvalis row.
No chosen/full-module equality, identification with the Ru three-space,
or transported centralizer bound remains as a premise. -/
theorem rudvalis_false_of_chosen_flag {T : Sylow 2 G} {L V U W : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (hV : Nat.card V = 64)
    (hUV : U ≤ V) (hU : Nat.card U = 8)
    (hC : centralizer (U : Set G) ≤ normalizer (L : Set G))
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W)
    (d : RudvalisFlagData L U W) : False := by
  obtain ⟨he,hUle,hcard,hstab,hcentral⟩ :=
    chosen_flag_of_section_conjugation D hV hUV hC c hVW d.full_card
  have hsame : U.map (MulAut.conj (c : G)).toMonoidHom = d.three := by
    apply d.unique_three _ hUle (hcard.trans hU)
    have ha : d.actor ≤ L ⊓ normalizer (U : Set G) :=
      le_inf d.actor_le d.original_invariant
    rw [← hstab] at ha
    exact ha.trans inf_le_right
  have hCthree : centralizer (d.three : Set G) ≤ normalizer (L : Set G) :=
    hsame ▸ hcentral
  exact not_unitary_counterexample d.setup d.cubic d.component.subtype
    d.component.subtype_injective d.three (normalizer (L : Set G))
    d.three_le d.fixed_intersection hCthree

/-- Actual odd-actor consumer: after the earlier source identifies every
selected C.2.8 pair with its marked Rudvalis row, the original residual is
a uniqueness subgroup. The row-recognition premise is kept explicit. -/
theorem chosen_oddActorResidual_unique_of_rudvalis_flag_source
    {κ : GroupClass} {T : Sylow 2 G} {L V U : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hV : Nat.card V = 64)
    (hUV : U ≤ V) (hU : Nat.card U = 8)
    (hC : centralizer (U : Set G) ≤ normalizer (L : Set G))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hrows : ∀ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L)),
      PushLE L (Section04.oddActorResidual L A) J → IsMaximalTwoLocal H → J ≤ H →
      H ⊓ normalizer (L : Set G) < H →
      ChapterC.HypothesisC28 κ H (H ⊓ normalizer (L : Set G))
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) (J.pCoreIn 2)
        (fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)) →
      Nonempty (RudvalisFlagData L U
        (fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)))) :
    UniqueMaximalOvergroup (Section04.oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hn
  obtain ⟨J,H,S,hpush,hH,hJH,hstrict,hC28,c,_,hVW⟩ :=
    chosen_oddActorResidual_C28 h D A hAN hcomm hodd hAV hM hn
  obtain ⟨d⟩ := hrows J H S hpush hH hJH hstrict hC28
  exact rudvalis_false_of_chosen_flag D hV hUV hU hC c hVW d

end CFSG.Quasithin.Chapter4.Section02.Unitary
