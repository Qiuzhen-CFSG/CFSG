module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Embedding
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ModelRestrictions.Outer
public import Theory.SpecificGroups.Suzuki.ElementarySylowSubgroups.FieldEight

/-!
# The exceptional centralizer order and pair-stabilizer bound

A solvable subgroup of the actual Sz(8) with a Sylow two-subgroup of order
two and order divisible by seven has order fourteen. Standard containment
and the concrete Borel and torus-normalizer calculations prove this intrinsic
statement.

For the source centralizer J, the given embedding J → L followed by the
model L ≃ Sz(8) preserves the Sylow subgroup and cardinality. The common
prime supplies seven, so |J| = 14. The already proved action on L then
gives |D| dividing 294 through the literal relative quotient D/(K × J).
This also discharges the order premise of the exceptional prime-power sieve.

Source: GLS4, Chapter 4, Lemma 3.8; Chapter 2, the last paragraph of
Lemma 14.9, in refs/KGroup/GLS4/Chapter4.tex and Chapter2.tex.
-/

namespace BenderSuzuki.MatrixGroups

/-- The intrinsic solvable-subgroup consequence of GLS4, Chapter 4,
Lemma 3.8 at field order eight. -/
public theorem suzuki_solvable_card_fourteen_at_eight
    (H : Subgroup (SuzukiMatrixGroup 1)) [Group.IsSolvable H]
    (V : Sylow 2 H) (hV : Nat.card V = 2) (hseven : 7 ∣ Nat.card H) :
    Nat.card H = 14 := by
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair 1 (by decide)
  exact suzuki_card_fourteen_of_standard_containment T H
    (suzukiStandardContainment_of_isSolvable (by decide) T H) V hV hseven

end BenderSuzuki.MatrixGroups

namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {z t : G}

/-- The embedded source centralizer has order fourteen when the parameter
is eight and its specified Sylow subgroup U has order two. -/
public theorem Context.centralizer_card_fourteen_at_eight
    (d : Context Z M z t 1) (g : LocalGeometry Z M z t 1) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : Nat.card g.U = 2) :
    Nat.card (centralizer (residualGenerated M z t : Set G)) = 14 := by
  let e := MonoidHom.ofInjective (f := d.model.toMonoidHom.comp f)
    (d.model.injective.comp hf)
  have hcard : Nat.card (centralizer (residualGenerated M z t : Set G)) =
      Nat.card (d.model.toMonoidHom.comp f).range := Nat.card_congr e.toEquiv
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair 1 (by decide)
  obtain ⟨V, _, hV⟩ := d.centralizer_model_elementary_sylow g f hf
  exact hcard.trans (suzuki_card_fourteen_of_standard_containment T _
    (d.centralizer_model_standard_containment g f hf T) V (hV.trans hU)
    (hcard ▸ s.seven_dvd_centralizer_card g))

/-- Apply the actual outer-action bound after discharging |J| = 14. -/
public theorem Context.pair_card_dvd_294_of_U_card_two
    (d : Context Z M z t 1) (g : LocalGeometry Z M z t 1) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : Nat.card g.U = 2) :
    Nat.card (residualPairStabilizer M t) ∣ 294 :=
  d.pair_card_dvd_294_of_centralizer_card (d.centralizer_card_fourteen_at_eight g s f hf hU)

/-- The exceptional prime-power obstruction with its model-order premise
discharged from the original embedding and Sylow hypotheses. -/
public theorem Context.no_odd_primePower_congruence_of_U_card_two
    (d : Context Z M z t 1) (g : LocalGeometry Z M z t 1) (s : SylowGeometry g)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (hU : Nat.card g.U = 2)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hdiv : p ^ a ∣ Nat.card M) : ¬ 7 ∣ p ^ a - 1 :=
  d.no_odd_primePower_congruence_at_eight (d.pair_card_dvd_294_of_U_card_two g s f hf hU)
    hp hp2 ha hdiv

end BenderSuzuki.ZD.SuzukiExclusion
