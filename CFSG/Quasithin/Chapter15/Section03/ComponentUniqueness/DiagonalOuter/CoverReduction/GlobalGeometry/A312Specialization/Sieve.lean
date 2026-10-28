module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization.Extensions
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization.SmallModels

/-!
# The twenty-two-case reduction for the PSL₃(4) cover

This conditional sieve eliminates every A.3.12 alternative except equality
and the actual M₂₃ model. Normal p-kernels are excluded by the small center;
small simple and central-three-cover models are excluded by order. The last
two alternatives contradict centrality of the odd core in the containing
quasisimple group of even order.

The rank-one model separations and the distinction between PSL₃(4) and
PSL₄(2) remain explicit hypotheses. They are mathematical prerequisites to
be discharged in A312Specialization, not assumptions of the source theorem.
In particular the equal order 20160 is not used to distinguish the latter
pair. The final adapter retains the actual ambient two-core quotient map.

Source: Aschbacher--Smith, A.3.12, printed pp.47--48, and 15.3.38, p.1136.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Resolve the literal list once its remaining model separations are supplied. -/
theorem resolve_of_separations (B K : Subgroup H) [IsQuasisimple B] [IsQuasisimple K]
    (hBK : B ≤ K) (c : ProjectiveMarking B 4) (hZ : Nat.card (center B) ≤ 4)
    (hlinear : ∀ n : ℕ, 2 ≤ n → ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2 ^ n))
    (hbinary : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hodd : ∀ p : ℕ, p.Prime → Odd p → 3 < p →
      ¬ (ClassicalGroup.IsPSL B 2 p ∨ IsSL B 2 p))
    (hemb : A312Embedding B K) :
    B = K ∨ Nonempty (K ≃* Sporadic.Mathieu.M23) := by
  have hc := marked_card_dvd B c
  have hq : 20160 ∣ Nat.card (B ⧸ pCore 2 B) := by rw [marked_quotient_card B c]
  have hK2 : 2 ∣ Nat.card K :=
    (dvd_trans (by norm_num : 2 ∣ 20160) hc).trans (card_dvd_of_le hBK)
  cases hemb with
  | one he => exact Or.inl he
  | two n hn small _ _ => exact (hlinear n hn small).elim
  | three m hm small _ _ => exact (no_suzuki hq hm small).elim
  | four small _ _ => exact (no_psl_three_two hq small).elim
  | five small _ _ => exact (hbinary small).elim
  | six small _ =>
    rcases small with ha | hl
    · exact (no_alternating_small hc (Or.inl rfl) ha).elim
    · exact (no_psl_three_two hc hl).elim
  | seven models =>
    rcases models with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact (no_alternating_small hc (Or.inr rfl) ha).elim
    · exact (no_alternating_threeCover hc ha).elim
  | eight models =>
    rcases models with ⟨p, hp, ho, hlarge, small, _⟩ | ⟨_, _, small, _⟩
    · exact (hodd p hp ho hlarge (Or.inl small)).elim
    · exact (no_alternating_small hc (Or.inl rfl) small).elim
  | nine models =>
    rcases models with ⟨p, _, hp, ho, hlarge, small, _⟩ | ⟨small, _⟩ | ⟨small, _⟩
    · exact (hodd p hp ho hlarge (Or.inr small)).elim
    · exact (no_alternating_small hc (Or.inr rfl) small).elim
    · exact (no_alternating_threeCover hc small).elim
  | ten p hp _ hlarge small _ =>
    let : Fact p.Prime := ⟨hp⟩
    exact (no_elementary_extension hZ (p := p) (r := 2) (by nlinarith) _ small).elim
  | eleven small _ => exact (no_alternating_small hc (Or.inr rfl) small).elim
  | twelve models =>
    rcases models with ⟨small, _⟩ | ⟨small, _⟩
    · exact (no_elementary_extension hZ (p := 2) (r := 4) (by norm_num) _ small).elim
    · exact (no_elementary_extension hZ (p := 2) (r := 4) (by norm_num) _ small).elim
  | thirteen large _ => exact Or.inr large
  | fourteen _ small =>
    rcases small with small | small | small
    · exact (no_elementary_extension hZ (p := 2) (r := 4) (by norm_num) _ small).elim
    · exact (no_elementary_extension hZ (p := 2) (r := 6) (by norm_num) _ small).elim
    · exact (no_extraspecial_extension hZ (p := 2) (n := 3) (by norm_num) _ small).elim
  | fifteen small _ => exact (no_alternating_small hc (Or.inl rfl) small).elim
  | sixteen small _ =>
    exact (no_extraspecial_extension hZ (p := 2) (n := 2) (by norm_num) _ small).elim
  | seventeen _ small =>
    rcases small with small | small | small | small | small | small
    · exact (no_extraspecial_extension hZ (p := 2) (n := 6) (by norm_num) _ small).elim
    · exact (no_elementary_extension hZ (p := 2) (r := 11) (by norm_num) _ small).elim
    · exact (no_alternating_small hq (Or.inl rfl) small).elim
    · exact (no_alternating_threeCover hq small).elim
    · exact (hbinary small).elim
    · exact (no_psl_three_two hq small).elim
  | eighteen _ small =>
    rcases small with small | small
    · exact (no_cyclicFour_extension hZ _ small).elim
    · exact (no_homocyclicFour_extension hZ _ small).elim
  | nineteen _ small =>
    rcases small with small | small
    · exact (no_extraspecial_extension hZ (p := 2) (n := 3) (by norm_num) _ small).elim
    · exact (no_elementary_extension hZ (p := 2) (r := 6) (by norm_num) _ small).elim
  | twenty _ small _ =>
    rcases small with small | small
    · exact (no_alternating_small hq (Or.inl rfl) small).elim
    · exact (no_psl_three_two hq small).elim
  | twenty_one _ _ _ hn _ _ => exact (hn (oddCore_central hK2)).elim
  | twenty_two _ _ hn _ _ => exact (hn (oddCore_central hK2)).elim

/-- Feed model-level separation facts into the actual ambient quotient.
Neither normality of B nor equality of its restriction kernel with its
intrinsic two-core is required. -/
theorem specialize_of_model_separations
    (hbinary : ∀ (X : Type u) [Group X], ClassicalGroup.IsPSL X 3 4 →
      ¬ ClassicalGroup.IsPSL X 4 2)
    (hrankOne : ∀ (X : Type u) [Group X] [Finite X],
      20160 ∣ Nat.card X → Nat.card X ≤ 80640 →
      (∀ n : ℕ, 2 ≤ n → ¬ ClassicalGroup.IsPSL X 2 (2 ^ n)) ∧
      (∀ p : ℕ, p.Prime → Odd p → 3 < p →
        ¬ (ClassicalGroup.IsPSL X 2 p ∨ IsSL X 2 p)))
    (B K : Subgroup H) [IsQuasisimple B] [IsQuasisimple K]
    (hBK : B ≤ K) (c : ProjectiveMarking B 4)
    (hZ : center B = pCore 2 B) (hc : Nat.card (center B) = 4)
    (hemb : A312Embedding (image B) (image K)) :
    image B = image K ∨ Nonempty (image K ≃* Sporadic.Mathieu.M23) := by
  let := image_quasisimple B
  let := image_quasisimple K
  let c' := imageMarking B c
  have hZ' := image_center_eq_twoCore B hZ
  have hc' : Nat.card (center (image B)) ≤ 4 := (image_center_card_le B).trans_eq hc
  have hsmall : ClassicalGroup.IsPSL (image B ⧸ pCore 2 (image B)) 3 4 :=
    ⟨c'.F, inferInstance, inferInstance, c'.card, ⟨c'.equivalence⟩⟩
  have hq : Nat.card (image B ⧸ pCore 2 (image B)) = 20160 :=
    marked_quotient_card _ c'
  have hline := (hrankOne (image B ⧸ pCore 2 (image B))
    (by rw [hq]) (by rw [hq]; norm_num)).1
  have hodd := (hrankOne (image B) (marked_card_dvd _ c')
    (marked_card_le _ c' hZ' hc')).2
  exact resolve_of_separations (image B) (image K) (map_mono hBK) c' hc'
    hline (hbinary _ hsmall) hodd hemb

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
