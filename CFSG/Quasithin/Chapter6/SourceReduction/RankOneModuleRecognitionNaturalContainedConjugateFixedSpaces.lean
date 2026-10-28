module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpacesLines
public import Theory.Representation.SL2NaturalFixedSpaces
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The local fixed-space classification in 6.1.13

If the local centralizers differ, choose an element of C_M(U) moving B.
The TI property puts this element in N_G(B), and relative normality puts
it in N_G(L). Transfer its two compatible actions through the actual
natural-module marking. A corank-n subgroup has order 2^n, so the proved
semilinear classification gives a field line or an outer involution with
exactly U as its fixed subgroup. The line transporter and quotient-action
alignment give precisely the two exceptional source alternatives.

The independent E.6.1 hypothesis is retained. No weak-closure, rank-bound,
or downstream recognition conclusion is used. The first alternative's
E.6.12 globalization remains in the existing centralizer module.
Source: Aschbacher--Smith 6.1.13, printed p.670 (PDF p.687).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

omit [Finite G] in
/-- The published field witness forces the even degree stated in 6.1.13(3). -/
theorem IsInvolutoryFieldFixedSpace.even {B U : Subgroup G}
    (h : IsInvolutoryFieldFixedSpace L M B U n) : Even n := by
  obtain ⟨_, _, _, _, F, _, _, _, hF, _, σ, hσne, hσsq, _⟩ := h
  have hs : Function.Involutive σ := by
    intro x
    exact congrArg (fun τ : F ≃+* F => τ x) hσsq
  have hc := FiniteField.card_involution_fixed_sq σ hs hσne
  let K := FixedBy.subfield F σ
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨m, _, hm⟩ := FiniteField.card K 2
  change Nat.card K ^ 2 = Nat.card F at hc
  rw [Nat.card_eq_fintype_card, hm, ← pow_mul, hF] at hc
  have hn := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  exact ⟨m, by omega⟩

/-- The local assertion in the proof of 6.1.13, with the natural-module
and TI hypotheses made explicit and all semilinear cases discharged. -/
theorem fixedSpaceAlternatives_of_natural
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V)) :
    FixedSpaceAlternatives L M (layer L V) (ZS (T : Subgroup G) L V) n := by
  intro U hUB hUne hcor
  by_cases hC : M ⊓ centralizer (U : Set G) = M ⊓ centralizer (layer L V : Set G)
  · exact Or.inl hC
  have hnot : ¬ M ⊓ centralizer (U : Set G) ≤ M ⊓ centralizer (layer L V : Set G) := by
    intro hc
    exact hC (le_antisymm hc (inf_le_inf_left M (centralizer_le hUB)))
  obtain ⟨t, ht, htB⟩ := SetLike.not_le_iff_exists.mp hnot
  have htN : t ∈ normalizer (layer L V : Set G) := hE.localCentralizer_le_normalizer hUne hUB ht
  have htL : t ∈ normalizer (L : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal) ht.1
  have htmove : t ∉ centralizer (layer L V : Set G) := fun hh => htB ⟨ht.1, hh⟩
  let := h.layer_elementary
  have hUcard := corank_half_card hUB hnatural.card hcor
  have hZcard := (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let E := vectorActor f ⟨t, htN⟩
  let a := quotientActor e ⟨t, htL⟩
  let A := coordinateSpace f U
  have hEne : E ≠ 1 := by
    intro hid
    apply htmove
    apply mem_centralizer_iff.mpr
    intro v hv
    have hfix : E (Multiplicative.toAdd (f ⟨v, hv⟩)) = Multiplicative.toAdd (f ⟨v, hv⟩) := by
      rw [hid]
      rfl
    have hvC := (vectorActor_fixed_iff f ⟨t, htN⟩ _).mp hfix
    have hh : v ∈ centralizer ({t} : Set G) := by simpa using hvC
    exact mem_centralizer_singleton_iff.mp hh
  have hAcard : Nat.card A = Nat.card F :=
    (coordinateSpace_card f hUB).trans (hUcard.trans hF.symm)
  have hfix : ∀ v ∈ A, E v = v := by
    intro v hv
    apply (vectorActor_fixed_iff f ⟨t, htN⟩ v).mpr
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp ht.2 _ hv)
  obtain hline | ⟨hAfixed, hasq, haouter⟩ :=
    Representation.SL2NaturalFixedSpaces.halfSpace_alternatives a E
      (vectorActor_intertwines e f hf ⟨t, htL⟩ htN) hEne A hAcard hfix
  · obtain ⟨X, hX, hXA⟩ := hline
    exact Or.inr (Or.inl (fieldLine_transport (T : Subgroup G) e f hf
      (hZcard.trans hF.symm) hUB X hX hXA))
  · refine Or.inr (Or.inr (field_fixedSpace_of_outer_quotient e hF ⟨t, htL⟩ ht.1 htN ?_ hasq haouter))
    ext v
    constructor
    · intro hv
      refine ⟨hUB hv, mem_centralizer_singleton_iff.mpr ?_⟩
      exact mem_centralizer_iff.mp ht.2 v hv
    · intro hv
      let w := Multiplicative.toAdd (f ⟨v, hv.1⟩)
      have hw : E w = w := by
        apply (vectorActor_fixed_iff f ⟨t, htN⟩ w).mpr
        simpa [w] using hv.2
      have hh := (hAfixed w).mpr hw
      simpa [A, w] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
