module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Setup
/-!
# Ambient conjugates of normal cubics in the offender subgroup

If a normal subgroup J has at most two normal cubic subgroups, every cubic
normal in J has at most two conjugates in the ambient group. Conjugation in D
restricts to an actual automorphism of J; mapping the two catalogue entries
through J's inclusion bounds the ambient orbit and hence the normalizer index.
Normality of the cubic in J and the two-entry catalogue are explicit premises.

Source: the orbit bound in Aschbacher–Smith 13.6.10, printed p.928,
using the product cases of B.5.6, printed p.105.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
open scoped Pointwise
open Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- Count conjugates in D using the normal cubic catalogue of a normal J. -/
theorem ambient_index_le_two_of_normal_cubic_cover (J A : Subgroup D) [J.Normal] (hle : A ≤ J)
    (hc : Nat.card A = 3) (hn : (A.subgroupOf J).Normal)
    (hcover : ∃ B₁ B₂ : Subgroup J, ∀ B : Subgroup J,
      B.Normal → Nat.card B = 3 → B = B₁ ∨ B = B₂) :
    (normalizer (A : Set D)).index ≤ 2 := by
  classical
  obtain ⟨B₁, B₂, hcover⟩ := hcover
  let : MulAction D (Subgroup D) := MulAction.compHom (Subgroup D) MulAut.conj
  have heq : normalizer (A : Set D) = MulAction.stabilizer D A := by
    ext g
    exact mem_normalizer_iff_map_conj_eq
  rw [heq, MulAction.index_stabilizer]
  have hconj (g : D) : A.map (MulAut.conj g).toMonoidHom = B₁.map J.subtype ∨
      A.map (MulAut.conj g).toMonoidHom = B₂.map J.subtype := by
    let e : MulAut J := MulAut.conjNormal g
    let B := (A.subgroupOf J).map e.toMonoidHom
    have hB : B.Normal := hn.map _ e.surjective
    have hcard : Nat.card B = 3 :=
      (card_map_of_injective e.injective).trans
        ((Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hc)
    have hm : B.map J.subtype = A.map (MulAut.conj g).toMonoidHom := by
      rw [show B = (A.subgroupOf J).map e.toMonoidHom from rfl, map_map,
        show J.subtype.comp e.toMonoidHom = (MulAut.conj g).toMonoidHom.comp J.subtype from rfl,
        ← map_map, map_subgroupOf_eq_of_le hle]
    rcases hcover B hB hcard with h | h
    · exact Or.inl (hm.symm.trans (congrArg (fun K => K.map J.subtype) h))
    · exact Or.inr (hm.symm.trans (congrArg (fun K => K.map J.subtype) h))
  have hs : MulAction.orbit D A ⊆ {B₁.map J.subtype, B₂.map J.subtype} := by
    rintro B ⟨g, rfl⟩
    exact hconj g
  exact (Set.ncard_le_ncard hs).trans (by
    by_cases h : B₁.map J.subtype = B₂.map J.subtype <;> simp [h])

open Representation Representation.BinaryOffender
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

/-- Apply the orbit calculation to the literal normal offender subgroup.
The premise is normality inside J, not normality in the ambient group. -/
theorem offender_index_le_two {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hn : (A.subgroupOf (offenderSubgroup ρ)).Normal)
    (hcover : ∃ B₁ B₂ : Subgroup (offenderSubgroup ρ),
      ∀ B : Subgroup (offenderSubgroup ρ),
      B.Normal → Nat.card B = 3 → B = B₁ ∨ B = B₂) :
    (normalizer (A : Set D)).index ≤ 2 :=
  ambient_index_le_two_of_normal_cubic_cover (offenderSubgroup ρ) A
    h.le_offender h.card hn hcover

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
